;;; This is part of mc3, a model checking solver.
;;;
;;; Copyright (c) 2021, National Technology & Engineering Solutions of Sandia,
;;; LLC (NTESS).  Under the terms of Contract DE-NA0003525 with NTESS, the
;;; U.S. Government retains certain rights in this software.
;;;
;;; mc3 is free software: you can redistribute it and/or modify it under the
;;; terms of the GNU Lesser General Public License as published by the Free
;;; Software Foundation, either version 3 of the License, or (at your option)
;;; any later version.
;;;
;;; mc3 is distributed in the hope that it will be useful, but WITHOUT ANY
;;; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
;;; FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public License for
;;; more details.
;;;
;;; You should have received a copy of the GNU Lesser General Public License
;;; along with mc3.  If not, see <https://www.gnu.org/licenses/>.


#lang racket/base
(require math/array
         racket/contract
         racket/function
         racket/hash
         racket/list
         racket/match
         racket/math
         racket/set
         racket/string
         racket/system)


(require (file "bounding.rkt"))
(require (file "foundation.rkt"))
(require (file "mmc.rkt"))
(require (file "options.rkt"))
(require (file "util.rkt"))


(provide transition-relation-proven-forward-total?
         transition-relation-proven-backward-total?
         write-bounds-dag
         write-csv
         solve)


(define/contract transition-relation-proven-forward-total?
  (parameter/c boolean?)
  (make-parameter #f))


(define/contract transition-relation-proven-backward-total?
  (parameter/c boolean?)
  (make-parameter #f))


(define/contract subformula:number
  (parameter/c (hash/c formula/c natural?))
  (make-parameter (hash)))
(define (number-subformulas f)
  (define merge (curry hash-union #:combine min))
  (define (aux/number-subformulas f idx)
    (match f
      ((? proposition?)
       (hash f idx))
      ((list 'not g)
       (merge (hash f idx)
              (aux/number-subformulas g (add1 idx))))
      ((list 'or g* ...)
       (apply merge
              (cons (hash f idx)
                    (let ((idx~ (add1 idx)))
                      (for/list ((g g*))
                        (let ((here (aux/number-subformulas g idx~)))
                          (set! idx~ (add1 (apply max (hash-values here))))
                          here))))))
      ((list 'diamond _ g)
       (merge (hash f idx)
              (aux/number-subformulas g (add1 idx))))
      ((list 'mu z g)
       (merge (hash f idx)
              (hash z (add1 idx))
              (aux/number-subformulas g (+ 2 idx))))
      ((? variable?)
       (hash f idx))))
  (aux/number-subformulas f 0))
(define (formula-label f (insist? #f))
  (cond
    ((and (not insist?) (variable? f))
     f)
    (else
     (format "#~a" (hash-ref (subformula:number) f)))))
(define (formula-abbreviation f)
  (match f
    ((? proposition?)
     f)
    ((list 'not g)
     (list 'not (formula-label g)))
    ((list 'or g* ...)
     `(or ,@(map formula-label g*)))
    ((list 'diamond alpha g)
     (list 'diamond alpha (formula-label g)))
    ((list 'mu z g)
     (list 'mu z (formula-label g)))
    (_ (formula-label f))))
(define (literals-abbreviation lits vars)
  (define var:val
    (for/hash ((lit lits))
      (match lit
        ((smt.expression (== smt.!)
                         (and (? smt.constant?) var))
         (values var #f))
        ((and (? smt.constant?) var)
         (values var #t)))))
  (let ((retval (make-vector (length vars) ".")))
    (for ((var vars)
          (idx (in-naturals))
          #:when (hash-has-key? var:val var))
      (vector-set! retval
                   idx
                   (match (hash-ref var:val var) (#f "0") (#t "1"))))
    (format "~s" (string-join (vector->list retval) ""))))


(define/contract (solve Sigma S0 P)
  (-> sys.lts? proposition? any/c boolean?)
  (reset-bounds)
  (relative-polarities (hash))
  (bindings (hash))
  (info "solve...~n Sigma: ~a~n S0: ~a~n P: ~a" Sigma S0 P)
  (when (and (backward?)
             (match P ((list 'AG (? smt.boolean?)) #t) (_ #f)))
    (info "applying backward analysis to the invariance property")
    (set! Sigma (sys.reverse-lts Sigma))
    (let ((fwd (transition-relation-proven-forward-total?))
          (bwd (transition-relation-proven-backward-total?)))
      (transition-relation-proven-forward-total? bwd)
      (transition-relation-proven-backward-total? fwd))
    (let ((S0-old S0))
      (set! S0 (smt.! (second P)))
      (set! P (list 'AG (smt.! S0-old)))))
  (let ((prprty~ (expand-formula P)))
    (when (malformed-formula? prprty~ Sigma)
      (raise-argument-error
       'solve
       (format
        "a well-formed formula w.r.t. state variables ~a and input variables ~a"
        (sys.lts-state-variables Sigma)
        (sys.lts-input-variables Sigma))
       P))
    (when (not (equal? P prprty~))
      (set! P prprty~)
      (info "expanded property: ~a" P)))
  (info "pretty-printed property: ~a" (formula->string P))
  ;; Cache some henceforth-immutable state.
  (subformula:number (number-subformulas P))
  (bindings (fixed-point-bindings P))
  (info "bindings: ~a" (bindings))
  (relative-polarities (bindings->relative-polarities (bindings)))
  (info "relative polarities: ~a" (relative-polarities))
  (match-define (sys.lts state-vars input-vars S I SI IS+ _) Sigma)
  (define state-vars+ (map sys.next state-vars))
  (when (and (not (and (transition-relation-proven-forward-total?)
                       (transition-relation-proven-backward-total?)))
             (check-totality?))
    (transition-relation-proven-forward-total?
     (sys.total-transition-relation? 'forward Sigma))
    (transition-relation-proven-backward-total?
     (sys.total-transition-relation? 'backward Sigma)))
  (info "transition relation is ~a"
        (if (transition-relation-proven-forward-total?)
            "FORWARD TOTAL"
            "NOT proven to be forward total"))
  (info "transition relation is ~a"
        (if (transition-relation-proven-backward-total?)
            "BACKWARD TOTAL"
            "NOT proven to be backward total"))
  ;; Helpers.
  (define/contract (expand-unsat conjunction query)
    (-> proposition? smt.solution? proposition?)
    ;; Expand `conjunction` (which should be a conjunction of literals) by
    ;; removing literals from it that do not appear in the UNSAT core contained
    ;; in `query` (which should be `smt.unsat?`, and should have resulted from a
    ;; `smt.solver-debug` check in which each of the conjuncts was asserted).
    (define conjuncts (smt.expression->conjuncts conjunction))
    (define conjuncts~
      (filter (curry set-member? (list->set (or (smt.core query) empty)))
              conjuncts))
    (let ((n (length conjuncts))
          (n~ (length conjuncts~)))
      (debug "dropped ~a/~a conjuncts via unsat core" (- n n~) n))
    (apply smt.&& conjuncts~))
  (define/contract (expand-model s constraints resolver)
    (-> proposition? (listof proposition?) smt.solver? proposition?)
    (smt.solver-push resolver)
    (smt.solver-assert resolver
                       (list (smt.! (apply smt.&& (cons S constraints)))))
    (smt.solver-assert resolver (smt.expression->conjuncts s))
    (let ((s~ (expand-unsat s (smt.solver-debug resolver))))
      (smt.solver-pop resolver)
      s~))
  (define/contract (expand-transition p/s s i t+)
    (-> (or/c 'predecessor 'successor) proposition? proposition? proposition?
        proposition?)
    ;; Given a transition from `s` with input `i` to `t+`, expand one side.
    ;;
    ;; If `p/s` is `'predecessor`, then `s` should be a single state, and `s`
    ;; will be expanded (by dropping literals) to a set `s~` of states from each
    ;; of which there is an `i` transition to a `t+` state.  If `p/s` is
    ;; `'successor`, then `s` and `t+` swap roles.
    (define-values (here these-vars there those-vars total?)
      (match p/s
        ('predecessor
         (values s state-vars
                 t+ state-vars+
                 (transition-relation-proven-forward-total?)))
        ('successor
         (values t+ state-vars+
                 s state-vars
                 (transition-relation-proven-backward-total?)))))
    (expect (listset=? (smt.symbolics here) these-vars))
    (expect (listset=? (smt.symbolics i) input-vars))
    (debug "~a to be expanded: ~a"
           p/s
           (literals-abbreviation (smt.expression->conjuncts here) these-vars))
    (cond
      ((not total?)
       (debug "transition relation not proven total; skipping ~a expansion" p/s)
       here)
      (else
       (define exists-bad-query
         (let ()
           (smt.solver-push resolver-diamond)
           (smt.solver-assert resolver-diamond
                              (list i DELTA here (smt.! there)))
           (let ((query (smt.solver-check resolver-diamond)))
             (smt.solver-pop resolver-diamond)
             query)))
       (cond
         ((smt.unsat? exists-bad-query)
          (debug
           "input for ~a expansion: ~a"
           p/s
           (literals-abbreviation (smt.expression->conjuncts i) input-vars))
          (smt.solver-push resolver-diamond)
          (smt.solver-assert
           resolver-diamond
           (append
            (smt.expression->conjuncts here)
            (list
             i
             (smt.||
              ;; Avoid including any state that does not satisfy the static
              ;; constraints.
              (smt.!
               (match p/s
                 ('predecessor S)
                 ('successor (sys.next S))))
              ;; Avoid including any state that has no transitions at all for
              ;; input `i`:
              (match p/s
                ('predecessor (smt.&& S (smt.! SI)))
                ('successor (smt.&& (sys.next S) (smt.! IS+))))
              (smt.&& DELTA (smt.! there))))))
          (let ((here~ (expand-unsat here (smt.solver-debug resolver-diamond))))
            (smt.solver-pop resolver-diamond)
            (when (not (eq? here~ here))
              (debug "expanded ~a: ~a"
                     p/s
                     (literals-abbreviation
                      (smt.expression->conjuncts here~) these-vars)))
            here~))
         (else
          (todo "try harder to do ~a expansion" p/s)
          here)))))
  (define/contract (query-constraints l/u p ctx)
    (-> (or/c 'lower 'upper) formula/c unrolling-context/c
        (listof proposition?))
    (match p
      ((list 'diamond alpha q)
       ;; [NOTE: `DELTA` is an activation literal; it will only work if the
       ;; correct activation assertion is active in the SMT solver!]
       (match l/u
         ('lower (list (sys.next (lower-bound q ctx))))
         ('upper (list alpha DELTA (sys.next (upper-bound q ctx))))))
      ((? variable? z)
       (define tau (third (hash-ref (bindings) z)))
       (define ctx- (hash-update ctx z sub1))
       (match l/u
         ('lower (list (lower-bound tau ctx-)))
         ('upper (list (upper-bound tau ctx-)))))))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define resolver-empty ; [TODO: shutdown]
    (smt.z3-names #:options (hash ':smt.core.minimize 'true
                                  ':random-seed (smtlib-random-seed)
                                  ':sat.random-seed (smtlib-random-seed)
                                  ':smt.random-seed (smtlib-random-seed))))
  (begin
    (define resolver-diamond ; [TODO: shutdown]
      (smt.z3-names #:options (hash ':smt.core.minimize 'true
                                    ':random-seed (smtlib-random-seed)
                                    ':sat.random-seed (smtlib-random-seed)
                                    ':smt.random-seed (smtlib-random-seed))))
    (smt.define-constant DELTA smt.boolean?)
    (expect (not (set-member? (append state-vars input-vars state-vars+)
                              DELTA)))
    (smt.solver-assert resolver-diamond
                       (list
                        (smt.<=> DELTA
                                 (sys.lts-transition-relation Sigma)))))
  (define one/some/each? (or/c 'one 'some 'each))
  (define/contract (log-decide-call quantifier formula context term)
    (-> one/some/each? formula/c unrolling-context/c proposition? void?)
    (algo "decide/~a...~n formula (~a): ~a~n context: ~a~n term: ~a"
          quantifier
          (formula-label formula #t)
          (formula-abbreviation formula)
          context
          (literals-abbreviation (smt.expression->conjuncts term) state-vars))
    (decide-calls (cons (list term formula context) (decide-calls))))
  (define/contract (already-decided quantifier decision)
    (-> one/some/each? boolean?
        ;; [TODO: returned value is the same as the `boolean?` argument]
        boolean?)
    (algo "already decided (~a, ~a)"
          quantifier
          (match decision (#f "negatively") (#t "positively")))
    decision)
  (define/contract (decide s p ctx)
    (-> proposition? closed-formula/c unrolling-context/c boolean?)
    (log-decide-call 'one p ctx s)
    (let ((keys (list->set (hash-keys ctx)))
          (vars (free-variables p)))
      (expect (subset? vars keys))
      (unless (set=? keys vars)
        (warning "superfluous context: ~a" (set-subtract keys vars))))
    (expect ; [TODO: make this check that `s` is a /single/ state more robust]
     (listset=? (smt.symbolics s) state-vars))
    (smt.solver-push resolver-empty)
    (smt.solver-assert resolver-empty (list s))
    (cond
      ((begin
         (smt.solver-push resolver-empty)
         (smt.solver-assert resolver-empty (list (smt.! (upper-bound p ctx))))
         (let ((query (smt.solver-check resolver-empty)))
           (smt.solver-pop resolver-empty)
           (smt.sat? query)))
       (already-decided 'one #f)
       (smt.solver-pop resolver-empty)
       #f)
      ((begin
         (smt.solver-push resolver-empty)
         (smt.solver-assert resolver-empty (list (smt.! (lower-bound p ctx))))
         (let ((query (smt.solver-check resolver-empty)))
           (smt.solver-pop resolver-empty)
           (smt.unsat? query)))
       (already-decided 'one #t)
       (smt.solver-pop resolver-empty)
       #t)
      (else
       (smt.solver-pop resolver-empty)
       (match p
         ((list 'not q)
          (algo "derive 'not")
          (not (decide s q ctx)))
         ((list 'or q* ...)
          (ormap (lambda (q)
                   (algo "derive 'or")
                   (decide s q (hash-restrict ctx (free-variables q))))
                 q*))
         ((list 'diamond _ q)
          (smt.solver-push resolver-diamond)
          (smt.solver-assert resolver-diamond (query-constraints 'upper p ctx))
          (smt.solver-assert resolver-diamond (smt.expression->conjuncts s))
          (define upper-bound-query (smt.solver-debug resolver-diamond))
          (cond
            ((smt.unsat? upper-bound-query)
             (define s~ (expand-unsat s upper-bound-query))
             (algo "expanded (diamond/one, excluded): ~a"
                   (literals-abbreviation
                    (smt.expression->conjuncts s~)
                    state-vars))
             (add-to-upper-bound! p ctx (smt.nnf (smt.! s~)))
             (smt.solver-pop resolver-diamond)
             #f)
            (else
             (expect (smt.sat? upper-bound-query))
             (smt.solver-assert resolver-diamond
                                (query-constraints 'lower p ctx))
             (define lower-bound-query (smt.solver-check resolver-diamond))
             (smt.solver-pop resolver-diamond)
             (cond
               ((smt.sat? lower-bound-query)
                (let* ((i (smt.solution->expression lower-bound-query
                                                    #:limit-to input-vars))
                       (s~ (expand-transition
                            'predecessor s i
                            (sys.next (lower-bound q ctx)))))
                  (algo "expanded (diamond/one, included): ~a"
                        (literals-abbreviation
                         (smt.expression->conjuncts s~)
                         state-vars))
                  (add-to-lower-bound! p ctx s~))
                #t)
               (else
                (algo "check successor")
                (define t+ (smt.solution->expression
                            upper-bound-query
                            #:limit-to state-vars+))
                (cond
                  ((and (not (single-states?))
                        (expand-successors?)
                        (transition-relation-proven-backward-total?))
                   (algo "expanding undecided successor (diamond)")
                   (let* ((i (smt.solution->expression
                              upper-bound-query
                              #:limit-to input-vars))
                          (t+~ (expand-transition 'successor s i t+)))
                     (cond
                       ((eq? t+~ t+)
                        (debug "expansion failed; stick with `decide`")
                        (decide (sys.prev t+~) q ctx))
                       (else
                        (debug "expansion succeeded; switch to `decide-some`")
                        (decide-some (sys.prev t+~) q ctx)))))
                  (else
                   (decide (sys.prev t+) q ctx)))
                (algo "proceed (after checking successor)")
                (decide s p ctx))))))
         ((list 'mu z tau)
          (define ctx/ (hash-remove ctx z))
          (define depth (unrolled-depth p ctx/))
          (define ctx/~ (hash-set ctx/ z depth))
          (expect (set=? (hash-keys ctx/~)
                         (set->list (free-variables tau))))
          (cond
            ((begin
               (algo "check finite approximation")
               (decide s z ctx/~))
             ;; There's no reason to repeat the `decide` call here because of
             ;; the way bounds on fixed points are deferred [right?].
             (algo "approximation is sufficient")
             #t)
            (else
             (algo "consolidate")
             (consolidate-constraints z ctx/ S)
             (cond
               ((smt.unsat? (smt.check* s (upper-bound p ctx/)))
                (algo "unrolling is unnecessary")
                #f)
               (else
                (algo "unroll")
                (unroll p ctx/)
                (algo "proceed (after unrolling)")
                (decide s p ctx/))))))
         ((? variable?)
          (expect ; the necessary context, and nothing more
           (set=? (set-subtract (list->set (hash-keys ctx))
                                (ancestors p))
                  (set p)))
          (smt.solver-push resolver-empty)
          (smt.solver-assert resolver-empty (query-constraints 'upper p ctx))
          (smt.solver-assert resolver-empty (smt.expression->conjuncts s))
          (define upper-bound-query (smt.solver-debug resolver-empty))
          (cond
            ((smt.unsat? upper-bound-query)
             (define s~ (expand-unsat s upper-bound-query))
             (algo "expanded (unrolled/one, excluded): ~a"
                   (literals-abbreviation
                    (smt.expression->conjuncts s~)
                    state-vars))
             (add-to-upper-bound! p ctx (smt.nnf (smt.! s~)))
             (smt.solver-pop resolver-empty)
             #f)
            (else
             (expect (smt.sat? upper-bound-query))
             (define lbq-constraints (query-constraints 'lower p ctx))
             (smt.solver-assert resolver-empty lbq-constraints)
             (define lower-bound-query (smt.solver-check resolver-empty))
             (smt.solver-pop resolver-empty)
             (cond
               ((smt.sat? lower-bound-query)
                (let ((s~ (expand-model s lbq-constraints resolver-empty)))
                  (algo "expanded (unrolled/one, included): ~a"
                        (literals-abbreviation
                         (smt.expression->conjuncts s~)
                         state-vars))
                  (add-to-lower-bound! p ctx s~))
                #t)
               (else
                (algo "check body")
                (define tau (third (hash-ref (bindings) p)))
                (define ctx- (hash-update ctx p sub1))
                (decide s tau ctx-)
                (algo "proceed (after checking body)")
                (decide s p ctx))))))))))
  (define (decide-some s~ f ctx)
    (log-decide-call 'some f ctx s~)
    (cond
      ((smt.unsat? (smt.check* s~ (upper-bound f ctx)))
       (already-decided 'some #f))
      ((smt.sat? (smt.check* s~ (lower-bound f ctx)))
       (already-decided 'some #t))
      (else
       (match f
         ((list 'not g)
          (not (decide-each s~ g ctx)))
         ((list 'or g* ...)
          (for/or ((g g*))
            (decide-some s~ g (hash-restrict ctx (free-variables g)))))
         ((list 'diamond _ g)
          (smt.solver-push resolver-diamond)
          (smt.solver-assert resolver-diamond (query-constraints 'upper f ctx))
          (smt.solver-assert resolver-diamond (smt.expression->conjuncts s~))
          (define upper-bound-query (smt.solver-debug resolver-diamond))
          (cond
            ((smt.unsat? upper-bound-query)
             (define s~~ (expand-unsat s~ upper-bound-query))
             (algo "expanded (diamond/some, excluded): ~a"
                   (literals-abbreviation
                    (smt.expression->conjuncts s~~)
                    state-vars))
             (add-to-upper-bound! f ctx (smt.nnf (smt.! s~~)))
             (smt.solver-pop resolver-diamond)
             #f)
            (else
             (expect (smt.sat? upper-bound-query))
             (smt.solver-assert resolver-diamond
                                (query-constraints 'lower f ctx))
             (define lower-bound-query (smt.solver-check resolver-diamond))
             (smt.solver-pop resolver-diamond)
             (cond
               ((smt.sat? lower-bound-query)
                (let* ((s (smt.solution->expression lower-bound-query
                                                    #:limit-to state-vars))
                       (i (smt.solution->expression lower-bound-query
                                                    #:limit-to input-vars))
                       (s~~ (expand-transition
                             'predecessor s i
                             (sys.next (lower-bound g ctx)))))
                  (algo "expanded (diamond/some, included): ~a"
                        (literals-abbreviation
                         (smt.expression->conjuncts s~~)
                         state-vars))
                  (add-to-lower-bound! f ctx s~~))
                #t)
               (else
                (algo "check successor")
                (define t+~
                  (let ((t+ (smt.solution->expression
                             upper-bound-query
                             #:limit-to state-vars+)))
                    (cond
                      ((not (expand-successors?))
                       t+)
                      (else
                       (algo "expanding undecided successor (diamond/some)")
                       (let ((i (smt.solution->expression
                                 upper-bound-query
                                 #:limit-to input-vars)))
                         (expand-transition 'successor s~ i t+))))))
                (decide-some (sys.prev t+~) g ctx)
                (algo "proceed (after checking successor)")
                (decide-some s~ f ctx))))))
         ((list 'mu z g)
          (define depth (unrolled-depth f ctx))
          (define ctx~ (hash-set ctx z depth))
          (cond
            ((begin
               (algo "check finite approximation")
               (decide-some s~ z ctx~))
             (algo "approximation is sufficient")
             #t)
            (else
             (algo "consolidate")
             (consolidate-constraints z ctx S)
             (cond
               ((smt.unsat? (smt.check* s~ (upper-bound f ctx)))
                (algo "unrolling is unnecessary")
                #f)
               (else
                (algo "unroll")
                (unroll f ctx)
                (algo "proceed (after unrolling)")
                (decide-some s~ f ctx))))))
         ((? variable? z)
          (expect ; the necessary context, and nothing more
           (set=? (set-subtract (list->set (hash-keys ctx))
                                (ancestors f))
                  (set f)))
          (smt.solver-push resolver-empty)
          (smt.solver-assert resolver-empty (query-constraints 'upper f ctx))
          (smt.solver-assert resolver-empty (smt.expression->conjuncts s~))
          (define upper-bound-query (smt.solver-debug resolver-empty))
          (cond
            ((smt.unsat? upper-bound-query)
             (define s~~ (expand-unsat s~ upper-bound-query))
             (algo "expanded (unrolled/some, excluded): ~a"
                   (literals-abbreviation
                    (smt.expression->conjuncts s~~)
                    state-vars))
             (add-to-upper-bound! f ctx (smt.nnf (smt.! s~~)))
             (smt.solver-pop resolver-empty)
             #f)
            (else
             (expect (smt.sat? upper-bound-query))
             (define lbq-constraints (query-constraints 'lower f ctx))
             (smt.solver-assert resolver-empty lbq-constraints)
             (define lower-bound-query (smt.solver-check resolver-empty))
             (smt.solver-pop resolver-empty)
             (cond
               ((smt.sat? lower-bound-query)
                (define s (smt.solution->expression lower-bound-query
                                                    #:limit-to state-vars))
                (define s~~ (expand-model s lbq-constraints resolver-empty))
                (algo "expanded (unrolled/some, included): ~a"
                      (literals-abbreviation
                       (smt.expression->conjuncts s~~)
                       state-vars))
                (add-to-lower-bound! f ctx s~~)
                #t)
               (else
                (algo "check body")
                (match-define (list 'mu (== z) g) (hash-ref (bindings) z))
                (define ctx- (hash-update ctx z sub1))
                (decide-some s~ g ctx-)
                (algo "proceed (after checking body)")
                (decide-some s~ f ctx))))))
         (_
          (todo "implement `decide-some` for formula: ~a" f)
          (define query (smt.check* s~ (undecided-bound f ctx)))
          (expect (smt.sat? query))
          (define s (smt.solution->expression query #:limit-to state-vars))
          (or (decide s f ctx)
              (decide-some s~ f ctx)))))))
  (define (decide-each s~ f ctx)
    (log-decide-call 'each f ctx s~)
    (cond
      ((smt.sat? (smt.check* s~ (smt.! (upper-bound f ctx))))
       (already-decided 'each #f))
      ((smt.unsat? ; [TODO: static constraints?]
        (smt.check* s~ (smt.! (lower-bound f ctx))))
       (already-decided 'each #t))
      (else
       (match f
         ((list 'not g)
          (not (decide-some s~ g ctx)))
         (_
          (todo "implement `decide-each` for formula: ~a" f)
          (define query (smt.check* s~ (undecided-bound f ctx)))
          (expect (smt.sat? query))
          (define s (smt.solution->expression query #:limit-to state-vars))
          (and (decide s f ctx)
               (decide-each s~ f ctx)))))))
  ;; Solve.
  (define-values (solution explanation)
    (let loop ((iteration 1))
      (info "iteration: ~a" iteration)
      (describe-bounds)
      (cond
        ((smt.sat?
          (smt.check*
           S0 S
           (smt.! (upper-bound P (hash)))))
         (let ((~cex (smt.solution->expression
                      #:limit-to state-vars
                      (smt.check* ; [TODO: redundant]
                       S0 S
                       (smt.! (upper-bound P (hash)))))))
           ;; [TODO: a full counterexample]
           (values #f ~cex)))
        ((smt.unsat?
          (smt.check*
           S0 S
           (smt.! (lower-bound P (hash)))))
         ;; [TODO: inductive invariant]
         (values #t (void)))
        (else
         (define undecided-state-constraints
           (list S0 S (undecided-bound P (hash))))
         (define undecided-state-query
           (apply smt.check* undecided-state-constraints))
         (expect (smt.sat? undecided-state-query))
         (let ((s (smt.solution->expression undecided-state-query
                                            #:limit-to state-vars)))
           (info "undecided top-level state: ~a" s)
           (cond
             ((single-states?)
              (decide s P (hash)))
             (else
              (define s~
                (expand-model s undecided-state-constraints resolver-empty))
              (info "undecided top-level state(s): ~a" s~)
              (decide-each s~ P (hash))))
           (loop (add1 iteration)))))))
  (when #t ; [TODO: clean this up]
    (tabulate-decide-calls)
    (decide-calls empty))
  (info "LB: ~a" (lower-bound P (hash)))
  (info "UB: ~a" (upper-bound P (hash)))
  (info "solution: ~a" solution)
  (when (not (void? explanation))
    (info "explanation: ~a" explanation))
  solution)


(define decide-calls (make-parameter empty))
(define csv-lines (make-parameter empty))
(define (tabulate-decide-calls)
  (define data (reverse (decide-calls)))
  (when (not (empty? data))
    (define properties (subformulas (second (first data))))
    (define p:i
      (for/hash ((p properties))
        (values p (index-of properties p)))) ; [TODO: fix performance]
    (define table
      (array->mutable-array
       (make-array (vector (length properties)
                           (length data))
                   "")))
    (for ((spc data)
          (j (in-range (length data))))
      (array-set! table
                  (vector (hash-ref p:i (second spc))
                          j)
                  (format "~a" (third spc))))
    (define labels (unparse (first properties)))
    (expect (= (length properties)
               (length labels)))
    (define column-of-labels (array-axis-insert (list->array labels) 1))
    (set! table (array-append* (list column-of-labels table) 1))
    (csv-lines (append (csv-lines)
                       (for/list ((row (in-array-axis table 1)))
                         (string-join (map (curry format "~s")
                                           (array->list row))
                                      ","))))))
(define (write-csv f)
  (with-output-to-file f
    #:mode 'text
    #:exists 'replace
    (thunk (for-each displayln (csv-lines)))))


(define (write-bounds-dag base-path)
  (let ((.dot (path-add-extension base-path ".dot"))
        (.svg (path-add-extension base-path ".svg")))
    (with-output-to-file .dot
      #:mode 'text
      #:exists 'replace
      (thunk (displayln (bounds->graphviz))))
    (system (format "dot -T svg ~a -o ~a" .dot .svg))))
