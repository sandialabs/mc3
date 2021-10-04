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
(require racket/contract
         racket/function
         racket/list
         racket/match
         racket/pretty
         racket/set)


(require (prefix-in gr. graph))


(require (file "foundation.rkt"))
(require (file "mmc.rkt"))
(require (file "util.rkt"))


(provide bound lower-bound upper-bound undecided-bound
         add-to-lower-bound! add-to-upper-bound!
         describe-bounds
         reset-bounds
         unrolled-depth unroll
         consolidate-constraints
         bounds->graphviz)


(define (bound l/u p ctx)
  (bound/raw l/u p ctx))
(define lower-bound (curry bound 'lower))
(define upper-bound (curry bound 'upper))
(define (undecided-bound p ctx)
  (smt.&& (upper-bound p ctx)
          (smt.! (lower-bound p ctx))))


(define/contract (add-to-bound! l/u p ctx x)
  (-> (or/c 'lower 'upper)
      formula/c
      unrolling-context/c
      proposition?
      void?)
  (add-to-bound/raw! l/u p ctx x))
(define add-to-lower-bound!
  (curry add-to-bound! 'lower))
(define (add-to-upper-bound! p ctx x)
  (for ((x~ (smt.expression->conjuncts x)))
    (add-to-bound! 'upper p ctx x~)))


(define/contract (remove-from-bound! l/u p ctx x)
  (-> (or/c 'lower 'upper)
      formula/c
      unrolling-context/c
      proposition?
      void?)
  (remove-from-bound/raw! l/u p ctx x))


(define (describe-bounds)
  (describe-bounds/raw))


(define (reset-bounds)
  (reset-bounds/raw))


(define depths
  (make-parameter (hash)))


(define/contract (unrolled-depth p ctx)
  (-> (list/c 'mu variable? formula/c) unrolling-context/c natural-number/c)
  (define key (contextualized p ctx))
  (define depth (hash-ref (depths) key (void)))
  (cond
    ((void? depth)
     (depths (hash-set (depths) key 1))
     1)
    (else depth)))


(define/contract (unroll p ctx)
  (-> (list/c 'mu variable? formula/c) unrolling-context/c void?)
  (depths (hash-update (depths) (contextualized p ctx) add1)))


(struct bounds-key contextualized (l/u) #:transparent)


(define/contract (consolidate-constraints z ctx S)
  (-> variable? unrolling-context/c proposition? void?)
  (define/contract (propagate-constraints z ctx)
    (-> variable? unrolling-context/c void?)
    (algo "checking propagation for ~a at ~a" z ctx)
    (define tau (third (hash-ref (bindings) z)))
    (define ctx+ (hash-update ctx z add1))
    (define key (bounds-key z ctx 'upper))
    (when (hash-has-key? (bounds/raw) key)
      (for ((u (hash-ref (bounds/raw) key)))
        (debug "candidate for propagation: ~a" u)
        (define query
          (smt.check*
           (smt.! u)
           S
           (bound 'upper z ctx+) ; changes throughout loop
           (bound 'upper tau ctx)))
        (cond
          ((smt.unsat? query)
           (algo "propagate: ~a" u)
           (remove-from-bound! 'upper z ctx u)
           (add-to-upper-bound! z ctx+ u))
          (else
           (define cex (smt.solution->expression query))
           (debug "counterexample to propagation: ~a" cex))))))
  (define/contract (induce-constraints z ctx)
    (-> variable? unrolling-context/c void?)
    (algo "checking induction for ~a at ~a" z ctx)
    (define key (bounds-key z ctx 'upper))
    (define ctx+ (hash-update ctx z add1))
    (define key+ (bounds-key z ctx+ 'upper))
    (when (and (hash-has-key? (bounds/raw) key)
               (hash-has-key? (bounds/raw) key+))
      (define constraints+ (hash-ref (bounds/raw) key+))
      (define cnd+ (apply smt.&& constraints+))
      (define (syntactic-check?)
        ;; Check whether each term that was stored "locally" at this depth
        ;; (i.e., that was not inferred from a deeper term) was propagated to
        ;; the subsequent depth, which is a necessary condition for induction.
        (let ((success? (empty? (hash-ref (bounds/raw) key))))
          (when success? (debug "candidate for induction: ~a" cnd+))
          success?))
      (define (semantic-check?)
        ;; Check whether the bound at the subsequent depth is as strong as the
        ;; one at this depth (including the terms inferred from other contexts),
        ;; which is a sufficient condition for induction.
        (let* ((query (smt.check* (smt.&&
                                   S
                                   (bound 'upper z ctx+)
                                   (smt.! (bound 'upper z ctx)))))
               (success? (smt.unsat? query)))
          (unless success?
            (debug "counterexample to induction: ~a"
                   (smt.solution->expression query)))
          success?))
      (when (and ; skip `semantic-check?` unless `syntactic-check?` passes
             (syntactic-check?)
             (semantic-check?))
        (algo "induce: ~a" cnd+)
        (define fp (hash-ref (bindings) z))
        (for ((c+ constraints+))
          (add-to-upper-bound! fp (hash-remove ctx z) c+))
        (bounds/raw (hash-set (bounds/raw) key+ empty)))))
  (define fp (hash-ref (bindings) z))
  (define frontier (unrolled-depth fp ctx))
  (when (not (void? frontier))
    (for ((k (in-range 1 frontier))) ; excludes `frontier` itself
      (define ctx~ (hash-set ctx z k))
      (propagate-constraints z ctx~)
      (induce-constraints z ctx~))))


(define/contract (related? b b~)
  (-> bounds-key? bounds-key? boolean?)
  ;; Is `b` related to `b~` (in the sense that it's valid to include terms from
  ;; `b~`'s bound in `b`'s bound)?
  (define l/u (bounds-key-l/u b))
  (define l/u~ (bounds-key-l/u b~))
  (and (eq? l/u l/u~)
       (match l/u
         ('lower (contextualized<=? b~ b))
         ('upper (contextualized<=? b b~)))))


(define (bounds->graphviz)
  (bounds->graphviz/raw))




;;;;;;;;;;;;;;;;
; "Raw" Bounds ;
;;;;;;;;;;;;;;;;


(define/contract bounds/raw
  (parameter/c (hash/c bounds-key? (listof proposition?)))
  ;; The bounds represent information related to the states that satisfy a
  ;; property.  The first element is the list of /lower/-bound terms, and the
  ;; second is the list of /upper/-bound terms.  The disjunction/conjunction of
  ;; the lower-/upper-bound terms is "the" lower/upper bound.
  (make-parameter (hash)))


(define (describe-bounds/raw)
  (define (sorted-bound-keys)
    (define/contract (order-bounds* a b)
      (-> bounds-key? bounds-key? (or/c '< '~ '>))
      (define (decontextualize* x)
        (match x
          ((contextualized p ctx)
           (contextualize p ctx))
          (_ ; an atomic proposition?
           x)))
      (let ((~order (order-formulas (decontextualize* a) (decontextualize* b))))
        (if (and (eq? '~ ~order)
                 (eq? 'lower (bounds-key-l/u a))
                 (eq? 'upper (bounds-key-l/u b)))
            '<
            ~order)))
    (sort (hash-keys (bounds/raw))
          (lambda (a b)
            (eq? '< (order-bounds* a b)))))
  (info "bounds:~n~a"
        (indent-lines
         (pretty-format
          #:mode 'display
          (for/list ((k (sorted-bound-keys)))
            (k-v k (hash-ref (bounds/raw) k)))))))


(define (bounds->graphviz/raw)
  (define keys (hash-keys (bounds/raw)))
  (define edges
    (apply append (for/list ((b keys))
                    (for/list ((b~ (directly-related-bounds/raw b)))
                      (list b b~)))))
  (define (->label b)
    (format "~a~n~a~n~a"
            (formula->string (contextualized-formula b) #:abbreviate? #t)
            (contextualized-context b)
            (bounds-key-l/u b)))
  (define edges~ (map (curry map ->label) edges))
  (define dag
    (let ((~dag (gr.directed-graph edges~)))
      (for ((b keys))
        (gr.add-vertex! ~dag (->label b)))
      ~dag))
  (gr.graphviz dag))


(define/contract (initial-bound/raw l/u p ctx)
  (-> (or/c 'lower 'upper) formula/c unrolling-context/c
      (listof proposition?))
  (match p
    ((list (or 'diamond 'mu) _ _)
     empty)
    ((? variable? z)
     (if (zero? (hash-ref ctx z))
         '(#f)
         empty))))


(define/contract (bound/raw l/u p ctx)
  (-> (or/c 'lower 'upper) formula/c unrolling-context/c proposition?)
  (match p
    ((? proposition?)
     p)
    ((list 'not q)
     (match l/u
       ('lower (smt.! (bound/raw 'upper q ctx)))
       ('upper (smt.! (bound/raw 'lower q ctx)))))
    ((list 'or q* ...)
     (apply smt.||
            (for/list ((q q*))
              (bound/raw l/u q (hash-restrict ctx (free-variables q))))))
    (_
     (define b (bounds-key p ctx l/u))
     (define relatives (related-bounds/raw b))
     (apply (match l/u ('lower smt.||) ('upper smt.&&))
            (apply append
                   (cons (hash-ref (bounds/raw)
                                   (bounds-key p ctx l/u)
                                   (initial-bound/raw l/u p ctx))
                         (map (curry hash-ref (bounds/raw))
                              relatives)))))))


(define (reset-bounds/raw)
  (bounds/raw (hash)))


(define (add-to-bound/raw! l/u p ctx x)
  (define b (bounds-key p ctx l/u))
  (define status
    (cond
      ((for/or ((x~ (hash-ref (bounds/raw) b (initial-bound/raw l/u p ctx))))
         (and (smt.syntactically-entails? x x~ #:strict? #f)
              (smt.syntactically-entails? x~ x #:strict? #f)))
       ;; The term is already present; be careful to not both remove the
       ;; already-present (subsumed) "version" and then neglect to add the new
       ;; (redundant) "version"!
       'duplicate)
      ((for/or ((b~ (hash-keys (bounds/raw)))
                #:when (eq? l/u (bounds-key-l/u b~))
                #:when (related? b b~))
         (for/or ((x~ (hash-ref (bounds/raw) b~)))
           (match l/u
             ('upper
              (smt.syntactically-entails? x~ x #:strict? #f))
             ('lower
              (smt.syntactically-entails? (smt.! x~)
                                          (smt.! x)
                                          #:strict? #f)))))
       ;; Order matters: building on the previous ("duplicate") case, the term
       ;; is strictly subsumed here, or is (not-necessarily-strictly) subsumed
       ;; elsewhere; it can safely be ignored.
       'redundant)
      (else
       'new)))
  (algo "~a ~a-bound term:~n formula: ~a~n context: ~a~n term: ~a"
        status l/u p ctx x)
  (for ((b~ (sort (hash-keys (bounds/raw)) related?))
        #:when (eq? l/u (bounds-key-l/u b~))
        #:when (related? b~ b))
    (define subsumed
      (for/list ((x~ (hash-ref (bounds/raw) b~))
                 #:when
                 (match l/u
                   ('upper
                    (smt.syntactically-entails? x x~ #:strict? #f))
                   ('lower
                    (smt.syntactically-entails? (smt.! x)
                                                (smt.! x~)
                                                #:strict? #f))))
        x~))
    (when (not (empty? subsumed))
      (algo
       "subsumed ~a-bound term(s):~n formula: ~a~n context: ~a~n term(s): ~a"
       (bounds-key-l/u b~)
       (contextualized-formula b~)
       (contextualized-context b~)
       subsumed)
      (bounds/raw
       (hash-update
        (bounds/raw)
        b~
        (curryr set-subtract subsumed)))))
  (when (match status ((or 'new 'duplicate) #t) ('redundant #f))
    ;; [NOTE: a "duplicate" will have "subsumed" itself, and must be added back]
    (bounds/raw
     (hash-set (bounds/raw)
               b
               (cons x (hash-ref (bounds/raw)
                                 b
                                 (initial-bound/raw l/u p ctx)))))))


(define (remove-from-bound/raw! l/u p ctx x)
  (define key (bounds-key p ctx l/u))
  (bounds/raw (hash-update (bounds/raw) key (curry remove* (list x)))))


(define (related-bounds/raw b)
  (remove b
          (filter (curry related? b)
                  (hash-keys (bounds/raw)))))


(define (directly-related-bounds/raw b)
  (define relatives (related-bounds/raw b))
  (for/list ((r relatives)
             #:when (not (ormap (lambda (r~) (related? r~ r))
                                (remove r relatives))))
    r))
