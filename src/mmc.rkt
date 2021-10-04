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
         racket/hash
         racket/list
         racket/match
         racket/math
         racket/set
         racket/string)


(require (file "foundation.rkt"))
(require (file "options.rkt"))
(require (file "util.rkt"))


(provide (all-defined-out))


(define proposition? smt.boolean?)
(define atom? (and/c proposition? smt.constant?))
(define variable? symbol?)
(define (formula-over/c x)
  (define (recur y)
    (recursive-contract (formula-over/c y) #:chaperone))
  (if (skip-slow-contracts?)
      any/c
      (first-or/c x
                  (list/c 'not (recur x))
                  (cons/c 'or (listof (recur x)))
                  (cons/c 'diamond (list/c (recur x) (recur x)))
                  (cons/c 'mu (cons/dc
                               (hd variable?)
                               (tl (hd) (list/c (recur (or/c x hd)))))))))
(define closed-formula/c (formula-over/c proposition?))
(define formula/c (formula-over/c (or/c proposition? variable?)))


(define/contract (expand-formula p)
  (-> any/c closed-formula/c)
  ;; Expand a formula in terms of a core set of operators.
  (simplify-formula
   (match p
     ;; Boolean.
     ((list 'iff q* ...)
      (expand-formula
       `(or (and ,@q*)
            (and ,@(map (curry list 'not) q*)))))
     ((list 'if-then p q)
      (expand-formula
       `(or (not ,p)
            ,q)))
     ;; CTL.
     ((list 'AX q)
      (expand-formula
       `(box* ,q)))
     ((list 'EF q)
      (let ((z (string->symbol (format "EF/~a" (next-fixed-point)))))
        (expand-formula
         `(mu ,z (or ,q (diamond* ,z))))))
     ((list 'EG q)
      (let ((z (string->symbol (format "EG/~a" (next-fixed-point)))))
        (expand-formula
         `(nu ,z (and ,q (diamond* ,z))))))
     ((list 'AF q)
      (let ((z (string->symbol (format "AF/~a" (next-fixed-point)))))
        (expand-formula
         `(mu ,z (or ,q (and (box* ,z) (diamond* #t)))))))
     ((list 'AG q)
      (let ((z (string->symbol (format "AG/~a" (next-fixed-point)))))
        (expand-formula
         `(nu ,z (and ,q (box* ,z))))))
     ;; MMC's "other half".
     ((list 'and q* ...)
      (expand-formula
       `(not (or ,@(map (curry list 'not) q*)))))
     ((list 'box alpha q)
      (expand-formula
       `(not (diamond ,alpha (not ,q)))))
     ((list 'nu z tau)
      (let ((~z (string->symbol (format "~~~a" (symbol->string z)))))
        (expand-formula
         `(not (mu ,~z (not ,(tree-substitute (list 'not ~z) z tau)))))))
     ;; "Non-qualified" modalities.
     ((list 'diamond* q)
      (list 'diamond #t (expand-formula q)))
     ((list 'box* q)
      (expand-formula
       (list 'box #t q)))
     ;; The "simple" cases.
     ((or (? proposition?)
          (? variable?))
      p)
     ((list 'not q)
      (list 'not (expand-formula q)))
     ((list 'or q* ...)
      (cons 'or (map expand-formula q*)))
     ((list 'diamond alpha q)
      (list 'diamond alpha (expand-formula q)))
     ((list 'mu z tau)
      (list 'mu z (expand-formula tau))))))
(define/contract next-fixed-point
  (-> positive-integer?)
  (let ((n 0))
    (lambda ()
      (set! n (add1 n))
      n)))


(define/contract (simplify-formula p)
  (-> formula/c formula/c)
  ;; Apply some simple rewrite rules [TODO: more!] to simplify a formula.
  (match p
    ((list 'not (list 'not q))
     (simplify-formula q))
    ((list 'not (? smt.boolean? q))
     (smt.! q))
    ;;
    ((list 'not q)
     (list 'not (simplify-formula q)))
    ((list 'or q* ...)
     (let ((q*~ (remove*
                 (list #f)
                 (remove-duplicates
                  (map simplify-formula q*)))))
       (cond
         ((empty? q*~)
          #f)
         ((= 1 (length q*~))
          (first q*~))
         (else
          (cons 'or q*~)))))
    ((list 'diamond alpha q)
     (list 'diamond (simplify-formula alpha) (simplify-formula q)))
    ((list 'mu z tau)
     (let ((tau~ (simplify-formula tau)))
       (if (not (hash-has-key? (direct-polarities tau~) z))
           tau~
           (list 'mu z tau~))))
    (_ p)))


(define/contract (formula->string p #:abbreviate? (abbreviate? #f))
  (->* (closed-formula/c)
       (#:abbreviate? boolean?)
       string?)
  ;; "Pretty print" a formula.
  (define recur (curry formula->string #:abbreviate? abbreviate?))
  (match p
    (#f "⊥")
    (#t "⊤")
    ((? (compose not list?))
     (format "~a" p))
    ((list 'not q)
     (format "(¬ ~a)" (recur q)))
    ((list 'not _ ...)
     (error 'formula->string "invalid `not` syntax: ~a" p))
    ((list 'or q r* ...)
     (format "(∨ ~a)" (string-join (map recur (cons q r*)) " ")))
    ((list 'or _ ...)
     (error 'formula->string "invalid `or` syntax: ~a" p))
    ((list 'diamond alpha q)
     (format "(⋄ ~a ~a)" (recur alpha) (recur q)))
    ((list 'diamond _ ...)
     (error 'formula->string "invalid `diamond` syntax: ~a" p))
    ((list 'mu z tau)
     (format "(μ ~a ~a)"
             (recur z)
             (if abbreviate?
                 "..."
                 (recur tau))))
    ((list 'mu _ ...)
     (error 'formula->string "invalid `mu` syntax: ~a" p))
    (_
     (error 'formula->string "unrecognized syntax: ~a" p))))


(define/contract (subformulas p)
  (-> closed-formula/c (non-empty-listof formula/c))
  ;; Return the list of subformulas of a formula (including the formula itself).
  (cons
   p
   (match p
     ((or (? proposition?)
          (? variable?))
      empty)
     ((list 'not q)
      (subformulas q))
     ((list 'or q* ...)
      (apply append (map subformulas q*)))
     ((list 'diamond alpha q)
      (subformulas q))
     ((list 'mu z tau)
      ;; [TODO: decide whether to include the bound variable explicitly]
      (cons z (subformulas tau))))))


(define/contract (unparse p)
  (-> closed-formula/c (non-empty-listof string?))
  ;; Produce a flat list that contains the "pieces" of a formula.
  (define (close-paren x*)
    (list-update x* (sub1 (length x*)) (curry format "~a)")))
  (match p
    ((or (? proposition?)
         (? variable?))
     (list (format "~a" p)))
    ((list 'not q)
     (cons "(not" (close-paren (unparse q))))
    ((list 'or q* ...)
     (cons "(or" (close-paren (apply append (map unparse q*)))))
    ((list 'diamond alpha q)
     (cons (format "(diamond ~a" alpha) (close-paren (unparse q))))
    ((list 'mu z tau)
     (cons "(mu" (close-paren (append (unparse z)
                                      (unparse tau)))))))


(define bindings/c
  ;; [TODO: encode the dependency that the `variable?`s are the same]
  (hash/c variable? (list/c 'mu variable? formula/c)))
(define/contract bindings
  (parameter/c bindings/c)
  ;; Provide a place to cache the fixed point bindings that appear in a formula.
  (make-parameter (hash)))


(define/contract (fixed-point-bindings p)
  (-> closed-formula/c bindings/c)
  ;; Find the fixed point bindings that appear in a formula (as subformulas).
  (match p
    ((list 'not q)
     (fixed-point-bindings q))
    ((list 'or q* ...)
     (apply (curry hash-union #:combine (lambda (a b)
                                          (expect (equal? a b))
                                          a))
            (map fixed-point-bindings q*)))
    ((list 'diamond _ q)
     (fixed-point-bindings q))
    ((list 'mu z tau)
     (hash-union (hash z p)
                 (fixed-point-bindings tau)))
    (_ (hash))))


(define polarity/c (or/c '+ '-))
(define/contract (combine-polarities a b)
  (-> polarity/c polarity/c polarity/c)
  (expect (eq? a b))
  a)
(define polarities/c (hash/c variable? polarity/c))
(define/contract (invert-polarities p)
  (-> polarities/c polarities/c)
  ;; Invert polarities by swapping positive and negative.
  (define (flip +/-) (match +/- ('+ '-) ('- '+)))
  (for/hash (((z +/-) p))
    (values z (flip +/-))))
(define/contract (direct-polarities f)
  (-> formula/c polarities/c)
  ;; Compute the polarities between a formula and each of its free variables.
  (match f
    ((? proposition?)
     (hash))
    ((list 'not g)
     (invert-polarities (direct-polarities g)))
    ((list 'or g* ...)
     (apply (curry hash-union #:combine combine-polarities)
            (map direct-polarities g*)))
    ((list 'diamond _ g)
     (direct-polarities g))
    ((list 'mu z g)
     (hash-remove (direct-polarities g) z))
    ((? variable?)
     (hash f '+))))
(define relative-polarities/c (hash/c variable? polarities/c))
(define/contract (bindings->relative-polarities bndgs)
  (-> bindings/c relative-polarities/c)
  ;; Compute the relative polarities among a set of nested fixed points.
  (define direct
    (for/hash (((z fp) bndgs))
      (match-define (list 'mu _ g) fp)
      (values z (direct-polarities g))))
  (define (extend z stale)
    (define stale~ (cons z stale))
    (define p (hash-ref direct z))
    (define fresh (set-subtract (hash-keys p) stale~))
    (apply (curry hash-union #:combine combine-polarities)
           (cons p (for/list ((z~ fresh))
                     ((match (hash-ref p z~)
                        ('+ identity)
                        ('- invert-polarities))
                      (extend z~ (set-union stale~ fresh)))))))
  (let ((indirect (for/hash ((z (hash-keys direct)))
                    (values z (extend z empty)))))
    (for (((z p) indirect))
      (expect (eq? '+ (hash-ref p z '+))))
    indirect))
(define/contract relative-polarities
  (parameter/c relative-polarities/c)
  ;; Provide a place to cache the polarities among fixed points in a formula.
  (make-parameter (hash)))
(define/contract (polarities f)
  (-> formula/c polarities/c)
  ;; Compute the polarities between a formula and each of its /influences/.
  ;;
  ;; The influences include not just each fixed points whose bound variable
  ;; appears free in this formula, but also each one that influences each of
  ;; those associated fixed points.
  (define direct (direct-polarities f))
  (apply (curry hash-union #:combine combine-polarities)
         (cons (hash) ; `hash-union` expects one or more arguments
               (for/list (((z p) direct))
                 ((match p
                    ('+ identity)
                    ('- invert-polarities))
                  (hash-ref (relative-polarities) z))))))


(define/contract (free-variables x)
  (-> formula/c (set/c variable?))
  ;; Find the free variables in a formula.
  (let ((ff (list->set (hash-keys (direct-polarities x)))))
    (apply set-union
           (cons
            ff
            (set-map ff
                     (compose list->set
                              hash-keys
                              (curry hash-ref (relative-polarities))))))))


(define/contract (ancestors x)
  (-> variable? (set/c variable?))
  ;; Return the ancestors of a fixed point (/not/ including itself).
  (set-remove (list->set (hash-keys (hash-ref (relative-polarities) x)))
              x))
(define/contract (ancestor? candidate relative-to)
  (-> variable? variable? boolean?)
  (set-member? (ancestors relative-to) candidate))


(define unrolling-context/c
  ;; Map a variable to a number of "Knaster-Tarski fixed-point iterations".
  (hash/c variable? natural? #:immutable #t))


(define/contract (context->scope c)
  (-> unrolling-context/c (listof variable?))
  ;; "Linearize" a context to the corresponding nesting/scoping order.
  (cond
    ((hash-empty? c)
     empty)
    (else
     (let* ((vars (hash-keys c))
            (not-bottom-vars
             (apply set-union (map (compose set->list ancestors)
                                   vars)))
            (bottom-vars (set-subtract vars not-bottom-vars))
            (bottom-var (first bottom-vars)))
       (expect (= 1 (length bottom-vars)))
       (append ; [TODO: rewrite in terms of `cons` and `reverse`]
        (context->scope (hash-remove c bottom-var))
        (list bottom-var))))))


(define/contract (truncate-context ctx v #:strict? (strict? #f))
  (->* (unrolling-context/c
        variable?)
       (#:strict? boolean?)
       unrolling-context/c)
  ;; Truncate a context to only include the given fixed point's ancestors.
  (define keep
    (let ((~keep (ancestors v)))
      (if strict?
          ~keep
          (set-add ~keep v))))
  (for/hash ((k keep)
             #:when (hash-has-key? ctx k))
    (values k (hash-ref ctx k))))


(struct contextualized (formula context) #:transparent)


(define contextualized-property*/c
  (formula-over/c (or/c proposition?
                        (list/c variable? unrolling-context/c)
                        variable?)))


(define/contract (contextualize p ctx)
  (-> formula/c unrolling-context/c contextualized-property*/c)
  (define recur ; omit contract for better performance
    (curryr contextualize ctx))
  (match p
    ((? proposition?)
     p)
    ((list 'not q)
     (list 'not (recur q)))
    ((list 'or q* ...)
     (cons 'or (map recur q*)))
    ((list 'diamond alpha q)
     (list 'diamond alpha (recur q)))
    ((list 'mu z tau)
     (list 'mu z (contextualize tau
                                (truncate-context ctx z #:strict? #t))))
    ((? variable?)
     (if (hash-has-key? ctx p)
         (list p (truncate-context ctx p))
         p))
    ((list (? variable?) (? unrolling-context/c))
     (raise-argument-error
      'contextualize "a not-yet-contextualized variable" p))))


(define/contract (formula-variables p #:input-location? (input-location? #f))
  (->* (closed-formula/c)
       (#:input-location? boolean?)
       (list/c (listof (or/c variable? smt.constant?))
               (listof (or/c variable? smt.constant?))))
  ;; Find the variables that occur in "state" and "input" places in a formula.
  (define recur (curry formula-variables #:input-location? input-location?))
  (match p
    ((? proposition?)
     (let ((vars (smt.symbolics p)))
       (if input-location?
           (list empty vars)
           (list vars empty))))
    ((list 'not q)
     (recur q))
    ((list 'or q* ...)
     (let ((rec-q* (map recur q*)))
       (list (apply set-union (map first rec-q*))
             (apply set-union (map second rec-q*)))))
    ((list 'diamond alpha q)
     (let ((i (formula-variables alpha #:input-location? #t))
           (s (formula-variables q #:input-location? #f)))
       (list (set-union (first i) (first s))
             (set-union (second i) (second s)))))
    ((list 'mu z tau)
     (let ((rec-tau (recur tau)))
       (list (remove* (list z) (first rec-tau))
             (second rec-tau))))
    ((? variable?) ; a fixed point variable, not a state/input variable
     (if input-location?
         ;; [TODO: this should be an error]
         (list empty (list p))
         (list (list p) empty)))))


(define/contract (malformed-formula? p m)
  (-> closed-formula/c sys.lts? boolean?)
  ;; Check whether a formula's variables appear in invalid places.
  (match-define (list p-states p-inputs) (formula-variables p))
  (match-define (sys.lts m-states m-inputs _ _ _ _ _) m)
  (not ; (not valid) -> /invalid/
   (and ; requirements for the formula to be /valid/
    (empty? (set-intersect p-states p-inputs)) ; disjoint state & input places
    (empty? (set-intersect p-states m-inputs)) ; no inputs in state places
    (empty? (set-intersect p-inputs m-states)) ; no states in input places
    (andmap ; unnecessary?  (enforced by the `closed-formula/c` contract)
     (negate variable?) p-states)
    (andmap ; fixed point variables are "state like"
     (negate variable?) p-inputs))))




(define/contract (order-formulas a b)
  (-> contextualized-property*/c contextualized-property*/c (or/c '< '~ '>))
  ;; Compute the ordering relationship between two formulas.
  (define (ap<? x y)
    (define vars-x (smt.symbolics x))
    (define vars-y (smt.symbolics y))
    (cond
      ((< (length vars-x) (length vars-y)) #t)
      ((> (length vars-x) (length vars-y)) #f)
      (else (string<? (format "~a" x) (format "~a" y)))))
  (define (context<? c1 c2)
    (expect (set=? (hash-keys c1) (hash-keys c2)))
    (let loop ((scope (context->scope c1)))
      (cond
        ((empty? scope) #f)
        ((< (hash-ref c1 (first scope))
            (hash-ref c2 (first scope)))
         #t)
        ((= (hash-ref c1 (first scope))
            (hash-ref c2 (first scope)))
         (loop (rest scope)))
        (else #f))))
  (match a
    ((? proposition?)
     (match b
       ((? proposition?)
        (cond
          ((ap<? a b) '<)
          ((ap<? b a) '>)
          (else '~)))
       (_ '<)))
    ((list 'not q)
     (match b
       ((? proposition?) '>)
       ((list 'not q~)
        (order-formulas q q~))
       (_ '<)))
    ((list 'or q* ...)
     (match b
       ((? proposition?) '>)
       ((list 'not _) '>)
       ((list 'or q*~ ...)
        (define (<? x y)
          (eq? '< (order-formulas x y)))
        (define sorted-q* (sort q* <?))
        (define sorted-q*~ (sort q*~ <?))
        (cond
          ((< (length q*) (length q*~)) '<)
          ((> (length q*) (length q*~)) '>)
          (else
           (define q*/q*~
             (for/list ((q sorted-q*)
                        (q~ sorted-q*~))
               (order-formulas q q~)))
           (cond
             ((or (subset? q*/q*~ '(~))
                  (subset? '(< >) q*/q*~))
              '~)
             ((set-member? q*/q*~ '<) '<)
             ((set-member? q*/q*~ '>) '>)))))
       (_ '<)))
    ((list 'diamond alpha q)
     (match b
       ((? proposition?) '>)
       ((list 'not _) '>)
       ((list 'or _ ...) '>)
       ((list 'diamond u~ q~)
        (cond
          ((ap<? alpha u~) '<)
          ((ap<? u~ alpha) '>)
          (else
           (order-formulas q q~))))
       (_ '<)))
    ((list 'mu z tau)
     (match b
       ((? proposition?) '>)
       ((list 'not _) '>)
       ((list 'or _ ...) '>)
       ((list 'diamond _ _) '>)
       ((list 'mu z~ tau~)
        (define z/z~
          (order-formulas (list z (hash)) (list z~ (hash))))
        (if (not (eq? z/z~ '~))
            z/z~
            (order-formulas tau tau~)))
       (_ '<)))
    ((list (? variable? z) (? unrolling-context/c ctx))
     (match b
       ((? proposition?) '>)
       ((list 'not _) '>)
       ((list 'or _ ...) '>)
       ((list 'diamond _ _) '>)
       ((list 'mu _ _) '>)
       ((list (? variable? z~) (? unrolling-context/c ctx~))
        (cond
          ((eq? z z~)
           (cond
             ((context<? ctx ctx~) '<)
             ((context<? ctx~ ctx) '>)
             (else '~)))
          ((ancestor? z~ z)
           '<)
          ((ancestor? z z~)
           '>)
          (else
           (if (string<? (symbol->string z)
                         (symbol->string z~))
               '<
               '>))))))
    ((? variable?) ; a "raw" bound variable, inside its binding fixed point
     '~)
    (_ '~)))


(define/contract (contextualized<=? c c~)
  (-> contextualized? contextualized? boolean?)
  ;; Is `c` (syntactically) "stronger" than `c~`?
  ;;
  ;; "Stronger" basically means implication, as in a smaller set of satisfying
  ;; states.  In the case of finite approximations of a [least] fixed point, a
  ;; "shallower" approximation is stronger than a "deeper" one (from
  ;; monotonicity), all other relevant context being equal.  That notion of
  ;; depth extends to the case of multiple fixed points, modulo "polarity"
  ;; (i.e., whether a particular variable appears "positively" or "negatively");
  ;; note that polarity is a "global" property of the top-level formula that `c`
  ;; and `c~` contain subformulas of, so the calculation depends on that
  ;; nonlocal information.
  (match-define (contextualized f ctx) c)
  (match-define (contextualized f~ ctx~) c~)
  (cond
    ((equal? f f~)
     ;; The formulas are the same, so compare the contexts.
     (let ((p (polarities f))
           (z* (hash-keys ctx)))
       (expect (set=? z* (hash-keys ctx~)))
       (andmap (lambda (z) ((match (hash-ref p z)
                              ('+ <=)
                              ('- >=))
                            (hash-ref ctx z)
                            (hash-ref ctx~ z)))
               z*)))
    ((variable? f)
     ;; A fixed point is conceptually the "infinite" unrolling/approximation, so
     ;; use transitivity to relate finite approximations to other fixed points.
     (contextualized<=? (contextualized (hash-ref (bindings) f)
                                        (hash-remove ctx f))
                        c~))
    (else
     ;; [TODO: `a < b -{monotonicity}-> (diamond a) < (diamond b)`, etc.?]
     #f)))
