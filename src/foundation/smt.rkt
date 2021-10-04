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
         racket/set)


(require (only-in rosette
                  exists forall
                  ! && || => <=>
                  = + >= <
                  boolean? integer? number?
                  type-of
                  constant symbolics expression constant? expression? term?
                  solver-assert solver-check solver-shutdown
                  solver? solution?
                  solver-push solver-pop solver-clear
                  solver-debug core
                  model complete-solution
                  sat evaluate
                  unsat? sat?
                  output-smt))
(provide (all-from-out rosette))

(require (only-in rosette/base/core/polymorphic
                  ite))
(provide (all-from-out rosette/base/core/polymorphic))

(require (only-in rosette/solver/smt/z3
                  z3))
(provide (all-from-out rosette/solver/smt/z3))


(require (file "z3-names.rkt"))
(provide (all-from-out (file "z3-names.rkt")))


(require (file "../options.rkt"))
(require (file "../util.rkt"))


(provide (all-defined-out))


(define-syntax-rule (define-constant id type)
  (define id (constant (symbol->string (quote id)) type)))


(define check
  (let ((s ; [TODO: respect `--random-seed` CLI option]
         (z3 #:options (hash ':random-seed (smtlib-random-seed)
                             ':sat.random-seed (smtlib-random-seed)
                             ':smt.random-seed (smtlib-random-seed))))
        (push/pop? ; [TODO: CLI?]
         #t))
    (lambda assertions
      (solver-assert s assertions)
      (let ((result (solver-check s)))
        (solver-clear s)
        result))))


(define check*
  (let ((s ; [TODO: respect `--random-seed` CLI option]
         (z3 #:options (hash ':random-seed (smtlib-random-seed)
                             ':sat.random-seed (smtlib-random-seed)
                             ':smt.random-seed (smtlib-random-seed)))))
    (lambda assertions
      (solver-push s)
      (solver-assert s assertions)
      (let ((result (solver-check s)))
        (solver-pop s)
        result))))


(define (solution->expression s #:limit-to (limit-to (void)))
  (define (equals f f~)
    (cond
      ((and (boolean? f) (boolean? f~))
       (<=> f f~))
      ((and (number? f) (number? f~))
       (= f f~))
      (else
       (error 'solution->expression.equals
              "failed to equate terms with types `~a` and `~a`"
              (type-of f)
              (type-of f~)))))
  (if (unsat? s)
      #f
      (let* ((m (model (complete-solution s (listset-union (symbolics s)
                                                           (if (void? limit-to)
                                                               '()
                                                               limit-to)))))
             (keys (hash-keys m))
             (vs (if (not (void? limit-to))
                     (listset-intersect keys limit-to)
                     keys)))
        (apply && (for/list ((v vs))
                    (equals v (hash-ref m v)))))))
(define (expression->solution conjunction-of-literals)
  (sat
   (for/hash ((l (expression->conjuncts conjunction-of-literals)))
     (match l
       ((constant _ boolean?)
        (values l #t))
       ((expression (== !) (and (constant _ boolean?) !l))
        (values !l #f))))))


(define (expression->conjuncts e)
  (match e
    (#t empty)
    ((expression (== &&) f* ...)
     (apply append (map expression->conjuncts f*)))
    (_
     (list e))))


(define (expression->disjuncts e)
  (match e
    (#f empty)
    ((expression (== ||) f* ...)
     (apply append (map expression->disjuncts f*)))
    (_
     (list e))))


(define/contract (nnf f)
  (-> boolean? boolean?)
  ;; Convert a formula to negation normal form (NNF).
  ;;
  ;; This definition is adapted from Huth & Ryan (2004).
  (define/memoized (aux/nnf f)
    (match f
      ((or #f #t
           (constant _ (== boolean?))
           (expression (== !) (constant _ (== boolean?))))
       f)
      ((expression (== !) (expression (== !) g))
       (aux/nnf g))
      ((expression (== !) (expression (== ||) g* ...))
       (apply && (map (compose aux/nnf !) g*)))
      ((expression (== !) (expression (== &&) g* ...))
       (apply || (map (compose aux/nnf !) g*)))
      ((expression (and (or (== ||) (== &&)) op) g* ...)
       (apply op (map aux/nnf g*)))))
  (aux/nnf f))


(define (syntactically-entails? f g #:strict? (strict? #f))
  ((if strict? proper-subset? subset?)
   (expression->disjuncts (nnf f))
   (expression->disjuncts (nnf g))))


(define (semantically-entails? f g #:strict? (strict? #f))
  (and (unsat? (check* f (! g)))
       (or (not strict?)
           (not (semantically-entails? g f #:strict? #f)))))


(define/contract (replace* x:x~ f)
  (-> (hash/c constant? boolean?) boolean? boolean?)
  ;; Replace each occurence of `x` in `f` by `x~`.
  (expect ; no "chained" replacements [TODO: improve this test]
   (let ((x* (list->set (hash-keys x:x~))))
     (for/and ((x~ (hash-values x:x~)))
       (set-empty? (set-intersect (list->set (symbolics x~)) x*)))))
  (define/memoized (aux/replace* f)
    (match f
      ((or #f #t)
       f)
      ((constant _ _)
       (hash-ref x:x~ f f))
      ((expression (and (or (== !) (== ||) (== &&) (== <=>)) op) g* ...)
       (apply op (map aux/replace* g*)))))
  (aux/replace* f))


(define (count . f*)
  ;; Count the number of "true" arguments.
  (apply + (for/list ((f f*)) (ite f 1 0))))
