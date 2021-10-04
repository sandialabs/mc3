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
         racket/hash
         racket/list
         racket/match
         racket/string)


(require (prefix-in smt. (file "smt.rkt")))
(require (file "../util.rkt"))


(provide (all-defined-out))


(define (next x)
  ;; Return the "next" counterpart of a formula, /after/ a transition.
  ;;
  ;; The result is essentially the same formula, but with a "+" appended to the
  ;; end of each variable's name.
  (define/memoized (next/aux x)
    (match x
      ((smt.constant id type)
       (smt.constant (format "~a+" id) type))
      ((smt.expression op arg ...)
       (cond
         ((eq? op smt.exists)
          (op (map next/aux (first arg)) (next/aux (second arg))))
         (else
          (apply op (map next/aux arg)))))
      (_ x)))
  (next/aux x))


(define (prev x)
  ;; Return the "previous" counterpart of a formula, /before/ a transition.
  ;;
  ;; The result is the opposite of `next`, i.e., a "+" is removed from the end
  ;; of each variable's name.  The case of a variable that does not end with a
  ;; "+" is not handled.[MAYBE: use "-" similarly to "+" in `next`]
  (match x
    ((smt.constant id type)
     (when (not (string-suffix? id "+"))
       (raise-argument-error 'prev "a \"next-state\" variable"))
     (smt.constant (substring id 0 (- (string-length id) 1)) type))
    ((smt.expression op arg ...)
     (apply op (map prev arg)))
    (_ x)))


(struct lts
  ;; Represent a labeled transition system (LTS).
  ;;
  ;; If the structure of the transition relation is known (i.e., it can be
  ;; decomposed as `state-constraints`, `input-constraints`, etc.), then storing
  ;; those separately --- as opposed to simply lumping them all into
  ;; `transition-constraints` --- may make subsequent analysis easier.
  (state-variables
   input-variables
   state-constraints
   input-constraints
   state-input-constraints
   input-next-state-constraints
   transition-constraints)
  #:transparent)


(define (lts-transition-relation l) ; [MAYBE: define this in `struct lts`]
  ;; Build the LTS's transition relation.
  ;;
  ;; If the transition relation was stored in a decomposed form, then it may
  ;; need to be recomposed --- the dynamics may not be fully defined by the
  ;; `transition-constraints` alone.
  (match-define (lts _ _ S I SI IS+ T) l)
  (smt.&& S I SI IS+ T (next S)))


(define/contract (total-transition-relation? f/b l)
  (-> (or/c 'forward 'backward) lts? boolean?)
  ;; Check whether the LTS's transition relation is /total/.
  ;;
  ;; /Forward/ totality is checked with respect to the state-, input-, and
  ;; state-input constraints, while /backward/ totality is checked w.r.t. the
  ;; input-, next-state-, and input-next-state-constraints.
  ;;
  ;; The check is whether
  ;;
  ;;   "(assumptions met) implies (exists transition)"
  ;;
  ;; is /valid/, which amounts to checking whether
  ;;
  ;;   "(assumptions met) and (no transition)"
  ;;
  ;; is /not satisfiable/.
  (match-define (lts x u S I SI IS+ _) l)
  (define w.r.t.
    (match f/b
      ('forward (smt.&& S I SI))
      ('backward (smt.&& I IS+ (next S)))))
  (define no-transition
    (smt.forall (match f/b
                  ('forward (map next x))
                  ('backward x))
                (smt.! (lts-transition-relation l))))
  (define query
    ;; Use `smt.check` (which uses clear instead of push/pop), because
    ;; apparently[TODO: bug in Rosette?] quantifiers and push/pop don't get
    ;; along.
    (smt.check w.r.t. no-transition))
  (define total? (smt.unsat? query))
  (when (not total?)
    (warning
     "transition relation is NOT ~a total; no transition exists for ~a"
     f/b
     (smt.solution->expression query)))
  total?)


(define/contract (reverse-lts Sigma)
  (-> lts? lts?)
  ;; "Reverse" an LTS by swapping its current- and next-state variables.
  (match-define (lts x u S I SI IS+ T) Sigma)
  (define x++:x (for/hash ((var x)) (values (next (next var)) var)))
  (define u+:u (for/hash ((var u)) (values (next var) var)))
  (define x++u+:xu (hash-union x++:x u+:u))
  (define -IS+ (smt.replace* u+:u (next SI)))
  (define -SI (smt.replace* x++u+:xu (next IS+)))
  (define -T (smt.replace* x++u+:xu (next T)))
  (lts x u S I -SI -IS+ -T))
