#lang racket/base


;; Rawlings (submitted to VMCAI 2022), "Satisfiability-Based Modal Mu Calculus
;; Model Checking Without Unrolling", running example.


(require (file "../src/foundation.rkt"))


(provide problem)
(smt.define-constant x1 smt.boolean?)
(smt.define-constant x2 smt.boolean?)
(smt.define-constant u1 smt.boolean?)
(define s00 (smt.&& (smt.! x1) (smt.! x2)))
(define s01 (smt.&& (smt.! x1) x2))
(define s10 (smt.&& x1 (smt.! x2)))
(define s11 (smt.&& x1 x2))
(define i0 (smt.! u1))
(define i1 u1)
(define problem
  (vector
   (sys.lts (list x1 x2)
            (list u1)
            #t
            #t
            #t
            #t
            (smt.&&
             ;; Outgoing transitions.
             (smt.=> s00
                     (sys.next (smt.|| s00 s11)))
             (smt.=> s01
                     (sys.next s11))
             (smt.=> s10
                     (smt.|| (smt.&& i0 (sys.next s00))
                             (smt.&& i1 (sys.next (smt.|| s01 s10)))))
             (smt.=> s11
                     (sys.next s11))
             ;; Incoming transitions.
             (smt.=> (sys.next s00)
                     (smt.|| s00 (smt.&& s10 i0)))
             (smt.=> (sys.next s01)
                     (smt.&& s10 i1))
             (smt.=> (sys.next s10)
                     (smt.&& s10 i1))
             (smt.=> (sys.next s11)
                     (smt.! s10))))
   s10
   ;; Related to "AFG x1".
   (list `(mu M (nu N (or (box* M) (and (box ,u1 N) ,x1)))))
   (list #t)))
