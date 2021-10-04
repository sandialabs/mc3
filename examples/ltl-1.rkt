#lang racket/base


(require (file "../src/foundation.rkt"))


(provide problem)
(smt.define-constant a smt.boolean?)
(smt.define-constant b smt.boolean?)
(smt.define-constant c smt.boolean?)
(smt.define-constant p smt.boolean?)
(define problem
  (vector (sys.lts (list a b c p)
                   (list)
                   (smt.&&
                    ; "one hot"
                    (smt.&& (smt.|| a b c)
                            (smt.! (smt.&& a b))
                            (smt.! (smt.&& a c))
                            (smt.! (smt.&& b c)))
                    ; atomic proposition
                    (smt.<=> p (smt.|| a c)))
                   #t
                   #t
                   #t
                   (smt.&&
                    ; a -> a, a -> b
                    (smt.=> a
                            (sys.next (smt.|| a b)))
                    ; b -> c
                    (smt.=> b
                            (sys.next c))
                    ; c -> c
                    (smt.=> c
                            (sys.next c))))
          #t
          ;; AFGp.
          (list `(mu M (nu N (or (box* M) (and (box* N) ,p)))))
          (list #t)))
