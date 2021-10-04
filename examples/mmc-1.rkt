#lang racket/base


(require (file "../src/foundation.rkt"))


(provide problem)
(smt.define-constant p smt.boolean?)
(define problem
  (vector (sys.lts (list p)
                   (list)
                   #t
                   #t
                   #t
                   #t
                   (smt.<=> p (sys.next (smt.! p))))
          p
          (list `(nu Z (and ,p (box* (box* Z)))))
          (list #t)))
