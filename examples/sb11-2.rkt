#lang racket/base


;; Somenzi & Bradley (2011), "IC3: Where Monolithic and Incremental Meet",
;; second example.


(require (file "../src/foundation.rkt"))
(require (file "../src/options.rkt"))


(provide problem)
(smt.define-constant x1 smt.boolean?)
(smt.define-constant x2 smt.boolean?)
(smt.define-constant x3 smt.boolean?)
(define problem
  (vector (sys.lts (list x1 x2 x3)
                   (list)
                   #t
                   #t
                   #t
                   #t
                   (smt.&& (smt.|| x1 (smt.! (sys.next x2)))
                           (smt.|| (smt.! x1) (sys.next x2))
                           (smt.|| x2 (smt.! (sys.next x3)))
                           (smt.|| (smt.! x2) (sys.next x3))))
          (smt.! (smt.|| x1 x2 x3))
          (list `(AG ,(smt.! (smt.&& x1 x2 x3))))
          (list #f)))
(backward? #t) ; do /backward/ analysis to mimic IC3
