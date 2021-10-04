#lang racket/base
(require racket/list
         racket/match)


;; Clarke, Grumberg, & Peled (1999), "Model Checking", Chapter 4 (pages 39--49):
;; microwave oven example.


(require (file "../src/ctl-star.rkt"))
(require (file "../src/foundation.rkt"))


(provide problem)
(smt.define-constant start smt.boolean?)
(smt.define-constant close smt.boolean?)
(smt.define-constant heat smt.boolean?)
(smt.define-constant fault smt.boolean?)
(define (state i)
  (match i
    (1 (smt.&& (smt.! start)
               (smt.! close)
               (smt.! heat)
               (smt.! fault)))
    (2 (smt.&& start
               (smt.! close)
               (smt.! heat)
               fault))
    (3 (smt.&& (smt.! start)
               close
               (smt.! heat)
               (smt.! fault)))
    (4 (smt.&& (smt.! start)
               close
               heat
               (smt.! fault)))
    (5 (smt.&& start
               close
               (smt.! heat)
               fault))
    (6 (smt.&& start
               close
               (smt.! heat)
               (smt.! fault)))
    (7 (smt.&& start
               close
               heat
               (smt.! fault)))))
(define state+ (compose sys.next state))
(define transitions
  '((1 (2 3))
    (2 (5))
    (3 (1 6))
    (4 (1 3 4))
    (5 (2 3))
    (6 (7))
    (7 (4))))
(define problem
  (vector
   (sys.lts (list start close heat fault)
            (list)
            (apply smt.|| (map state (range 1 8)))
            #t
            #t
            #t
            (apply smt.&&
                   (for/list ((t transitions))
                     (match-define (list i (list j* ...)) t)
                     (smt.=> (state i)
                             (apply smt.|| (map state+ j*))))))
   #t
   (list
    (ctl*->mmc
     `(AG (if-then (and (not ,close)
                        ,start)
                   (OnEachPath (or (Henceforth (not ,heat))
                                   (Eventually (not ,fault))))))))
   (list #t)))
