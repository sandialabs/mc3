#lang racket/base
(require racket/vector)


(require (file "../src/options.rkt"))
(require (file "../src/solver.rkt"))
(require (file "../src/parser/aiger.rkt"))


(provide problem)


(define problem
  (vector-append
   (call-with-values (lambda () (read-aiger "kenflashp11.aig"))
                     vector)
   (vector (list #t))))
(backward? #t) ; do /backward/ analysis to mimic IC3
(begin ; defaults and assumptions applied when reading an AIGER model directly
  (transition-relation-proven-forward-total? #t)
  (transition-relation-proven-backward-total? #f)
  (check-totality? #f)
  (use-qbf? #f))
