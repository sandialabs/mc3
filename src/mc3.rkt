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
(require contract-profile
         racket/cmdline
         racket/file
         racket/function
         racket/match
         racket/math
         racket/vector
         profile)


(require (file "foundation.rkt"))
(require (file "options.rkt"))
(require (file "solver.rkt"))
(require (file "util.rkt"))
(require (file "parser/aiger.rkt"))
(require (file "parser/nusmv.rkt"))


(begin
  (require (for-syntax racket/base) racket/runtime-path)
  (define-runtime-path mc3-license-path
    (build-path 'up "LICENSE")))


(define (main)
  (define report-runtime? (make-parameter #f))
  (define profile-performance? (make-parameter #f))
  (define profile-contracts? (make-parameter #f))
  (define path
    (command-line
     #:program "mc3"
     #:once-each
     (("--backward") "do the analysis /backward/ (if possible)" (backward? #t))
     (("--qbf") "use QBF functionality (potentially very slow!)" (use-qbf? #t))
     (("--totality")
      "check whether the transition relation is total"
      (check-totality? #t))
     (("--single-states")
      "decide single states, one at a time"
      (single-states? #t))
     (("--no-expand-successors")
      "do NOT expand successors when deciding diamond formulas"
      (expand-successors? #f))
     (("--profile")
      "profile the performance (use with `racket -l errortrace -t mc3.rkt ...`)"
      (profile-performance? #t))
     (("--time") "report timing information" (report-runtime? #t))
     (("--smtlib") "log the SMT-LIB encodings" (log-smtlib? #t))
     (("--random-seed")
      seed
      "set the seed (a natural number) for pseudorandomness"
      ;; [TODO: make sure that this affects solvers that were already created]
      (smtlib-random-seed (string->number seed)))
     (("--verbosity" "-v")
      verbosity
      "set the verbosity level "
      "(0 = silent; 1 = warning; 2 = todo; 3 = info; 4 = debug)"
      (let ((v (string->number verbosity)))
        (expect (natural? v))
        (when (< v 1) (warning-activated? #f))
        (when (< v 2) (todo-activated? #f))
        (when (< v 2) (info-activated? #f))
        (when (< v 3) (algo-activated? #f))
        (when (< v 4) (debug-activated? #f))))
     (("--profile-contracts")
      "profile the contracts' performance"
      (profile-contracts? #t))
     (("--version")
      "display version and copyright information, then exit"
      (display (file->string mc3-license-path))
      (exit))
     #:args (filename)
     (path->complete-path filename)))
  (when (log-smtlib?)
    (smt.output-smt (path-replace-extension path ".d")))
  (match-define (vector model initial-conditions properties expected)
    (cond
      ((has-extension? path ".rkt")
       (define-values (base name dir?)
         (split-path path))
       (parameterize ((current-directory base))
         (dynamic-require path 'problem)))
      ((or (has-extension? path ".aag")
           (has-extension? path ".aig"))
       (info
        (string-append
         "assuming that the AIGER model has a [forward] total "
         "(but /not/ backward total) transition relation"))
       (transition-relation-proven-forward-total? #t)
       (transition-relation-proven-backward-total? #f)
       (check-totality? #f)
       (info "disabling QBF functionality for AIGER model")
       (use-qbf? #f)
       (vector-append
        (call-with-values (thunk (read-aiger path)) vector)
        (vector (void))))
      ((or (has-extension? path ".smv")
           (has-extension? path ".obm"))
       (vector-append
        (call-with-values (thunk (read-nusmv path)) vector)
        (vector (void))))))
  (define results
    (let ((solve* (curry solve model initial-conditions)))
      (for/list ((p properties))
        (cond ; [TODO: make the corresponding CLI options mutually exclusive]
          ((profile-performance?)
           (profile (solve* p)
                    #:use-errortrace? #t ; [TODO: detect it?]
                    #:order 'self))
          ((profile-contracts?)
           (contract-profile (solve* p)))
          ((report-runtime?)
           (time (solve* p)))
          (else
           (solve* p))))))
  (write-csv (path-replace-extension path ".csv"))
  (write-bounds-dag (path-replace-extension path ""))
  (expect (or (void? expected)
              (equal? results expected))))
(main)
