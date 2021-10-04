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
(require racket/bool
         racket/file
         racket/function
         racket/hash
         racket/list
         racket/match
         racket/port
         racket/set
         racket/string
         racket/system)


(require (file "../foundation.rkt"))
(require (file "../util.rkt"))


(provide read-aiger)


(define (aiger->lines path)
  (define path-string
    (cond ((path? path) (path->string path))
          ((string? path) path)
          (else (error 'aiger->lines "bad path"))))
  (cond
    ((string-suffix? path-string ".aig")
     (string-split
      (with-output-to-string
        (lambda ()
          (system (format "aigtoaig -a ~a" path-string))))
      "\n"))
    ((string-suffix? path-string ".aag")
     (file->lines path-string))
    (else (error 'aiger->lines "bad extension"))))


(define (read-aiger path)
  (define lines (aiger->lines path))
  (define header (string-split (first lines)))
  (define fmt (first header))
  (when (not (string=? fmt "aag"))
    (error 'read-aiger
           (format "unsupported AIGER format: ~s" fmt)))
  (match-define (list M I L O A BCJF ...) (map string->number (rest header)))
  (match-define (list B C J F) (append BCJF (make-list (- 4 (length BCJF)) 0)))
  (expect (= M (+ I L A)))
  ;; Inputs.
  (define-values (input-lines non-I-lines)
    (split-at (rest lines) I))
  (define inputs (map (compose string->number string-trim) input-lines))
  ;; Latches.
  (define-values (latch-lines non-IL-lines)
    (split-at non-I-lines L))
  (define latches
    (for/list ((l latch-lines))
      (map string->number (string-split l))))
  ;; Outputs.
  (define-values (output-lines non-ILO-lines)
    (split-at non-IL-lines O))
  (define outputs (map (compose string->number string-trim) output-lines))
  ;; Bad, Constraints, Justice, Fairness.
  (define-values (bad-lines non-ILOB-lines)
    (split-at non-ILO-lines B))
  (define bads (map (compose string->number string-trim) bad-lines))
  (define-values (constraint-lines non-ILOBC-lines)
    (split-at non-ILOB-lines C))
  (define constraints
    (map (compose string->number string-trim) constraint-lines))
  ;; Justice.
  (expect (<= J 1)) ; [TODO: handle multiple justice properties]
  (define nJ
    (if (= J 0)
        0
        (string->number (string-trim (first non-ILOBC-lines)))))
  (define-values (justice-lines non-ILOBCJ-lines)
    (split-at non-ILOBC-lines (+ J nJ)))
  (define justice
    (if (not (empty? justice-lines))
        (map (compose string->number string-trim)
             (rest justice-lines))
        empty))
  (define-values (fairness-lines non-ILOBCJF-lines)
    (split-at non-ILOBCJ-lines F))
  (define fairness
    (map (compose string->number string-trim) fairness-lines))
  ;; Done.
  ;; And gates.
  (define-values (and-lines non-ILOBCJFA-lines)
    (split-at non-ILOBCJF-lines A))
  (define ands
    (for/hash ((a and-lines))
      (let ((indices (map string->number (string-split a))))
        (values (first indices) (rest indices)))))
  (when (not (empty? non-ILOBCJFA-lines)); [TODO: handle symbols, comments, etc.]
    (void))
  ;; Data validation.[TODO: the dependency graph of the ANDs must be acyclic]
  (define vars (append inputs
                       (map first latches)
                       (hash-keys ands)))
  (expect (false? (check-duplicates vars)))
  (expect (= M (length vars)))
  (expect (andmap (lambda (x) (and (<= 2 x) (even? x))) vars))
  (expect (subset? (map (lambda (x) (if (odd? x) (sub1 x) x)) outputs)
                   (cons 0 vars)))
  (expect (andmap (lambda (x) (<= 2 (length x) 3)) latches))
  ;; State variables.
  (define l:x
    (for/hash ((latch latches)
               (idx (in-naturals 1)))
      (values (first latch) (smt.constant (format "x~a" idx) smt.boolean?))))
  ;; Input variables.
  (define i:u
    (for/hash ((input inputs)
               (idx (in-naturals 1)))
      (values input (smt.constant (format "u~a" idx) smt.boolean?))))
  ;; Transition relation.
  (define idx:var (hash-union l:x i:u))
  (define/memoized (aiger->expression n)
    (cond
      ((odd? n)
       (smt.! (aiger->expression (- n 1))))
      ((zero? n)
       #f)
      ((hash-has-key? idx:var n)
       (hash-ref idx:var n))
      ((hash-has-key? ands n)
       (let ((m* (hash-ref ands n)))
         (apply smt.&& (map aiger->expression m*))))))
  (define x:x+
    (for/hash ((latch latches))
      (values (hash-ref l:x (first latch))
              (aiger->expression (second latch)))))
  ;; Model, initial states, and properties.
  (define treat-inputs-as-states? #f)
  (define model
    (let ((x~ (for/list ((l latches)) (hash-ref l:x (first l))))
          (u~ (for/list ((i inputs)) (hash-ref i:u i))))
      (sys.lts (if treat-inputs-as-states?
                   (append x~ u~)
                   x~)
               (if treat-inputs-as-states?
                   empty
                   u~)
               #t ; state constraints
               #t ; input constraints
               #t ; state-input constraints
               #t ; input-next-state constraints [TODO: there actually are some]
               (apply smt.&&
                      (for/list ((x x~))
                        (smt.<=> (sys.next x)
                                 (hash-ref x:x+ x)))))))
  (define initial-conditions
    (apply
     smt.&&
     (for/list ((l latches)) ; [TODO: reuse `x~` from above]
       (let ((x (hash-ref l:x (first l))))
         (cond
           ((or (= 2 (length l))
                (= 0 (third l)))
            (smt.! x))
           ((= 1 (third l))
            x)
           ((= (first l) (third l))
            #t)
           (else
            (error 'read-aiger (format "bad latch: ~a" l))))))))
  (define properties ; [TODO: "constraints"]
    (cond
      ((and (= O 0) (= B 0)
            (= J 1) (>= nJ 1))
       ;; One or more "justice" and "fairness" properties (lumped together),
       ;; [perhaps] along with an "invariant" property: A!(Gi && &&_J(GFj))
       ;; (equivalent to A(F!i || ||_J(FG!j))) asserts that /no/ path exists
       ;; along which i is perpetually true and /each/ j is true infintely
       ;; often; hence, a counterexample demonstrates an "invariant fair/just"
       ;; path.  The following is a by-hand translation of the LTL property to
       ;; MMC.[TODO: explain]
       (define justice-fairness (append justice fairness))
       (let ((!i (smt.! (apply smt.&& (map aiger->expression constraints))))
             (!jj (map (compose smt.! aiger->expression)
                       justice-fairness))
             (NN (map (compose string->symbol (curry format "N~a") add1)
                      (range (length justice-fairness)))))
         `((mu M (or ,@(for/list ((!j !jj)
                                  (N NN))
                         `(nu ,N (or ,!i
                                     (and (or ,!j (box* M))
                                          (box* ,N))))))))))
      ;; A single "bad state" property: "SAT" means the bad state is reachable.
      ((and (= O 0)
            (> B 0))
       (for/list ((b bads))
         `(AG ,(smt.! (aiger->expression b)))))
      ;; A single output: assume that it represents a "bad" property.
      ((and (= O 1))
       (for/list ((o outputs))
         `(AG ,(smt.! (aiger->expression o)))))
      (else
       (error 'read-aiger
              (format "unsupported property: ~a"
                      (hash 'O O 'B B 'C C 'J J 'nJ nJ 'F F))))))
  (values model initial-conditions properties))
