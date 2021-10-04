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
(require (for-syntax racket/base)
         racket/contract
         racket/function
         racket/list
         racket/match
         racket/math
         racket/pretty
         racket/set
         racket/string)


(provide (except-out (all-defined-out) _log))


;;;;;;;;;;;
; Logging ;
;;;;;;;;;;;


(define (_log port label format-string . vals)
  (let ((label (string-upcase (symbol->string label))))
    (cond
      ((empty? vals)
       (displayln (format "[~a: ~a]" label format-string)
                  port))
      (else
       (displayln (string-append "[" label ": "
                                 (apply format (cons format-string vals))
                                 "]")
                  port)))))
(define-syntax (define-logging-macro stx)
  (syntax-case stx ()
    ((_ name port)
     (with-syntax ((activated?
                    (datum->syntax
                     #'name
                     (string->symbol
                      (format "~a-activated?" (syntax->datum #'name))))))
       #'(begin
           (define/contract activated? (parameter/c boolean?)
             (make-parameter #t))
           (define-syntax-rule (name format-string vals (... ...))
             (when (activated?)
               (apply _log
                      (append (list port (syntax->datum #'name) format-string)
                              (list vals (... ...)))))))))
    ((_ name)
     #'(define-logging-macro name (current-output-port)))))
(define-logging-macro todo)
(define-logging-macro info)
(define-logging-macro algo)
(define-logging-macro debug)
(define-logging-macro warning)


(define-syntax-rule (showme x)
  (let ((x-rslt x))
    (displayln (format "~a: ~a"
                       (pretty-format #:mode 'display (quote x))
                       (pretty-format #:mode 'display x-rslt)))
    x-rslt))


(define/contract (indent-lines s #:columns (columns 1))
  (->* (string?) (#:columns natural?) string?)
  (string-join (map (curry string-append (make-string columns #\space))
                    (string-split s "\n"))
               "\n"))


;;;;;;;;;;;;;;;;
; Expectations ;
;;;;;;;;;;;;;;;;


(define-syntax expect-error
  (syntax-rules ()
    ((_ x)
     (with-handlers
       ((exn:fail?
         (lambda (err)
           (printf
            "{~nError during evaluation.~nExpression:~n~a~nError:~n~a~n}~n"
            (quote x)
            err))))
       x))
    ((_ x #:quiet)
     (with-handlers
       ((exn:fail?
         (lambda (_)
           (printf
            "{Error during evaluation of ~a.}~n"
            (quote x)))))
       x))))


(struct exn:fail:expectation exn:fail (source-location)
  #:transparent
  #:property prop:exn:srclocs
  (lambda (x)
    (match x
      ((exn:fail:expectation _ _ sl)
       (list sl)))))
(define-syntax-rule (expect x)
  ;; [TODO: report better source location info]
  (when (not x)
    (raise (exn:fail:expectation
            (format "expectation failed: ~a" (quote x))
            (current-continuation-marks)
            (let ((x~ (syntax x)))
              (srcloc (syntax-source x~)
                      (syntax-line x~)
                      (syntax-column x~)
                      (syntax-position x~)
                      (syntax-span x~)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;
; Nested Lists as Trees ;
;;;;;;;;;;;;;;;;;;;;;;;;;


(define (tree-replace* x:x~ t)
  ;; Replace each of `x:x~`'s keys in `t` with its associated value.
  (define/memoized (aux/tree-replace* t)
    (cond
      ((hash-has-key? x:x~ t)
       ;; [TODO: is the "recursive" replacement intended? (does it even work?)]
       (aux/tree-replace* (hash-ref x:x~ t)))
      ((list? t)
       (map aux/tree-replace* t))
      (else t)))
  (aux/tree-replace* t))


(define (tree-substitute x~ x t)
  (tree-replace* (hash x x~) t))


;;;;;;;;;;;;;;;;;
; Lists as Sets ;
;;;;;;;;;;;;;;;;;


(define (listset-intersect . l*)
  (set->list (apply set-intersect (map list->set l*))))


(define (listset-union . l*)
  (set->list (apply set-union (map list->set l*))))


(define (listset=? . l*)
  (apply set=? (map list->set l*)))


;;;;;;;;;;;;;;;;;
; Miscellaneous ;
;;;;;;;;;;;;;;;;;


(struct k-v (k v) #:transparent)
(define (hash->k-v h)
  (define (k<? a b)
    (string<? (format "~a" a)
              (format "~a" b)))
  (for/list ((k (sort (hash-keys h) k<?)))
    (k-v k (hash-ref h k))))


(define (hash-restrict h keys)
  (for/hash ((k keys))
    (values k (hash-ref h k))))


(define (has-extension? p .x)
  (string-suffix? (path->string p) .x))


(define-syntax-rule (define/memoized (f x) body* ...)
  ;; Define a "memoized" version of the single-argument function `f` that stores
  ;; each computed result in a cache for later lookup.
  (define f
    (let ((f~ ; the original/unmemoized function
           (lambda (x) body* ...))
          (cache ; the result cache (uses `equal?` for comparisons)
           (make-hash)))
      (lambda (x~)
        ;; Try to get the result from the cache; if it isn't yet in the cache,
        ;; then compute the result, cache it, and return it.
        (hash-ref cache x~ (lambda ()
                             (let ((f-of-x (f~ x~)))
                               (hash-set! cache x~ f-of-x)
                               f-of-x)))))))


(module* test #f

  (define (slowly n)
    (sleep n)
    n)
  (debug (slowly 0.5))
  (parameterize ((debug-activated? #f))
    (debug (slowly 100)))
  (debug (slowly 1))

  (void))
