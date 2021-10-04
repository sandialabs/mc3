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
         racket/function
         racket/list
         racket/match
         racket/math
         racket/set)


(require (file "foundation.rkt"))
(require (file "mmc.rkt"))
(require (file "util.rkt"))


(provide (all-defined-out))


(struct automaton (states initial accepting transitions) #:transparent)
(struct transition (source destination label) #:transparent)


(define/contract (sort-automaton a)
  (-> automaton? automaton?)
  (define (transition<? t1 t2)
    (match-define (transition s1 d1 _) t1)
    (match-define (transition s2 d2 _) t2)
    (or (< s1 s2)
        (and (= s1 s2)
             (< d1 d2))))
  (automaton (sort (automaton-states a) <)
             (sort (automaton-initial a) <)
             (sort (automaton-accepting a) <)
             (sort (automaton-transitions a) transition<?)))


(define/contract (existential-ba->mmc a)
  (-> automaton? any/c)
  ;; Apply the translation scheme from
  ;; https://doi.org/10.1016/0304-3975(94)90269-0 (Dam, 1994), Section 9 --- the
  ;; one for "ECTL*", not the tableau-based CTL* translation.
  (define/contract (Dam-1994-tr_e i history i*)
    (-> natural? (hash/c natural? symbol?) natural? closed-formula/c)
    (define (Omega x history~)
      (match x
        (#t #t)
        ((? smt.boolean?)
         x)
        ((list 'not y)
         (list 'not (Omega y history~)))
        ((list (? (curry set-member? (set 'or 'and)) or/and) y* ...)
         (cons or/and (map (curryr Omega history~) y*)))
        ((list 'diamond* i)
         (list 'diamond* (Dam-1994-tr_e i history~ i*)))))
    (define (outgoing i)
      (define transitions (filter (compose (curry = i) transition-source)
                                  (automaton-transitions a)))
      (cons 'or (for/list ((t transitions))
                  (list 'and
                        (transition-label t)
                        (list 'diamond* (transition-destination t))))))
    (cond
      ((hash-has-key? history i)
       (hash-ref history i))
      (else
       (define Zi (gensym "Z"))
       (if (= i i*)
           `(nu ,Zi ,(Omega (outgoing i) (hash i Zi)))
           `(mu ,Zi ,(Omega (outgoing i) (hash-set history i Zi)))))))
  (todo "check bound variables and atomic propositions for name clashes")
  (cons 'or (map (curry Dam-1994-tr_e 0 (hash))
                 (automaton-accepting a))))


(define (compress-variable-indices f)
  ;; "Compress" the indices of bound variables so that the indices are
  ;; sequential, starting from 0.
  (define (bound-variable? x)
    (and (symbol? x)
         (regexp-match? "Z[0-9]+" (symbol->string x))))
  (define (index x)
    (string->number (substring (symbol->string x) 1)))
  (define Z*
    (sort (remove-duplicates (filter bound-variable? (flatten f)))
          <
          #:key index))
  (define Z:Z~
    (for/hash ((Z Z*)
               (i (in-naturals)))
      (values Z (string->symbol (format "Z~a" i)))))
  (tree-replace* Z:Z~ f))
