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
(require racket/function
         racket/list
         racket/match)


(require brag/support)
(require br-parser-tools/lex)


(require (file "../buchi.rkt"))
(require (file "../foundation.rkt"))
(require (file "../util.rkt"))


(require (file "grammar/lbtt.rkt"))


(provide lbtt->ba)


(define (tokenize raw)
  (define lbtt-lexer
    (lexer-src-pos
     (whitespace (token 'WHITESPACE #:skip? #t))
     ((repetition 1 +inf.0 numeric)
      (token 'NATURAL-NUMBER (string->number lexeme)))
     ("-1" (token 'NEGATIVE-ONE lexeme))
     ("t" (token 'TRUE lexeme))
     ((concatenation "\""
                     (repetition 1 +inf.0 (union alphabetic numeric "." "_"))
                     "\"")
      (token 'IDENTIFIER ((lambda (s) ; strip the double quotes
                            (substring s 1 (sub1 (string-length s))))
                          lexeme)))
     ("!" (token 'NOT lexeme))
     ("|" (token 'OR lexeme))
     ("&" (token 'AND lexeme))
     ((eof) (void))))
  (thunk (lbtt-lexer raw)))


(define lbtt-port->datum (compose parse-to-datum tokenize))
(define lbtt-string->datum (compose lbtt-port->datum open-input-string))


(define (translate parse-tree)
  (match-define
    (list 'gba number-of-states number-of-acceptance-sets states ...)
    parse-tree)
  (expect (<= 1 number-of-states))
  (expect (= 1 number-of-acceptance-sets)) ; regular BA, not GBA
  (expect (= number-of-states (length states)))
  (let loop ((remaining states)
             (ba (automaton empty empty empty empty)))
    (cond
      ((empty? remaining)
       (sort-automaton ba))
      (else
       (match-define `(state ,idx
                             (is-initial ,intl)
                             (acceptance-sets ,acc* ...)
                             ,trns* ...)
         (first remaining))
       (loop (rest remaining)
             (automaton
              (cons idx (automaton-states ba))
              (match intl
                (0 (automaton-initial ba))
                (1 (cons idx (automaton-initial ba))))
              (match acc*
                ('() (automaton-accepting ba))
                ('(0) (cons idx (automaton-accepting ba))))
              (append (for/list ((t trns*))
                        (match-define (list 'transition destination label) t)
                        (transition idx destination (->formula label)))
                      (automaton-transitions ba))))))))


(define (->formula x)
  (match x
    ("t" #t)
    ((list 'atom a) (smt.constant a smt.boolean?))
    ((list 'negation y)
     (list 'not (->formula y)))
    ((list 'disjunction y z)
     (list 'or (->formula y) (->formula z)))
    ((list 'conjunction y z)
     (list 'and (->formula y) (->formula z)))))


(define lbtt->ba (compose translate lbtt-string->datum))
