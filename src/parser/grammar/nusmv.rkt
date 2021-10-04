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


#lang brag


;;; This is a grammar for a fragment of NuSMV's modeling language, intended for
;;; use with the output of `NuSMV -obm`, i.e., a flat[tened] Boolean[ized]
;;; model.


;; Expect a single main module.
module: /MODULE identifier statement+

;; Everything is a statement; some of them can be grouped in blocks.
@statement: constants | declaration | definition | constraint | assumption | assertion

;; Symbolic constant values.
constants: /CONSTANTS identifier (/"," identifier)* /SEMICOLON

;; Declarations and definitions; each one ends with a semicolon.
declaration: (VAR | IVAR) (identifier /COLON BOOLEAN /SEMICOLON)+ ; Boolean only
definition: DEFINE (identifier /COLEQ term /SEMICOLON)+

;; Constraints; apparently the final one in a block does not have to end with a
;; semicolon...
constraint: (INIT | INVAR | TRANS) term (/SEMICOLON term)* /SEMICOLON?

;; Assumptions.
assumption: (FAIRNESS | JUSTICE) term /SEMICOLON?
            | COMPASSION /"(" term /"," term /")" /SEMICOLON?

;; Assertions; apparently the semicolon is optional...
assertion: (CTLSPEC | LTLSPEC) /[NAME identifier COLEQ] term /SEMICOLON?

;; Terms; no distinction is made between current/input/next variables, nor
;; between temporal/Boolean logic, and operator precedence isn't addressed.
@term: literal | identifier
       | parens
       | next
       | unop
       | binop
       | if-then-else
       | case
literal: LITERAL
identifier: IDENTIFIER
@parens: /"(" term /")"
next: /NEXT /"(" term /")"
unop: UNOP term
binop: term BINOP term
if-then-else: term /QUESTION-MARK term /COLON term
case: /CASE case-pair+ /ESAC
/case-pair: (term /COLON term /SEMICOLON)
