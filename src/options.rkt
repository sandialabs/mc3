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
         racket/math)


(provide (all-defined-out))


(define/contract backward?
  (parameter/c boolean?)
  (make-parameter #f))


(define/contract single-states?
  (parameter/c boolean?)
  (make-parameter #f))


(define/contract expand-successors?
  (parameter/c boolean?)
  (make-parameter #t))


(define/contract use-qbf?
  (parameter/c boolean?)
  (make-parameter #f))


(define/contract skip-slow-contracts? ; [TODO: CLI]
  (parameter/c boolean?)
  (make-parameter #t))


(define/contract check-totality?
  (parameter/c boolean?)
  (make-parameter #f))


(define/contract log-smtlib?
  (parameter/c boolean?)
  (make-parameter #f))


(define/contract smtlib-random-seed
  (parameter/c natural?)
  (make-parameter 0))
