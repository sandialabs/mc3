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
         racket/dict
         racket/function
         racket/hash
         racket/list
         racket/match)
(require pkg/path)


(require
 (only-in rosette/base/core/reporter
          current-reporter)
 (prefix-in base/
            rosette/solver/smt/base-solver)
 rosette/solver/smt/cmd
 rosette/solver/smt/env
 rosette/solver/smt/server
 (only-in rosette/solver/smt/smtlib2
          reset set-option check-sat push)
 rosette/solver/solution
 rosette/solver/solver)


(provide (rename-out (make-z3-names z3-names)) z3-names?)


(define rosette-z3-path
  (let ((rosette-installation (hash-ref (read-pkgs-db 'user) "rosette")))
    (match-define (list 'link rosette-link)
      (pkg-info-orig-pkg rosette-installation))
    (simplify-path
     (path->complete-path
      (build-path (get-pkgs-dir 'user) rosette-link ".." "bin" "z3")))))
(define z3-opts '("-smt2" "-in"))


(define default-options
  (hash ':produce-unsat-cores 'true
        ':auto-config 'false
        ':smt.mbqi 'false))


(define (make-z3-names (solver #f)
                       #:options (options (hash))
                       #:logic (logic #f)
                       #:path (path #f))
  (define config
    (cond
      ((z3-names? solver)
       (base/solver-config solver))
      (else
       (base/config (hash-union default-options
                                options
                                #:combine (lambda (d o) o))
                    (base/find-solver "z3" rosette-z3-path path)
                    logic))))
  (z3-names
   (server (base/config-path config) z3-opts (base/make-send-options config))
   config
   '() '() '() (env) '()
   (list (list))))


(struct z3-names base/solver (encoded-assertions)
  ;; Name everything up front to avoid clearing/reasserting everything (with
  ;; names) each time an UNSAT core is needed.  The extra member
  ;; `encoded-assertions` tracks the already-encoded assertions (organized by
  ;; push/pop "frame") to avoid renaming the same thing, which Z3 wouldn't like.
  #:mutable
  #:property prop:solver-constructor make-z3-names
  #:methods gen:custom-write
  ((define (write-proc self port mode) (fprintf port "#<z3-names>")))
  #:methods gen:solver
  ((define (solver-features self)
     '(qf_uf unsat-cores))

   (define (solver-options self)
     (base/solver-options self))

   (define (solver-assert self bools)
     (base/solver-assert self bools))

   (define (solver-clear self)
     (base/solver-clear-stacks! self)
     (base/solver-clear-env! self)
     (set-z3-names-encoded-assertions! self (list (list)))
     (server-write (base/solver-server self) (reset))
     (server-initialize (base/solver-server self)))

   (define (solver-shutdown self)
     (set-z3-names-encoded-assertions! self (list (list)))
     (base/solver-shutdown self))

   (define (solver-push self)
     ;; Encode and assert the currently-"buffered" assertions, record the fact
     ;; that they were encoded, clear the buffers, and open a new frame.
     (match-define (z3-names server _ assertions _ _ env level ea) self)
     (let ((assertions (remove-duplicates assertions)))
       (server-write
        server
        (begin
          ((current-reporter) 'encode-start)
          (encode-for-proof env (remove* (flatten ea) ; don't "rename" things
                                         assertions))
          (set-z3-names-encoded-assertions!
           self
           (cons
            (list) ; the new frame (empty to begin with)
            (list-update ea 0 (curry append assertions))))
          ((current-reporter) 'encode-finish)
          (push)))
       (base/solver-clear-stacks! self)
       (base/set-solver-level! self (cons (dict-count env) level))))

   (define (solver-pop self (k 1))
     ;; Pop a frame, and record the fact that the assertions that were encoded
     ;; in that frame are no longer encoded.
     (base/solver-pop self k)
     (set-z3-names-encoded-assertions!
      self
      (drop (z3-names-encoded-assertions self) k)))

   (define (solver-check self (read-solution base/read-solution))
     ;; As in `solver-push`, name and track encoded assertions.
     (match-define (z3-names server _ assertions _ _ env _ ea) self)
     (let ((assertions (remove-duplicates assertions)))
       (cond
         ((ormap false? assertions)
          (unsat))
         (else
          (server-write
           server
           (begin
             ((current-reporter) 'encode-start)
             (encode-for-proof env (remove* (flatten ea) assertions))
             (set-z3-names-encoded-assertions!
              self
              (list-update ea 0 (curry append assertions)))
             ((current-reporter) 'encode-finish)
             (check-sat)))
          ((current-reporter) 'solve-start)
          (base/solver-clear-stacks! self)
          (define ret (read-solution server env))
          ((current-reporter) 'solve-finish (sat? ret))
          ret))))

   (define (solver-debug self)
     (solver-check self (curry base/read-solution #:unsat-core? #t)))))


(module* test #f
  (define slvr (make-z3-names))
  rosette-z3-path
  (base/config-path (base/solver-config slvr))
  (require rosette)
  (solver-push slvr)
  (define-symbolic x boolean?)
  (define-symbolic y boolean?)
  (solver-assert slvr (list (<=> x y)))
  (solver-check slvr)
  (solver-pop slvr)
  (void))
