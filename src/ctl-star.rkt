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
         racket/hash
         racket/match
         racket/set
         racket/contract
         racket/format
         racket/list
         racket/port
         racket/pretty
         racket/string
         racket/system)


(require (file "buchi.rkt"))
(require (file "foundation.rkt"))
(require (prefix-in mmc. (file "mmc.rkt")))
(require (file "util.rkt"))
(require (file "parser/lbtt.rkt"))


(provide ctl*->mmc
         apply-path-assumption)


(define state-formula/c
  (or/c mmc.proposition?
        (list/c 'not (recursive-contract state-formula/c #:flat))
        (cons/c 'or (listof (recursive-contract state-formula/c #:flat)))
        (list/c 'OnSomePath (recursive-contract path-formula/c #:flat))))
(define path-formula/c
  (or/c state-formula/c
        (list/c 'not (recursive-contract path-formula/c #:flat))
        (cons/c 'or (listof (recursive-contract path-formula/c #:flat)))
        (list/c 'Subsequently (recursive-contract path-formula/c #:flat))
        (list/c 'Until
                (recursive-contract path-formula/c #:flat)
                (recursive-contract path-formula/c #:flat))))


(define (expand-formula f)
  ;; Expand a CTL* formula in terms of a core set of operators.
  (match f
    ;; Abbreviations.
    ((list 'if-then g h)
     (expand-formula
      `(or (not ,g) ,h)))
    ((list 'Eventually g)
     (expand-formula
      (list 'Until #t g)))
    ((list 'Henceforth g)
     (expand-formula
      (list 'Release #f g)))
    ((list 'EF g)
     (expand-formula
      `(OnSomePath (Eventually ,g))))
    ((list 'AF g)
     (expand-formula
      `(OnEachPath (Eventually ,g))))
    ((list 'AG g)
     (expand-formula
      `(OnEachPath (Henceforth ,g))))
    ;; Dual.
    ((list 'and g* ...)
     (expand-formula
      `(not (or ,@(map (curry list 'not) g*)))))
    ((list 'Release g h)
     (expand-formula
      `(not (Until (not ,g) (not ,h)))))
    ((list 'OnEachPath g)
     (expand-formula
      `(not (OnSomePath (not ,g)))))
    ;; Core.
    ((? mmc.proposition?)
     f)
    ((list (? (curry set-member? (set 'not 'Subsequently 'OnSomePath)) unop) g)
     (list unop (expand-formula g)))
    ((list 'Until g h)
     (list 'Until (expand-formula g) (expand-formula h)))
    ((list 'or g* ...)
     (cons 'or (map expand-formula g*)))))


(define (apply-path-assumption ~p ~f)
  ;; Restrict the CTL* formula `~f` to paths along which `~p` holds.
  (define (worker p f)
    (match f
      ((? mmc.proposition?) f)
      ((list 'not g)
       (list 'not (worker p g)))
      ((list 'or g* ...)
       (cons 'or (map (curry worker p) g*)))
      ((list 'Subsequently g)
       (list 'Subsequently (worker p g)))
      ((list 'Until g h)
       (list 'Until (worker p g) (worker p h)))
      ((list 'OnSomePath g)
       `(OnSomePath (and ,p ,(worker p g))))))
  (worker (expand-formula ~p) (expand-formula ~f)))


(define (ctl*->mmc f)
  ;; Convert a CTL* formula to MMC.
  (info "converting CTL* formula to MMC: ~a" f)
  (define atomic-propositions
    (remove-duplicates
     (apply append (map smt.symbolics (filter mmc.proposition? (flatten f))))))
  (define (placeholder-safe? v)
    (match-define (smt.constant name smt.boolean?) v)
    (not (regexp-match? "__placeholder_[0-9]+__" name)))
  (expect (andmap placeholder-safe? atomic-propositions))
  (define/contract (worker f)
    (-> state-formula/c mmc.closed-formula/c)
    (match f
      ((? mmc.proposition?)
       f)
      ((list 'not g)
       (list 'not (worker g)))
      ((list 'or g* ...)
       (cons 'or (map worker g*)))
      ((list 'OnSomePath g)
       (define-values (g~ placeholders)
         (hide-state-subformulas g))
       (expect (path-formula/c g~))
       (info "path formula: ~a" g~)
       (define g~~
         (let ()
           (define s (path->spot g~))
           (info "path formula in Spot syntax: ~a" s)
           (define l (spot->lbtt s))
           (info "Büchi automaton in LBTT syntax:~n~a" (indent-lines l))
           (define b (lbtt->ba l))
           (info "Büchi automaton:~n~a"
                  (indent-lines (pretty-format #:mode 'display b)))
           (define m (existential-ba->mmc b))
           (info "MMC: ~a" (compress-variable-indices m))
           m))
       (define replacements
         (for/hash ((p (hash-keys placeholders)))
           (values p (worker (hash-ref placeholders p)))))
       (tree-replace* replacements g~~))))
  (define f~ (expand-formula f))
  (info "rewritten CTL* formula: ~a" f~)
  (compress-variable-indices (worker f~)))


(define (hide-state-subformulas f)
  ;; Replace each state subformula of the given path formula with a placeholder.
  ;;
  ;; The point is to reveal the "relevant" structure of the path formula, which
  ;; does not depend on a nested path formula that is preceded by a path
  ;; quantifier.
  (match f
    ((? mmc.proposition?)
     (values f (hash)))
    ((list 'not g)
     (define-values (g~ placeholders) (hide-state-subformulas g))
     (values (list 'not g~)
             placeholders))
    ((list 'or g* ...)
     (let loop ((remaining g*)
                (processed empty)
                (placeholders (hash)))
       (cond
         ((empty? remaining)
          (values (cons 'or (reverse processed))
                  placeholders))
         (else
          (define g (first remaining))
          (define-values (g~ p) (hide-state-subformulas g))
          (loop (rest remaining)
                (cons g~ processed)
                (hash-union p placeholders))))))
    ((list 'Subsequently g)
     (define-values (g~ placeholders) (hide-state-subformulas g))
     (values (list 'Subsequently g~)
             placeholders))
    ((list 'Until g h)
     (define-values (g~ pg) (hide-state-subformulas g))
     (define-values (h~ ph) (hide-state-subformulas h))
     (values (list 'Until g~ h~)
             (hash-union pg ph)))
    ((list 'OnSomePath _)
     (define f~
       (next-placeholder))
     (values f~ (hash f~ f)))))
(define next-placeholder
  (let ((i 0))
    (lambda ()
      (set! i (add1 i))
      (smt.constant (format "__placeholder_~a__" i) smt.boolean?))))


(define/contract (path->spot p)
  (-> path-formula/c string?)
  ;; Convert a path formula to Spot's LTL syntax.
  (define/contract (parens s) (-> string? string?) (string-append "(" s ")"))
  (define/contract (unary op arg)
    (-> string? path-formula/c string?)
    (parens (string-append op " " (path->spot arg))))
  (define/contract (binary op a b)
    (-> string? path-formula/c path-formula/c string?)
    (parens (string-append (path->spot a) " " op " " (path->spot b))))
  (define/contract (variadic op arg* base)
    (-> string? (listof path-formula/c) path-formula/c string?)
    (parens
     (string-join (if (empty? arg*) (list base) (map path->spot arg*))
                  (string-append " " op " "))))
  (match p
    (#f "0")
    (#t "1")
    ((? (or/c mmc.atom? symbol?))
     (~a p))
    ((or (list 'not q)
         (smt.expression (== smt.!) q))
     (unary "!" q))
    ((or (list 'or q* ...)
         (smt.expression (== smt.||) q* ...))
     (variadic "||" q* #f))
    ((smt.expression (== smt.&&) q* ...)
     (variadic "&&" q* #t))
    ((smt.expression (== smt.<=>) q r)
     (binary "<->" q r))
    ((list 'Subsequently q)
     (unary "X" q))
    ((list 'Until q r)
     (binary "U" q r))))


(define/contract (spot->lbtt s)
  (-> string? string?)
  ;; Convert an LTL formula (Spot syntax) to a Büchi automaton (LBTT syntax).
  (with-output-to-string
    (thunk
     (system
      (format "ltl2tgba '~a' --lbtt --ba" s)))))


(module* test #f
  (smt.define-constant a smt.boolean?)
  (smt.define-constant b smt.boolean?)
  (define a-until-b
    `(Until ,a ,b))
  (pretty-display a-until-b)
  (expect (path-formula/c a-until-b))
  (define exists-a-until-b
    `(OnSomePath ,a-until-b))
  (pretty-display exists-a-until-b)
  (expect (state-formula/c exists-a-until-b))
  (pretty-display
   (ctl*->mmc `(OnSomePath (or ,exists-a-until-b
                               ,exists-a-until-b))))
  (void))
