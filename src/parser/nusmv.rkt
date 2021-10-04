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
(require racket/file
         racket/format
         racket/function
         racket/list
         racket/match
         racket/set
         racket/system)


(require brag/support)
(require br-parser-tools/lex)


(require (file "../foundation.rkt"))
(require (file "../ctl-star.rkt"))
(require (file "../util.rkt"))


(require (file "grammar/nusmv.rkt"))


(provide read-nusmv)


(define (tokenize raw)
  (define nusmv-lexer
    (lexer-src-pos
     ((from/stop-before "--" "\n") (token 'COMMENT #:skip? #t))
     (whitespace (token 'WHITESPACE #:skip? #t))
     ("boolean" (token 'BOOLEAN lexeme))
     ("next" (token 'NEXT lexeme))
     ("case" (token 'CASE lexeme))
     ("esac" (token 'ESAC lexeme))
     ((union "X" "EX" "AX"
             "F" "EF" "AF"
             "G" "EG" "AG")
      (token 'UNOP lexeme))
     ((union "<->" "->"
             (char-set "|&")
             "U")
      (token 'BINOP lexeme))
     ("MODULE" (token 'MODULE lexeme))
     ("CONSTANTS" (token 'CONSTANTS lexeme))
     ("VAR" (token 'VAR lexeme))
     ("IVAR" (token 'IVAR lexeme))
     ("INIT" (token 'INIT lexeme))
     ("INVAR" (token 'INVAR lexeme))
     ("TRANS" (token 'TRANS lexeme))
     ("ASSIGN" (token 'ASSIGN lexeme))
     ("DEFINE" (token 'DEFINE lexeme))
     ("FAIRNESS" (token 'FAIRNESS lexeme))
     ("JUSTICE" (token 'JUSTICE lexeme))
     ("COMPASSION" (token 'COMPASSION lexeme))
     ("CTLSPEC" (token 'CTLSPEC lexeme))
     ("LTLSPEC" (token 'LTLSPEC lexeme))
     ("NAME" (token 'NAME lexeme))
     ((union "FALSE" "TRUE"
             (repetition 1 +inf.0 numeric))
      (token 'LITERAL lexeme))
     ((concatenation (union alphabetic "_")
                     (repetition 0 +inf.0 (union alphabetic numeric "." "_")))
      (token 'IDENTIFIER lexeme))
     ((union "(" ")" ",") lexeme) ; [MAYBE: use `token`]
     ((char-set "!")
      (token 'UNOP lexeme))
     (";" (token 'SEMICOLON lexeme))
     ("?" (token 'QUESTION-MARK lexeme))
     (":=" (token 'COLEQ lexeme))
     (":" (token 'COLON lexeme))
     ((eof) (void))))
  (thunk (nusmv-lexer raw)))


(define nusmv->datum
  (compose parse-to-datum tokenize))


(define (translate parse-tree)
  ;; Split up blocks.
  (define pt~ (split-blocks parse-tree))
  ;; Inline the definitions.
  (define pt~~ (inline-definitions pt~))
  ;; Convert `case`s to chained `if-then-else`s.
  (define ast (case->ite pt~~))
  ;;
  (ast->model+init+props ast))


(define (inline-definitions x)
  (define-values (dfn-part non-dfn-part)
    (partition (lambda (y)
                 (and (list? y)
                      (eq? 'definition (first y))))
               x))
  (define env (for/hash ((d dfn-part)) (apply values (drop d 2))))
  (tree-replace* env non-dfn-part))


(define (case->ite x)
  (match x
    ((list 'case (list _ result))
     ;; Assume that it was exhaustive; go directly to the result.
     (case->ite result))
    ((list 'case (list condition1 result1) other-pair* ...)
     (list 'if-then-else
           (case->ite condition1)
           (case->ite result1)
           (case->ite (cons 'case other-pair*))))
    ((list 'case y* ...)
     (error 'case->ite "invalid `case` syntax: ~a" x))
    ((? list?) (map case->ite x))
    (_ x)))


(define (split-blocks x)
  (define block-arity (hash 'declaration 2
                            'definition 2
                            'constraint 1
                            'assertion 1))
  (define (proceed y)
    (cons (first y) (split-blocks (rest y))))
  (cond
    ((empty? x) x)
    ((and (list? x)
          (list? (first x))
          (hash-has-key? block-arity (first (first x))))
     (define desired-size (+ 2 (hash-ref block-arity (first (first x)))))
     (if (< desired-size (length (first x)))
         (let-values (((block-head block-tail) (split-at (first x)
                                                         desired-size)))
           (cons block-head
                 (split-blocks (cons (append (take block-head 2)
                                             block-tail)
                                     (rest x)))))
         (proceed x)))
    (else
     (proceed x))))


(define (ast->model+init+props ast)
  (define statements (drop ast 2))
  ;; Declarations.
  (define type-map (hash "boolean" smt.boolean?))
  (define (declaration? x) (eq? 'declaration (first x)))
  (define (decls->vars decls)
    (for/list ((d decls))
      (smt.constant (second (third d))
                    (hash-ref type-map (fourth d)))))
  (define-values (declarations non-declarations)
    (partition declaration? statements))
  (define-values (sv-decls non-sv-decls)
    (partition (lambda (x) (string=? "VAR" (second x)))
               declarations))
  (define state-variables (decls->vars sv-decls))
  (define-values (iv-decls other-decls)
    (partition (lambda (x) (string=? "IVAR" (second x)))
               non-sv-decls))
  (define input-variables (decls->vars iv-decls))
  (when (not (empty? other-decls))
    (error 'ast->model+init+props "unrecognized declarations: ~a" other-decls))
  (define variables (append state-variables input-variables))
  (define translate-term~ (curryr translate-term variables))
  ;; Constraints.
  (define-values (constraints non-constraints)
    (partition (lambda (x) (eq? 'constraint (first x)))
               non-declarations))


  (define-values (invar-cnstrs non-invar-cnstrs)
    (partition (lambda (x) (string=? "INVAR" (second x)))
               constraints))
  (define state-constraints
    (apply smt.&& (map (compose translate-term~ third) invar-cnstrs)))


  (define-values (trans-cnstrs non-trans-non-invar-cnstrs)
    (partition (lambda (x) (string=? "TRANS" (second x)))
               non-invar-cnstrs))
  (define transition-constraints
    (apply smt.&& (map (compose translate-term~ third) trans-cnstrs)))
  ;; Model.
  (define model (sys.lts state-variables
                         input-variables
                         state-constraints
                         #t ; input constraints
                         #t ; state-input constraints
                         #t ; input-next-state constraints
                         transition-constraints))
  ;; Initial conditions.
  (define-values (init-cnstrs non-init-non-trans-non-invar-cnstrs)
    (partition (lambda (x) (string=? "INIT" (second x)))
               non-trans-non-invar-cnstrs))
  (define initial-conditions
    (apply smt.&& (map (compose translate-term~ third) init-cnstrs)))
  (when (not (empty? non-init-non-trans-non-invar-cnstrs))
    (error 'ast->model+init+props
           "unrecognized constraints: ~a"
           non-init-non-trans-non-invar-cnstrs))
  ;; Assumptions.
  (define-values (assumptions non-assumptions)
    (partition (lambda (x) (eq? 'assumption (first x)))
               non-constraints))
  (define fairness
    (let ((conjuncts
           (for/list ((a assumptions))
             (cond
               ((set-member? (set "FAIRNESS" "JUSTICE") (second a))
                (let ((j (translate-term~ (third a))))
                  `(Henceforth (Eventually ,j))))
               ((string=? (second a) "COMPASSION")
                (let ((p (translate-term~ (third a)))
                      (q (translate-term~ (fourth a))))
                  `(if-then (Henceforth (Eventually ,p))
                            (Henceforth (Eventually ,q)))))
               ((set-member? (set "FAIRNESS" "JUSTICE") (second a))
                (define j (translate-term~ (third a)))
                `(Henceforth (Eventually ,j)))
               (else
                (error
                 'ast->model+init+props
                 (format "unrecognized assumption type: ~a" (second a))))))))
      (if (empty? conjuncts) #t (cons 'and conjuncts))))
  ;; Assertions.
  (define-values (assertions non-assertions)
    (partition (lambda (x) (eq? 'assertion (first x)))
               non-assumptions))
  (define properties
    (for/list ((a assertions))
      (define p (translate-term~ (third a)))
      (cond
        ((string=? (second a) "LTLSPEC")
         (let ((p~ (if (eq? #t fairness) p `(if-then ,fairness ,p))))
           (ctl*->mmc `(OnEachPath ,p~))))
        ((string=? (second a) "CTLSPEC")
         (if (eq? #t fairness)
             p
             (ctl*->mmc (apply-path-assumption fairness p))))
        (else
         (error
          'ast->model+init+props
          (format "unrecognized assertion type: ~a" (second a)))))))
  ;; Constants (just ignore them; they should only appear in non-Boolean terms).
  (define-values (constants other-statements)
    (partition (lambda (x) (eq? 'constants (first x)))
               non-assertions))
  ;; Done.
  (when (not (empty? other-statements))
    (error 'ast->model+init+props
           "unrecognized statements: ~a"
           other-statements))
  (values model initial-conditions properties))


(define (translate-term t ctx)
  (match t
    ((list 'literal "FALSE") #f)
    ((list 'literal "TRUE") #t)
    ((list 'identifier u)
     (let ((var (findf (lambda (x) (string=? u (format "~a" x)))
                       ctx)))
       (when (eq? #f var)
         (error 'translate-term "unknown identifier: ~a" t))
       var))
    ((list 'next u)
     (sys.next (translate-term u ctx)))
    ((list 'unop op u)
     (operate op (translate-term u ctx)))
    ((list 'binop u op v)
     (operate op
              (translate-term u ctx)
              (translate-term v ctx)))
    ((list 'if-then-else u v w)
     (smt.ite (translate-term u ctx)
              (translate-term v ctx)
              (translate-term w ctx)))
    (_
     (error 'translate-term "unrecognized term: ~a" t))))
(define (operate op . args)
  (define op:proc (hash "!" smt.!
                        "&" smt.&&
                        "|" smt.||
                        "<->" smt.<=>))
  (define op:symbolic (hash "!" 'not
                            "&" 'and
                            "|" 'or
                            "<->" 'iff
                            "AF" 'AF "EF" 'EF "F" 'Eventually
                            "AG" 'AG "EG" 'EG "G" 'Henceforth
                            "AX" 'AX "EX" 'EX "X" 'Subsequently
                            "U" 'Until))
  (cond
    ((and (hash-has-key? op:proc op)
          (andmap (negate list?) args))
     (apply (hash-ref op:proc op) args))
    (else
     (cons (hash-ref op:symbolic op) args))))


(define (nusmv-path->input-port path)
  (define path~
    (cond
      ((path? path) path)
      ((string? path) (string->path path))
      (else (error 'nusmv-path->input-port "bad path"))))
  (cond
    ((has-extension? path~ ".obm")
     (open-input-file path~))
    ((has-extension? path~ ".smv")
     (define random-label (~a #:width 8 (random (expt 10 8) (expt 10 9))))
     (begin
       (define tmpfile (make-temporary-file
                        (format "mc3-~a-~~a.obm" random-label)))
       (todo "catch exceptions to ensure that the temporary file gets deleted"))
     (system
      (format "NuSMV -ic -ii -ils -ips -is -df -obm ~a ~a"
              tmpfile
              path~))
     (define obm-contents (file->string tmpfile))
     (delete-file tmpfile)
     (open-input-string obm-contents))
    (else
     (error
      'nusmv-path->input-port
      (format "path does not have a recognized NuSMV extension: ~a"
              path~)))))


(define read-nusmv (compose translate nusmv->datum nusmv-path->input-port))
