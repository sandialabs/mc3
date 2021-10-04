#lang racket


(define (parse-logs name)
  (msg "benchmark: ~a" name)
  (define mc3-log (file->string (string-append name ".log")))
  (define mc3-result
    (let ((m* (regexp-match #rx"\\[INFO: solution: #.\\]" mc3-log)))
      (match (last (string-split (first m*)))
        ("#f]" #f)
        ("#t]" #t))))
  (msg "result: ~a" mc3-result)
  (define mc3-time
    (let ((m* (regexp-match #rx"cpu time: [0-9]*" mc3-log)))
      (/ (string->number (last (string-split (first m*)))) 1000.0)))
  (msg "mc3: ~a" mc3-time)
  (define smv-data
    (for/hash ((mode (list "00" "01" "10" "11")))
      (define smv-log
        (file->string (string-append name (string-append ".smvlog" mode))))
      (define smv-result
        (let ((m* (regexp-match #rx"-- specification .*?  is (?:true|false)"
                                smv-log)))
          (if (false? m*)
              (void)
              (match (last (string-split (first m*)))
                ("false" #f)
                ("true" #t)))))
      (unless (or (void? smv-result) (eq? smv-result mc3-result))
        (error "disagreement"))
      (define smv-time
        (let ((m* (regexp-match #rx"User time .*?(?=\n)" smv-log)))
          (if (false? m*)
              (void)
              (string->number (third (string-split (first m*)))))))
      (define smv-oom
        (let ((m* (regexp-match #rx"Out of memory" smv-log)))
          (not (false? m*))))
      (values mode (cond
                     (smv-oom "\\texttt{M}")
                     ((void? smv-time) "\\texttt{T}")
                     (else (exact-round smv-time))))))
  (let* ((smv-times (filter number?
                            (map (curry hash-ref smv-data)
                                 (list "00" "01" "10" "11"))))
         (smv-best (apply min (cons +inf.0 smv-times))))
    (msg "NuSMV: ~a" smv-best)
    (format "\\texttt{~a} & ~a & ~a & ~a & ~a & ~a & ~a \\\\"
            (last (string-split name "/"))
            (match mc3-result
              (#t "$\\models$")
              (#f "$\\not\\models$")
              ((? void?) "???"))
            (let ((mc3-time~ (exact-round mc3-time)))
              (if (< mc3-time~ smv-best)
                  (format "\\textcolor{green}{\\textbf{~a}}" mc3-time~)
                  mc3-time~))
            (hash-ref smv-data "00")
            (hash-ref smv-data "01")
            (hash-ref smv-data "10")
            (hash-ref smv-data "11"))))


(define (msg fmt . vals)
  (displayln (apply format (cons fmt vals)) (current-error-port)))


(define (main)
  (define args
    (command-line
     #:args args
     args))
  (define lines
    (map parse-logs (sort args string<?)))
  (displayln (string-join lines "\n")))
(main)
