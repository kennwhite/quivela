#lang rosette

;; Racket's builtin logger makes it unnecessarily complicated to
;; output in the repl buffer and to change the level easily..
(provide info warn debug err set-log-level!)

(define log-level 'info)

(define (set-log-level! new-level)
  (set! log-level new-level))

(define level-numbers
  (make-immutable-hash '((debug . 0) (info . 1) (warn . 2) (err . 3))))

(define (level-<=? l1 l2)
  (<= (hash-ref level-numbers l1)
      (hash-ref level-numbers l2)))

(define-syntax-rule (make-log-fun level)
  (lambda (msg . rest)
    (when (level-<=? log-level level)
      (if (empty? rest)
          (display (format "[~a] ~a~n" level msg))
          (display (format "[~a] ~a~n" level (apply format msg rest)))))))

(define info (make-log-fun 'info))
(define warn (make-log-fun 'warn))
(define err (make-log-fun 'err))
(define debug (make-log-fun 'debug))
