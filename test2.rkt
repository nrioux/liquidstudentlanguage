#lang s-exp "./lang.rkt"
(require rackunit)
(require rackunit/turnstile)

(define (x : Number) 42)
(check-type x : (Refine (_ : Number) #t))
