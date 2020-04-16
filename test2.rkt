#lang s-exp "./lang.rkt"
(require rackunit)
(require rackunit/turnstile)

(define (x : Number) 42)
(define (id [y : (Refine (_ : Number) #t)]) : Number
  y)
(check-type (id x) : #t)
