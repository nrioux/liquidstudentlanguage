#lang s-exp "./lang.rkt"
(require rackunit)
(require rackunit/turnstile)

;; Literals
(check-type #t : Boolean)
(check-type #f : Boolean)
(check-type "Hello, world!" : String)
;; (check-type #\c : Char)
(check-type 42 : Number)

;; Definitions
(define (x : Number) 42)
(check-type x : Number)
(check-type x : (Refine (_ : Number) #t))
(check-type x : (Refine (v : Number) (equal? v 42)))
(check-not-type x : (Refine (_ : Boolean) #t))
;; FAIL
(check-not-type x : (Refine (_ : Number) #f))

;; Functions
#;(define (thunk) : Boolean
  #t)
#;(check-type thunk : (→ Boolean))

(define (add1 [n : Number]) : Number
  (+ n 1))
(check-type add1 : (Π (_ : Number) Number))
(check-type add1 : (Π (n : Number) (Refine (m : Number) (> m n))))
;; FAIL
#;(check-not-type add1 : (Π (n : Number) (Refine (m : Number) (< m n))))

#;(define (result : Number) (add1 x))
#;(check-eqv? result 43)
#;(check-type result : Number)

;; Cond
(check-type (cond [#t 1]) : Number)
#;(check-type (cond [#t 1]
                  [#f 2]) : Number)
(typecheck-fail (cond))
(typecheck-fail (cond [#f 1]
                      [#t "false"])
                #:with-msg "type mismatch")

#;(check-type (if #t #f #t) : Boolean)
(typecheck-fail (if 1 2 3) #:with-msg "type mismatch")


;; Structs
#;(define-struct posn [(x : Number) (y : Number)])

#;(check-type (make-posn 3 4) : (posn))
#;(typecheck-fail (make-posn "a" "b"))

#;(define (pythag : (posn))
  (make-posn 3 4))

#;(define (sum : Number)
  (+ (posn-x pythag) (posn-y pythag)))
#;(check-type sum : Number)
#;(check-eqv? sum 7)

#;(define (aggregate (p : (posn)) (op : (→ Number Number Number))) : Number
  (op (posn-x p) (posn-y p)))
#;(check-type (aggregate pythag +) : Number)

#;pythag
