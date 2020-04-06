#lang turnstile+/quicklang
(require turnstile+/eval turnstile+/typedefs turnstile+/more-utils)

(provide Π Boolean String Char Number SExp
         #%datum

         [rename-out
          (app           #%app)
          (define        define)
          (lsl-cond      cond)
          (lsl-if        if)
          #;(define-struct define-struct)
          (plus          +)])


;; Types
(define-type Type : Type)
(define-type Number : Type)
(define-type Boolean : Type)
(define-type String : Type)
(define-type Char : Type)
(define-type SExp : Type)

(define-type Π #:with-binders [X : Type] : Type -> Type)
(define-type Σ #:with-binders [X : Type] : Type -> Type)
(define-type refine #:with-binders [X : Type] : Boolean -> Type)

(define-typed-syntax plus
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Number] ...
   --------
   [⊢ (+ e- ...) ⇒ Number]])

(define-typed-syntax #%datum
  [(_ . n:number) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Number]]
  [(_ . b:boolean) ≫
   --------
   [⊢ (#%datum- . b) ⇒ Boolean]]
  [(_ . c:char) ≫
   --------
   [⊢ (#%datum- . c) ⇒ Char]]
  [(_ . s:string) ≫
   --------
   [⊢ (#%datum- . s) ⇒ String]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x
                        #:msg "Unsupported literal: ~v" #'x)]])

;; TODO separate annotations from the definitions
#;(define-typerule
    (lsl-module-begin
     (~seq ann def) ...) ≫
    -------
    [≻ (#%module-begin (annotate-def ann def) ...)])

(define-typerule lam
  [(_ [x:id (~datum :) τin] e) ≫
   [⊢ τin ≫ τin- ⇐ Type]
   [[x ≫ x- : τin] ⊢ e ≫ e- ⇒ τout]
   --------
   [⊢ (λ (x-) e-) ⇒ (Π (x- : τin) τout)]])

(define-typerule app
  [(_ f arg) ≫
   [ ⊢ f ≫ f- ⇒ (~Π (x : τin) τout) ]
   [ ⊢ arg ≫ arg- ⇐ τin]
   #:with τout- (reflect (subst #'arg- #'x #'τout))
   --------
   [⊢ (f- arg-) ⇒ τout-]])


(define-red β
  (#%plain-app ((~literal #%plain-lambda) (x) body) e)
  ~> ($subst e x body))

(define-typerule define #:datum-literals (:)
  [(_ (f:id [x:id : τin]) : τout e) ≫
   [⊢ [τin ≫ τin- ⇐ Type] [τout ≫ τout- ⇐ Type]]
   --------
   [≻ (define-typed-variable f (lam [x : τin] e) ⇐ (Π (x : τin-) τout-))]]
  [(_ (x:id : τ) e) ≫
   --------
   [≻ (define-typed-variable x e ⇐ τ)]])

(define-typerule lsl-cond #:datum-literals (else)
  [(_ [test0 body0] [test body] ...) ≫
   [⊢ test0 ≫ test0- ⇐ Boolean]
   [⊢ body0 ≫ body0- ⇒ τ]
   [⊢ test ≫ test- ⇐ Boolean] ...
   [⊢ body ≫ body- ⇐ τ] ...
   --------
   [⊢ (cond [test0- body0-] [test- body-] ...) ⇒ τ ]])

;; TODO manually typecheck if so we get good error messages
(define-syntax lsl-if
  (syntax-parser
    [(_ test e1 e2)
     #'(lsl-cond [test e1]
                 [#t   e2])]))

#;(define-typerule define-struct #:datum-literals (:)
  [(_ user-type-name [(field : τ_f) ...]) ≫
   ;; Create temporary (untyped) names for the underlying struct and its accessors
   #:with (struct-name-) (generate-temporaries #'(user-type-name))
   #:with (getter- ...) (stx-map (λ (f) (format-id #'struct-name- "~a-~a" #'struct-name- f)) #'(field ...))

   ;; These are the typed identifiers accessible to the user
   #:with user-ctor (format-id #'user-type-name "make-~a" #'user-type-name)
   ;; The accessors exposed to the user are just the user's name for the type and the field names hyphenated
   #:with (user-getter ...) (stx-map (λ (f) (format-id #'user-type-name "~a-~a" #'user-type-name f)) #'(field ...))
   --------
   [≻ (begin
        (define-type-constructor user-type-name #:arity = 0)
        (define-typed-variable-rename user-ctor ≫ struct-name- : (→ τ_f ... (user-type-name)))
        (define-typed-variable-rename user-getter ≫ getter- : (→ (user-type-name) τ_f)) ...
        (struct struct-name- (field ...) #:transparent #:reflection-name 'user-type-name))]])
