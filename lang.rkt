#lang turnstile+/quicklang
(require turnstile+/eval turnstile+/typedefs turnstile+/more-utils
         syntax/parse
         (for-syntax rosette/safe))

(provide Π Refine Boolean String Char Number SExp
         #%datum

         [rename-out
          (app           #%app)
          (define        define)
          (lsl-cond      cond)
          (lsl-if        if)
          #;(define-struct define-struct)
          (lsl-plus      +)
          (lsl-<         <)
          (lsl->         >)
          (lsl-and       and)
          (lsl-equal?    equal?)])


;; Types
(define-type Type : Type)

;; (define-type Condition : Type)

(define-type Number : Type)
(define-type Unit : Type)
(define-type Boolean : Type)
(define-type String : Type)
(define-type Char : Type)
(define-type SExp : Type)

(begin-for-syntax
  (define-syntax ~base-type
    (pattern-expander
     (syntax-parser
       [_ #'(~or ~Number ~Unit ~Boolean ~String ~Char ~SExp)])))

  (define-syntax-class base-type #:description "a base type"
    (pattern (~and τ (~parse (~base-type)
                             ((current-type-eval) #'τ))))))

(define-syntax lq-predicate
  (syntax-parser
    [(_ ~Number)  number?]
    [(_ ~Unit)    boolean?] ;; unit encoded as #t
    [(_ ~Boolean) boolean?]
    [(_ ~String)  string?]
    [(_ ~Char)    char?]
    #;[(_ ~SExp)    ???]))

(begin-for-syntax
  (define (lq-constraint τ x)
    (syntax-parse τ
      [(~or ~Number ~Boolean ~String ~Char _) #'#t]
      [~Unit #'(equal? x #t)])))


(define-type Π #:with-binders [X : Type] : Type -> Type)
(define-type Σ #:with-binders [X : Type] : Type -> Type)

;; Refinement Types
;; Based on the turnstile typedef implementation
;; Originally re-implemented so we have access to the internal refine struct, but
;; I'm not sure if this is still necessary
(struct refine (τ c))
(define-typed-syntax Refine
  [(_ [x : τ:base-type] c) ≫
   [⊢ τ ≫ τ- ⇐ Type]
   [[x ≫ x- : τ] ⊢ c ≫ c- ⇐ Boolean]
   -------
   [⊢ (#%plain-app refine τ- (#%plain-lambda (x-) c-)) ⇒ Type]])

(begin-for-syntax
  (define refine/internal (expand/df #'refine))
  (define-syntax ~Refine
    (pattern-expander
     (syntax-parser
       [(_ [x:id (~datum :) τ-base] c)
        #:with ty-to-match (generate-temporary)
        #'(~and ty-to-match
                (~parse
                 ((~literal #%plain-app)
                  (~and name/internal:id
                        (~fail
                         #:unless (free-id=? #'name/internal refine/internal)
                         (format "Expected refinement type, got: ~a"
                                 (resugar-type #'ty-to-match)
                                 #;(syntax->datum (resugar-type #'ty-to-match)))))
                  τ-base
                  ((~literal #%plain-lambda) (x) c))
                 #'ty-to-match))]))))

;; Base type values and operations
(define-typed-syntax unit
  [_  (⇐ : (~Refine (x : ~Unit) c)) (⇐ env ϕ) ≫
   #:with out #'#t
   #:when (ple #'((equal? x out) . ϕ) #'c)
   -------
   [⊢ out]]
  [_ ≫
   #:with out #'#t
   #:with x (generate-temporary)
   #:with c (assign-type #'(equal? x out))
   #:with τ #'(Refine (x : Unit) c)
   -------
   [⊢ out ⇒ τ]])

(define-typed-syntax lsl-plus
  [(_ e ...) (⇐ : (Refine (x : ~Number) c)) (⇐ env ϕ) ≫
   [⊢ e ≫ e- ⇐ Number] ...
   #:with out #'(+ e- ...)
   #:when (ple #'((equal? x out) . ϕ) #'c)
   -------
   [⊢ out]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Number] ...
   #:with out #'(+ e- ...)
   #:with x (generate-temporary)
   #:with c (assign-type #'(equal? x out) #'Boolean)
   #:with τ #'(Refine (x : Number) c)
   --------
   [⊢ out ⇒ τ]])

(define-typed-syntax lsl-<
  [(_ e1 e2) (⇐ : (~Refine (x : ~Boolean) c)) (⇐ env ϕ) ≫
   [⊢ e1 ≫ e1- ⇐ Number]
   [⊢ e2 ≫ e2- ⇐ Number]
   #:with out #'(< e1- e2-)
   #:when (ple #'((equal? x out) . ϕ) #'c)
   --------
   [⊢ out ⇒ τ]]
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇐ Number]
   [⊢ e2 ≫ e2- ⇐ Number]
   #:with out #'(< e1- e2-)
   -------
   [⊢ out ⇒ Boolean]])

(define-typed-syntax lsl->
  [(_ e1 e2) (⇐ : (~Refine (x : ~Boolean) c)) (⇐ env ϕ) ≫
   [⊢ e1 ≫ e1- ⇐ Number]
   [⊢ e2 ≫ e2- ⇐ Number]
   #:with out #'(> e1- e2-)
   #:when (ple #'((equal? x out) . ϕ) #'c)
   --------
   [⊢ out ⇒ τ]]
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇐ Number]
   [⊢ e2 ≫ e2- ⇐ Number]
   -------
   [⊢ (> e1- e2-) ⇒ Boolean]])


(define-typed-syntax lsl-and
  [(_ e ...) (⇐ : (Refine (x : ~Number) c)) (⇐ env ϕ) ≫
   [⊢ e ≫ e- ⇐ Number] ...
   #:with out #'(and e- ...)
   #:when (ple #'((equal? x out) . ϕ) #'c)
   -------
   [⊢ out]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Boolean] ...
   -------
   [⊢ (and e- ...) ⇒ Boolean]])

#;(define-syntax join-types
  (define (join τacc τnext)
    )
  (syntax-parser
    [(_ τ . rst)
     (foldl )]))

(define-typed-syntax lsl-equal?
  [(_ e1 e2) (⇐ : (~Refine (x : ~Boolean) c)) (⇐ env ϕ) ≫
   [⊢ e1 ≫ e1- ⇐ Number]
   [⊢ e2 ≫ e2- ⇐ Number]
   #:with out #'(equal? e1- e2-)
   #:when (ple #'((equal? x out) . ϕ) #'c)
   --------
   [⊢ out ⇒ τ]]
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ τ1]
   [⊢ e2 ≫ e2- ⇒ τ2]
   #:fail-unless (<: #'τ2 #'τ1) "TEMPORARY"
   ;; [τ2 τ⊑ τ1]
   ;; #:with τout (join-types τ1 τ2)
   -------
   [⊢ (equal? e1- e2-) ⇒ Boolean]])

(define-for-syntax (prim-base-type v)
  (syntax-parse v
    [n:number  #'Number]
    [b:boolean #'Boolean]
    [c:char    #'Char]
    [s:string  #'String]))


(define-for-syntax (prim-type v)
  (let* [[τ-base (prim-base-type v)]
         [lit (assign-type #`(#%datum- #,v) τ-base)]]
    #`(Refine (x : #,τ-base) (lsl-equal? x #,lit))))

(define-typed-syntax #%datum
  [(_ . v) (⇐ : (~Refine (x : τ-base) c)) (⇐ env ϕ) ≫
   #:with out #'(#%datum- . v)
   #:when (ple #'((equal? x out) . ϕ) #'c)
   --------
   [⊢ out]]
  [(_ . v) ⇐ env ϕ ≫
   #:with τ (prim-type #'v)
   --------
   [⊢ (#%datum- . v) ⇒ τ]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x
                        #:msg "Unsupported literal: ~v" #'x)]])

(define-typed-variable-syntax
  [(_ x ≫ x- : τ) ⇐ τr #;(~and τr (~Refine (y : τ-base) c)) #;(⇐ env ϕ) ≫
   #:do [(printf "~a ⇐ ~a~n" #'x (type->str #'τr))]
   ;; #:fail-unless (ple #'ϕ (subst #'x- #'y #'c)) "ple failed"
   --------
   [⊢ x- ]]
  [(_ x ≫ x- : τ) (⇐ env _) ≫
   #:do [(printf "~a ⇒ ~a~n" #'x (type->str #'τ))]
   --------
   [⊢ x- ⇒ τ]])

;; Subtype relation
(begin-for-syntax
  ;; Proof by logical evaluation (proof search)
  ;; Given the assumptions in ϕ, return true if c can be proven valid
  ;; ϕ - a list of syntax object boolean expressions that are assumed to evaluate to true
  ;; c - a syntax object boolean expression that we try to prove evaluates to true
  (define (ple ϕ c)
    ;; Check for syntactic equality
    ;; Based on https://stackoverflow.com/a/53450175/568190
    #;(implies (eval-syntax c1) (eval-syntax c2))
    (printf "(ple ~a ~a)~n" (syntax->datum ϕ) (syntax->datum c))
    #t)

  ;; Subtype relation
  ;; Can a τ1 be passed to a context expecting a τ2?
  (define (<: τ1 τ2)
    (<:* (list) τ1 τ2))
  (define (<:* ϕ τ1 τ2)
    (define τ1- ((current-type-eval) τ1))
    (define τ2- ((current-type-eval) τ2))
    (printf "(<: ~a ~a)~n" (type->str τ1-) (type->str τ2-))
    (syntax-parse (list τ1- τ2-)
      [((~Π (x1 : τ-in1) τ-out1) (~Π (x2 : τ-in2) τ-out2))
       (define (r->s τr) τr)
       (and (<:* ϕ #'τ-in2  #'τ-in1)
            (<:* (cons (r->s #'τ-in2) ϕ)
                 (subst #'x2 #'x1 #'τ-out1) #'τ-out2))]
      [((~Refine (x1 : τ-base1) c1) (~Refine (x2 : τ-base2) c2))
       (error "refine subtype")
       #;(and (type=? #'τ-base1 #'τ-base2)
            (let* [(ϕ    (list)) ;; TODO how to build this environment?
                   (ϕ+x2 (cons (subst #'x2 #'x1 #'c1) ϕ))]
              #;(printf "<:  ~a /// ~a~n"
                      (map (λ (k) (list k (syntax-property #'c1 k))) (syntax-property-symbol-keys #'c1))
                      (syntax-property-symbol-keys #'c2))
              (ple ϕ+x2 #'c2)))]
      [((~Refine (x1 : τ-base1) _) τ-base2)
       (<: #'τ-base1 #'τ-base2)]
      [(_ (~Refine (_ : _) _))
       (error "refine subtype")]
      [_ (type=? τ1 τ2)]))
  (current-typecheck-relation <:))



;; TODO separate annotations from the definitions
#;(define-typerule
    (lsl-module-begin
     (~seq ann def) ...) ≫
    -------
    [≻ (#%module-begin (annotate-def ann def) ...)])

#;(define-typerule lam
  [(_ [x:id (~datum :) τin] e) ⇐ env ϕ  ≫
   [⊢ τin ≫ τin- (⇐ Type) (⇐ env ϕ)]
   [[x ≫ x- : τin] ⊢ e ≫ e- (⇒ : τout) (⇐ env (x . ϕ))]
   --------
   [⊢ (λ (x-) e-) ⇒ (Π (x- : τin) τout)]])

(define-typerule app
  [(_ f arg) (⇐ env ϕ)  ≫
   [ ⊢ f ≫ f- (⇒ : (~Π (x : τin) τout)) (⇐ env ϕ) ]
   [ ⊢ arg ≫ arg- (⇐ : τin) (⇐ env ϕ)]
   #:with τout- (reflect (subst #'arg- #'x #'τout))
   --------
   [⊢ (f- arg-) ⇒ τout-]])


(define-for-syntax (refine-reflect τ e)
  (syntax-parse τ
    [((~datum Refine) τ-base c)    #'(Refine [x : τ-base] (and e (lsl-equal? x c)))]
    [τ-base
     #:with x (generate-temporary 'v)
     #:with c (assign-type #`(equal? x #,e) #'Boolean)
     #'(Refine [x : τ-base] c)]
    ;; [_ (error "No match for ~a" τ)]
    [((~datum Π) [x (~datum :) τ-in] τ-out)
     #:with x- (fresh 'x)
     #:with τr (refine-reflect #'τ-out (#'e #'x-))
     #'(Π [x- : τ-in] τr)]))

(define-typerule define #:datum-literals (:)
  [(_ (f:id [x:id : τin]) : τout e) ≫
   #:with τout-r (refine-reflect #'τout #'e)
   [⊢ τin ≫ τin- ⇐ Type]
   [[x ≫ x- : τin-] ⊢ τout-r ≫ τout-r- ⇐ Type]
   #:with c (lq-constraint #'τin- #'x-)
   [[x ≫ _ : τin-] ⊢ e ≫ e- (⇐ : τout-r-) (⇐ env (c))]
   --------
   [≻ (define-typed-variable f (λ (x-) e-) ⇒ (Π (x- : τin-) τout-r-))]]
  ;; TODO refinement reflection here?
  [(_ (x:id : τ) e) ≫
   [⊢ e ≫ e- (⇐ : τ)]
   --------
   [≻ (define-typed-variable x e- ⇒ τ)]])

(define-typerule lsl-cond #:datum-literals (else)
  [(_ [test body] ...+) (⇐ : τ) (⇐ env ϕ) ≫
   [⊢ test ≫ test- (⇐ : Boolean) (⇐ env ϕ)] ...
   ;; TODO constraints for earlier tests need to be negated in later bodies
   [⊢ body ≫ body- (⇐ : τ) (⇐ env (test- . ϕ))] ...
   --------
   [⊢ (cond [test0- body0-] [test- body-] ...)]]
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
