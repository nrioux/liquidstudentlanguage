#lang turnstile+
(require turnstile+/eval turnstile+/typedefs turnstile+/more-utils
         syntax/parse
         (for-syntax rosette/safe))

(provide Π Refine Boolean String Char Number SExp
          require

         [rename-out
          (lsl-datum         #%datum)
          (lsl-module-begin #%module-begin)
          (lsl-top-interaction #%top-interaction)
          (app           #%app)
          (lsl-define        define)
          #;(lsl-cond      cond)
          (lsl-if        if)
          #;(define-struct define-struct)
          (lsl-plus      +)
          (lsl-minus     -)
          (lsl-mult      *)
          (lsl-div       /)
          (lsl-<         <)
          (lsl->         >)
          (lsl-<=        <=)
          (lsl->=        >=)
          (lsl-integer?  integer?)
          (lsl-positive? positive?)
          (lsl-and       and)
          (lsl-or        or)
          (lsl-not       not)
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
                             ((current-type-eval) #'τ)))))


  (define-syntax-class env-item #:description "an environment item"
    (pattern (x:identifier p c))
    (pattern ((~literal #%constr) c)))
  (define-syntax-class env #:description "an environment"
    (pattern (_:env-item ...)))

  (define-syntax-class env/f #:description "an environment"
    (pattern (~or (~and #f (~bind [env #'()]))
                  (~and ϕ:env (~bind [env #'ϕ]))))))



;; Pi Types
;; Based on the turnstile typedef implementation
;; Re-implemented rather than using define-type to propagate env syntax property
(struct pi (τ c))
(define-typed-syntax Π
  [(_ [x : τin] τout) ⇐ env ϕ:env ≫
   [⊢ τin ≫ τin- (⇐ : Type) (⇐ env ϕ)]
   [[x ≫ x- : τin] ⊢ τout ≫ τout- (⇐ : Type) (⇐ env ϕ)]
   -------
   [⊢ (#%plain-app pi τin- (#%plain-lambda (x-) τout-)) ⇒ Type]])

(begin-for-syntax
  (define pi/internal (expand/df #'pi))
  (define-syntax ~Π
    (pattern-expander
     (syntax-parser
       [(_ [x:id (~datum :) τin] τout)
        #:with ty-to-match (generate-temporary)
        #:do [(printf "in Π~ ~n")]
        #'(~and ty-to-match
                (~parse
                 ((~literal #%plain-app)
                  (~and name/internal:id
                        (~fail
                         #:unless (free-id=? #'name/internal pi/internal)
                         (format "Expected function type, got: ~a"
                                 (type->str #'ty-to-match)
                                 #;(syntax->datum (resugar-type #'ty-to-match)))))
                  τin
                  ((~literal #%plain-lambda) (x) τout))
                 #'ty-to-match))]))))


;; Refinement Types
;; Based on the turnstile typedef implementation
;; Originally re-implemented so we have access to the internal refine struct, but
;; I'm not sure if this is still necessary
(struct refine (τ c))
(define-typed-syntax Refine
  [(_ [x : τ:base-type] c) ⇐ env ϕ-orig:env/f ≫
   #:with ϕ:env #'ϕ-orig.env
   [⊢ τ ≫ τ- (⇐ : Type) (⇐ env ϕ)]
   [[x ≫ x- : τ] ⊢ c ≫ c- (⇐ : Boolean) (⇐ env ϕ)]
   -------
   [⊢ (#%plain-app refine τ- (#%plain-lambda (x-) c-)) ⇒ Type]])

(define-syntax Refine/untyped
  (syntax-parser
    [(_ [x:identifier : τ:base-type] c)
     #:with out (assign-type #'(#%plain-app refine τ (#%plain-lambda (x) c)) #'Type)
     #'out]))

(begin-for-syntax
  (define refine/internal (expand/df #'refine))
  (define-syntax ~Refine
    (pattern-expander
     (syntax-parser
       [(_ [x:id (~datum :) τ-base] c)
        #:do [(printf "in Π~ ~n")]
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
                 #'ty-to-match))])))

  ;; Get the base type that describes the data of the given type
  ;; Identity for base types
  ;; Returns the base type annotation for refinement types
  ;; Returns #f for other (Pi/Sigma) types
  (define (get-base-type τ)
    (syntax-parse τ
      [τ-base:base-type #'τ-base]
      [(~Refine (_ : τ-base) _) #'τ-base]
      [_ #f]))

  (define (get-refinement x τ)
    (syntax-parse τ
      [τ-base:base-type #'#t]
      [(~Refine (v : τ-base) c) #`($subst #,x v c)]
      [_ #f]))

  ;; Get a constraint for the SMT solve as a syntax object that describes the
  ;; variable x given that it has type τ
  (define (lq-constraint x τ)
    (syntax-parse τ
      [(~or ~Number ~Boolean ~String ~Char) #'#t]
      [~Unit #'(equal? x #t)]
      [(~Refine (v : τ-base) c)
       #:with c-base (lq-constraint x #'τ-base)
       #`(and c-base ($subst #,x v c))]
      [_ #'#t]))

  (define type->lq-pred
    (syntax-parser
      [~Number  real?]
      [~Unit    boolean?] ;; unit encoded as #t
      [~Boolean boolean?]
      [~String  string?]
      [~Char    char?]
      #;[(_ ~SExp)    ???]
      [(~Π [x : τin] τout) integer?]
      [(~Refine [x : τ-base] _) (type->lq-pred #'τ-base)]))

  (define env-empty (list))
  (define (env-ext-constr ϕ c)
    (cons #`(#%constr #,c) ϕ))
  (define (env-ext ϕ x τ)
    (assert (identifier? x))
    (define τ- ((current-type-eval) τ))
    (define predicate (type->lq-pred τ-))
    (define constraint (lq-constraint x τ-))
    (cons #`(#,x #,predicate #,constraint) ϕ))
  (define (env-single x τ)
    (env-ext env-empty x τ)))

;; Base type values and operations
;; TODO abstract these definitions
(define-typed-syntax unit
  [_ ≫
   #:with out #'#t
   #:with x (generate-temporary)
   #:with c (assign-type #'(equal? x out))
   #:with τ #'(Refine (x : Unit) c)
   -------
   [⊢ out ⇒ τ]])

(define-typed-syntax lsl-plus
  [(_ e ...) (⇐ env ϕ) ≫
   [⊢ e ≫ e- (⇐ : Number) (⇐ env ϕ)] ...
   #:with out #'(+ e- ...)
   #:with x (generate-temporary)
   #:with c (assign-type #'(equal? x out) #'Boolean)
   #:with τ #'(Refine (x : Number) c)
   --------
   [⊢ out ⇒ τ]])

(define-typed-syntax lsl-minus
  [(_ e ...) (⇐ env ϕ) ≫
   [⊢ e ≫ e- (⇐ : Number) (⇐ env ϕ)] ...
   #:with out #'(- e- ...)
   #:with x (generate-temporary)
   #:with c (assign-type #'(equal? x out) #'Boolean)
   #:with τ #'(Refine (x : Number) c)
   --------
   [⊢ out ⇒ τ]])

(define-typed-syntax lsl-mult
  [(_ e ...) (⇐ env ϕ) ≫
   [⊢ e ≫ e- (⇐ : Number) (⇐ env ϕ)] ...
   #:with out #'(* e- ...)
   #:with x (generate-temporary)
   #:with c (assign-type #'(equal? x out) #'Boolean)
   #:with τ #'(Refine (x : Number) c)
   --------
   [⊢ out ⇒ τ]])

(define-typed-syntax lsl-div
  [(_ e1 e2) (⇐ env ϕ) ≫
   [⊢ e1 ≫ e1- (⇐ : Number) (⇐ env ϕ)]
   [⊢ e2 ≫ e2- (⇐ : (Refine (v : Number) (not (equal? v 0)))) (⇐ env ϕ)]
   #:with out #'(/ e1- e2-)
   #:with x (generate-temporary)
   #:with c (assign-type #'(equal? x out) #'Boolean)
   #:with τ #'(Refine (x : Number) c)
   --------
   [⊢ out ⇒ τ]])

(define-typed-syntax lsl-<
  [(_ e1 e2) ⇐ env ϕ ≫
   [⊢ e1 ≫ e1- (⇐ : Number) (⇐ env ϕ)]
   [⊢ e2 ≫ e2- (⇐ : Number) (⇐ env ϕ)]
   #:with out #'(< e1- e2-)
   -------
   [⊢ out ⇒ Boolean]])

(define-typed-syntax lsl->
  [(_ e1 e2) ⇐ env ϕ ≫
   [⊢ e1 ≫ e1- (⇐ : Number) (⇐ env ϕ)]
   [⊢ e2 ≫ e2- (⇐ : Number) (⇐ env ϕ)]
   -------
   [⊢ (> e1- e2-) ⇒ Boolean]])

(define-typed-syntax lsl-<=
  [(_ e1 e2) ⇐ env ϕ ≫
   [⊢ e1 ≫ e1- (⇐ : Number) (⇐ env ϕ)]
   [⊢ e2 ≫ e2- (⇐ : Number) (⇐ env ϕ)]
   #:with out #'(<= e1- e2-)
   -------
   [⊢ out ⇒ Boolean]])

(define-typed-syntax lsl->=
  [(_ e1 e2) ⇐ env ϕ ≫
   [⊢ e1 ≫ e1- (⇐ : Number) (⇐ env ϕ)]
   [⊢ e2 ≫ e2- (⇐ : Number) (⇐ env ϕ)]
   -------
   [⊢ (>= e1- e2-) ⇒ Boolean]])


(define-typed-syntax lsl-integer?
  [(_ e) ⇐ env ϕ:env ≫
         [⊢ e ≫ e- (⇐ : Number) (⇐ env ϕ)]
         #:with x (generate-temporary 'x)
         #:with out #'(integer? e-)
         #:with v (generate-temporary 'v)
         #:with c (assign-type #'(equal? v out) #'Boolean)
         #:with τ (set-env #'(Refine/untyped (v : Boolean) c) #'ϕ)
         -------
         [⊢ out ⇒ τ]])

(define-typed-syntax lsl-positive?
  [(_ e) ⇐ env ϕ:env ≫
   [⊢ e ≫ e- (⇐ : Number) (⇐ env ϕ)]
   #:with x (generate-temporary 'x)
   #:with out #'(positive? e-)
   #:with v (generate-temporary 'v)
   #:with c (assign-type #'(equal? v out) #'Boolean)
   #:with τ (set-env #'(Refine/untyped (v : Boolean) c) #'ϕ)
   -------
   [⊢ out ⇒ τ]])

(define-typed-syntax lsl-and
  [(_ e ...) (⇐ env ϕ:env) ≫
   [⊢ e ≫ e- (⇐ : Boolean) (⇐ env ϕ)] ...
   -------
   [⊢ (and e- ...) ⇒ Boolean]])

(define-typed-syntax lsl-or
  [(_ e ...) (⇐ env ϕ:env) ≫
   [⊢ e ≫ e- (⇐ : Boolean) (⇐ env ϕ)] ...
   -------
   [⊢ (or e- ...) ⇒ Boolean]])

(define-typed-syntax lsl-not
  [(_ e) (⇐ env ϕ:env) ≫
   [⊢ e ≫ e- (⇐ : Boolean) (⇐ env ϕ)]
   -------
   [⊢ (not e-) ⇒ Boolean]])

#;(define-syntax join-types
  (define (join τacc τnext)
    )
  (syntax-parser
    [(_ τ . rst)
     (foldl )]))



(define-typed-syntax lsl-equal?
  [(_ e1 e2) ⇐ env ϕ:env ≫
   [⊢ e1 ≫ e1- (⇒ : τ1) (⇐ env ϕ)]
   [⊢ e2 ≫ e2- (⇒ : τ2) (⇐ env ϕ)]
   ;; #:when (comparable τ1 τ2)
   -------
   [⊢ (equal? e1- e2-) ⇒ Boolean]])

(define-for-syntax (prim-base-type v)
  (syntax-parse v
    [n:number  #'Number]
    [b:boolean #'Boolean]
    [c:char    #'Char]
    [s:string  #'String]))


(define-for-syntax (set-env e ϕ)
  (assert (syntax-parse ϕ
            [_:env #t]
            [_     #f]))
  (attach e 'env ϕ))
(define-for-syntax (prim-type v)
  (let* [[τ-base (prim-base-type v)]
  [lit #`(quote #,v) #;(assign-type #`(#%datum- #,v) τ-base)]]
  (assign-type #`(Refine/untyped (x : #,τ-base) (equal? x #,lit)) #'Type)))

(define-typed-syntax lsl-datum
  [(_ . v) ⇐ env ϕ:env ≫
   #:with τ (prim-type #'v)
   [⊢ τ ≫ τ- (⇐ : Type) (⇐ env ϕ)]
   --------
   [⊢ (#%datum- . v) ⇒ τ]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x
                        #:msg "Unsupported literal: ~v" #'x)]])

;; Subtype relation
(begin-for-syntax
  ;; Proof by logical evaluation (proof search)
  ;; Given the assumptions in ϕ, return true if c can be proven valid
  ;; ϕ - a list of syntax object boolean expressions that are assumed to evaluate to true
  ;; c - a syntax object boolean expression that we try to prove evaluates to true
  (define (ple ϕ c)
    (printf "(ple ~a ~a)~n" (syntax->datum ϕ) (syntax->datum c))
    (define build1
      (syntax-parser #:datum-literals (#%constr)
                     [(x p c-prem)
                      #:with def-sym #'(define-symbolic x p)
                      #:with premise #'(assert c-prem)
                      (list #'def-sym #'premise)]
                     [(#%constr c-prem)
                      #:with premise #'(assert c-prem)
                      (list #'premise)]))
    (with-syntax
      [(prems (append-map build1 (reverse (syntax->list ϕ))))
       (conclusion #`(assert #,c))
       (program #'(begin
                     (clear-asserts!)
                     (verify #:assume (begin  prems)
                             #:guarantee conclusion)))]
      (define ns (make-empty-namespace))
      (namespace-attach-module (current-namespace) 'rosette/safe ns)
      (namespace-require 'rosette/safe ns)
      (define solver-result (eval (syntax->datum #'program) ns))
      ;; (printf "EVAL RESULT: ~a~n" solver-result)
      (unsat? solver-result)))

  (define (get-env e)
    (detach e 'env))
  (define (strengthen-exact τ e)
    (syntax-parse ((current-type-eval) τ)
      [(~Refine (v : τ-base) c)
       #`(Refine/untyped (v : τ-base) (and c v #,e))]
      [τ-base:base-type
       #`(Refine/untyped (v : τ-base) (equal? v #,e))]
      [_ τ]))
  (define (default-⇐ e tag)
    ;; Apply T-Exact and T-Subsumption when checking
    (define τ-exp  (get-expected-type e))
    (define τ-actual (strengthen-exact (detach/check e tag) e))
    (define ϕ (or (get-env e) env-empty))
    #;(printf "~a ⊢ ~a : ~a <: ~a~n"
            ϕ (type->str e)
            (type->str τ-actual) (type->str τ-exp))
    (assert (syntax-parse ϕ
              [_:env #t]
              [_     #f]))
    (not (<: ϕ τ-actual τ-exp)))
  (current-⇐-check default-⇐)

  ;; Subtype relation
  ;; Can a τ1 be passed to a context expecting a τ2?
  (define (<: ϕ τ1 τ2)
    (define τ1- ((current-type-eval) τ1))
    (define τ2- ((current-type-eval) τ2))
    (syntax-parse (list τ1- τ2-)
      [((~Π (x1 : τ-in1) τ-out1) (~Π (x2 : τ-in2) τ-out2))
       (and (<: ϕ #'τ-in2  #'τ-in1)
            (<: (env-ext ϕ #'x2 #'τ-in2)
                (subst #'x2 #'x1 #'τ-out1) #'τ-out2))]
      [(_ (~Refine (x2 : τ-base2) c2))
       ;; #:do [(printf "Subtype: ~a <: ~a~n" (type->str τ1) (type->str τ2))]
       #:with τ-base1:base-type (get-base-type τ1-)
       #:when (type=? #'τ-base1 #'τ-base2)
       #:with ϕ+x2:env (env-ext ϕ #'x2 τ1-)
       (ple #'ϕ+x2 #'c2)]
      [((~Refine (x1 : τ-base1) _) τ-base2:base-type)
       (<: ϕ #'τ-base1 #'τ-base2)]
      [_ (type=? τ1 τ2)]))
  (current-typecheck-relation (λ (τ1 τ2)
                                (printf "current-typecheck-relation ~a <: ~a ~n" (type->str τ1) (type->str τ2))
                                #;(<: #'() τ1 τ2)
                                (error "typecheck relation should not be used"))))




(define-syntax lsl-top-interaction
  (syntax-parser
    [(~and self (_ . e))
     #:with e/env (set-env #'e env-empty)
     #'(#%top-interaction . e/env)]))

#;(define-typerule lam
  [(_ [x:id (~datum :) τin] e) ⇐ env ϕ  ≫
   [⊢ τin ≫ τin- (⇐ Type) (⇐ env ϕ)]
   [[x ≫ x- : τin] ⊢ e ≫ e- (⇒ : τout) (⇐ env (x . ϕ))]
   --------
   [⊢ (λ (x-) e-) ⇒ (Π (x- : τin) τout)]])

(define-typerule app
  [(_ f arg) (⇐ env ϕ:env)  ≫
   [ ⊢ f ≫ f- (⇒ : (~Π (x : τin) τout)) (⇐ env ϕ) ]
   [ ⊢ arg ≫ arg- (⇐ : τin) (⇐ env ϕ)]
   #:with τout- (reflect (subst #'arg- #'x #'τout))
   --------
   [⊢ (f- arg-) ⇒ τout-]])


(begin-for-syntax
  (define-syntax-class defn
    #:description "a definition"
    #:attributes (name body τ)
    #:datum-literals (:)
    (pattern (_ (f:id [x:id : τin]) : τout e)
             #:attr name #'f
             #:attr body #'e
             #:attr τ    #'(Π (x : τin) τout))
    (pattern (_ (x:id : τ) e)
             #:attr name #'x
             #:attr body #'e)))


(define-for-syntax (refine-reflect τ e ϕ)
  (printf "in refine-reflect for ~a~n" (type->str τ))
  (syntax-parse τ
    [(~Refine [x : τ-base] c)
     #'(Refine [x : τ-base] (and e (lsl-equal? x c)))]
    [(~Π [x : τ-in] τ-out)
     #:with x- (fresh 'x)
     #:with e+ϕ (set-env e ϕ)
     #:with τr (refine-reflect #'τ-out (#'e+ϕ #'x-))
     #'(Π [x- : τ-in] τr)]
    [τ-base:base-type
     #:with x (generate-temporary 'v)
     #:with e+ϕ (set-env e ϕ)
     #:with c (assign-type #'(equal? x e+ϕ) #'Boolean)
     #'(Refine [x : τ-base] c)]))

(define-typerule lsl-define #:datum-literals (:)
  [(_ (f:id [x:id : τin]) : τout e) ⇐ env ϕ:env ≫
   #:do [(printf "BEGIN define fun ~a~n" (syntax->datum #'f))]
   #:with τout-r (refine-reflect #'τout #'e #'ϕ)
   #:do [(printf "reflected fun type ~n")]
   ;; [⊢ (Π (x : τin) τout-r) ≫ τ- (⇐ : Type) (⇐ env ϕ)]

   ;; #:with (~Π (xt- : τin-) τout-r-) #'τ-

   ;; We want a premise along these lines:
   ;;   [[x ≫ xe- : τin- ] ⊢ e ≫ e- (⇐ : ($subst x xt- τout-r)) (⇐ env ϕ-in)]
   ;; But ϕ-in must contain a constraint on xe-, and xe- is not bound in ϕ-in by
   ;; this rule. So we must do things manually.

   ;; Expand the context [x ≫ xe- : τin-]
   ;; #:do [(define Γ (expand1/bind #'x #': #'τin-))]
   #:with τ (set-env #'(Π (x : τin) τout) #'ϕ)
   #:do [(printf "begin expand fun type~n")]
   #:do [(define Γ (expands/bind #'(x f) #'(: :) #'(τin τ)))]
   #:do [(printf "end expand fun type~n")]
   #:with (xe- f-) (env-xs Γ)
   #:with (τin- τ-) (env-τs Γ)

   ;; Build constraints for the context
   #:with ϕ-in:env (env-ext #'ϕ #'xe- #'τin-) ;; TODO add f to ϕ

   ;; Expand output type
   #:do [(printf "expand output type~n")]
   #:with τout-r- (expand1 (set-env #'τout-r #'ϕ-in) Γ)
   #:do [(printf "end expand output type~n")]

   ;; Now we can expand e [e ≫ e- (⇐ : ($subst x xt- τout-r)) (⇐ env ϕ-in)]
   #:with e/exp (add-expected-type (attach #'e 'env #'ϕ-in) #'τout-r-)
   #:with e-  (expand1 #'e/exp Γ)
   #:with e-tmp #'e- #;(get-orig #'e-) ;; Uncomment if getting mysterious bad syntax errors
   #:with τ-tmp (detach/check #'e- ':)

   ;; Call out to the ⇐ rule to check that e was well typed.
   #:fail-unless (not ((current-⇐-check) #'e-tmp ':)) (typecheck-fail-msg/1 #'τout-r #'τ-tmp #'e-tmp)
   #:do [(printf "END define fun~n")]


   --------
   [⊢ (begin (define-typed-variable-rename f ≫ f- : τ-)
             (define (f- xe-) e-))
      (⇒ env ϕ)]]
  ;; TODO refinement reflection here?
  [(_ (x:id : τ) e) ⇐ env ϕ:env ≫
   #:with τr (refine-reflect #'τ #'e #'ϕ)
   [⊢ τr ≫ τr- (⇐ : Type) (⇐ env ϕ)]
   #:with ϕ-new:env (env-ext #'ϕ #'x #'τr-)
   [⊢ e ≫ e- (⇐ : τr) (⇐ env ϕ-new)]
   --------
   [⊢ (define-typed-variable x e- ⇒ τr-) (⇒ env ϕ-new)]])



(define-syntax lsl-module-begin
  (syntax-parser
    [(_ . body)
     ;; Iterate through each item in the module, building up constraints from
     ;; the type of each definition adding to the environment, and attaching it
     ;; to future items
     #:with (_ body-)
            (stx-fold (λ (e acc)
                        (syntax-parse (list e acc)
                          [(d:defn (ϕ:env (out ...)))
                           #:with d- (set-env #'d #'ϕ)
                           #:with next-ϕ:env (env-ext #'ϕ #'d.name (set-env #'d.τ #'ϕ))
                           #'(next-ϕ (out ... d-))]
                          [(e (ϕ:env (out ...)))
                           #:with e- (set-env #'e #'ϕ)
                           #'(ϕ (out ... e-))]))
                        #'(() ()) #'body)
     #'(#%module-begin . body-)]))

#;(define-typerule defns
  [(_) ≫
   --------
   [≻ (begin)]]
  [(_ d:defn . rst) ⇐ env ϕ:env ≫
   #:do [(printf "defn ~a: ~a  / ~a~n" (syntax->datum #'d.name) #'d #'ϕ)]
   [⊢ d ≫ d- ⇐ env ϕ]
   #:do [(printf "continue: ~a~n" #'d.name)]
   #:with c (lq-constraint ((current-type-eval) #'d.τ))
   #:with next-ϕ #'(c . ϕ)
   #:do [(printf "pre-defns~n")]
   [⊢ (defns . rst) ≫ rst- ⇐ next-ϕ]
   #:do [(printf "pre-out~n")]
   #:with out #'(defns . rst-)
   #:do [(printf "out: ~a~n" #'out)]
   --------
   [⊢ (d- . rst-)]]
  #;[(_ e . rst) ≫ ⇐ env ϕ:env
   [⊢ e ≫ e-]
   --------
   [⊢ e-]])

(define-for-syntax (meet-types τ1 τ2)
  (syntax-parse (list τ1 τ2)
    [((~Π (x1 : τin1) τout1) (~Π (x2 : τin2) τout2))
     #:with x #'x1
     #:with τin (join-types #'τin1 #'τin2)
     #:with τout (meet-types #'($subst x x1 τout1) #'($subst x x2 τout2))
     #:when (and #'τin #'τout)
     #'(Π (x : τin) τout)]
    [_
     #:with τ-base1 (get-base-type τ1)
     #:with τ-base2 (get-base-type τ2)
     #:when (and #'τ-base1 #'τ-base2 (type=? #'τ-base1 #'τ-base2))
     #:with v (generate-temporary 'v)
     #:with c1 (get-refinement #'v τ1)
     #:with c2 (get-refinement #'v τ2)
     #'(Refine/untyped (v : τ-base1) (and c1 c2))]
    [_ #f]))
(define-for-syntax (join-types τ1 τ2)
  (syntax-parse (list τ1 τ2)
    [((~Π (x1 : τin1) τout1) (~Π (x2 : τin2) τout2))
     #:with x #'x1
     #:with τin (meet-types #'τin1 #'τin2)
     #:with τout (join-types #'($subst x x1 τout1) #'($subst x x2 τout2))
     #:when (and #'τin #'τout)
     #'(Π (x : τin) τout)]
    [_
     #:with τ-base1 (get-base-type τ1)
     #:with τ-base2 (get-base-type τ2)
     #:when (and #'τ-base1 #'τ-base2 (type=? #'τ-base1 #'τ-base2))
     #:with v (generate-temporary #'v)
     #:with c1 (get-refinement #'v τ1)
     #:with c2 (get-refinement #'v τ2)
     #'(Refine/untyped (v : τ-base1) (or c1 c2))]
    [_ #f]))

(define-typerule lsl-if
  [(_ test e1 e2) (⇐ env ϕ) ≫
     [⊢ test ≫ test- (⇐ : Boolean) (⇐ env ϕ)]
     #:with ϕ1 (env-ext-constr #'ϕ #'test-)
     [⊢ e1 ≫ e1- (⇒ : τ1) (⇐ env ϕ1)]
     #:with ϕ2 (env-ext-constr #'ϕ #'(not test-))
     [⊢ e2 ≫ e2- (⇒ : τ2) (⇐ env ϕ2)]
     #:with τ (join-types #'τ1 #'τ2)
     #:fail-unless #'τ (format "types ~a and ~a are not compatible" (type->str #'τ1) (type->str #'τ2))
     -------
     [⊢ (if test- e1- e2-) ⇒ τ]])

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
