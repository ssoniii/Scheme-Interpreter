#lang racket

;; Project 3: Metacircular interpreter for Scheme
;; CIS352 -- Spring '25

(provide interp-ce)

; Your task is to write a CE interpreter for a substantial subset of Scheme/Racket. 
; A CE interpreter is meta-circular to a large degree (e.g., a conditional in the target
; language (scheme-ir?) can be implemented using a conditional in the host language (Racket),
; recursive evaluation of a sub-expression can be implemented as a recursive call to the
; interpreter, however, it's characterized by creating an explicit closure value for lambdas
; that saves its static environment (the environment when it's defined). For example, a CE
; interpreter for the lambda calculus may be defined:
(define (interp-ce-lambda exp [env (hash)])
  (match exp
         [`(lambda (,x) ,body)
          ; Return a closure that pairs the code and current (definition) environment
          `(closure (lambda (,x) ,body) ,env)]
         [`(,efun ,earg)
          ; Evaluate both sub-expressions
          (define vfun (interp-ce-lambda efun env))  
          (define varg (interp-ce-lambda earg env))
          ; the applied function must be a closure
          (match-define `(closure (lambda (,x) ,body) ,env+) vfun)
          ; we extend the *closure's environment* and interp the body
          (interp-ce-lambda body (hash-set env+ x varg))]
         [(? symbol? x)
          ; Look up a variable in the current environment
          (hash-ref env x)]))

; Following is a predicate for the target language you must support. You must support any
; syntax allowed by scheme-ir that runs without error in Racket, returning a correct value..
(define (scheme-ir? exp)
  ; You should support a few built-in functions bound to the following variables at the top-level
  (define (prim? s) (member s '(+ - * = equal? list cons car cdr null?)))
  (match exp
         [`(lambda ,(? (listof symbol?)) ,(? scheme-ir?)) #t] ; fixed arguments lambda
         [`(lambda ,(? symbol?) ,(? scheme-ir?)) #t] ; variable argument lambda
         [`(if ,(? scheme-ir?) ,(? scheme-ir?) ,(? scheme-ir?)) #t]
         [`(let ([,(? symbol?) ,(? scheme-ir?)] ...) ,(? scheme-ir?)) #t]
         [`(let* ([,(? symbol?) ,(? scheme-ir?)] ...) ,(? scheme-ir?)) #t]
         [`(and ,(? scheme-ir?) ...) #t]
         [`(or ,(? scheme-ir?) ...) #t]
         [`(apply ,(? scheme-ir?) ,(? scheme-ir?)) #t]
         [(? (listof scheme-ir?)) #t]
         [(? prim?) #t]
         [(? symbol?) #t]
         [(? number?) #t]
         [(? boolean?) #t]
         [''() #t]
         [_ #f]))

; Interp-ce must correctly interpret any valid scheme-ir program and yield the same value
; as DrRacket, except for closures which must be represented as `(closure ,lambda ,environment).
; (+ 1 2) can return 3 and (cons 1 (cons 2 '())) can yield '(1 2). For programs that result in a 
; runtime error, you should return `(error ,message)---giving some reasonable string error message.
; Handling errors and some trickier cases will give bonus points. 
(define (interp-ce exp)
  ; Might add helpers or other code here...
  (define (interp exp env)
    (match exp
      ;; hint: use hash-ref, look up x
      [(? symbol? x) (hash-ref env x (λ () `(error ,(format "unbound variable: ~a" x))))]
      ;; build a closure (see video lecture, or come to class)
      [`(lambda (,args ...) ,body) `(closure (lambda ,args ,body) ,env)]
      [`(lambda ,args ,body) `(closure (lambda ,args ,body) ,env)]
      ;; evaluate e-g, then branch...
      [`(if ,e-g ,e-t ,e-f)
       (if (interp e-g env)
           (interp e-t env)
           (interp e-f env))]
      ;; Here we have two separate patterns for let
      ;; (but you can change it if you want!)
      [`(let () ,e-body) (interp e-body env)]
      [`(let ([,x ,e0]) ,e-body)
       (let* ([val (interp e0 env)]
              [new-env (hash-set env x val)])
         (interp e-body new-env))]
      [`(let ([,xs ,es] ...) ,e-body)
       (let* ([vals (map (λ (e) (interp e env)) es)]
              [new-env (foldl (λ (k v h) (hash-set h k v)) env xs vals)])
         (interp e-body new-env))]
      ;; You might also want 2/3 patterns for let*
      [`(let* () ,e-body) (interp e-body env)]
      [`(let* ([,x ,e0] . ,rest) ,e-body)
       (let* ([val (interp e0 env)]
              [new-env (hash-set env x val)])
         (if (null? rest)
             (interp e-body new-env)
             (interp `(let* ,rest ,e-body) new-env)))]
      ;; polyadic and/or
      [`(and) #t]
      [`(and ,e0) (interp e0 env)]
      [`(and ,e0 ,e-rest ...)
       (if (interp e0 env)
           (interp `(and ,@e-rest) env)
           #f)]
      [`(or) #f]
      [`(or ,e0) (interp e0 env)]
      [`(or ,e0 ,e-rest ...)
       (let ([v (interp e0 env)])
         (if v v (interp `(or ,@e-rest) env)))]
      ;; literals are just themselves
      [(? number? n) n]
      [(? boolean? b) b]
      [''() '()]
      ;; application
      [`(,ef ,eargs ...)
       (let* ([f (interp ef env)]
              [args (map (λ (e) (interp e env)) eargs)])
         (match f
           [`(closure (lambda (,params ...) ,body) ,closure-env)
            (if (= (length params) (length args))
                (let ([new-env (foldl (λ (k v h) (hash-set h k v)) 
                                     closure-env params args)])
                  (interp body new-env))
                `(error "arity mismatch"))]
           [`(closure (lambda ,param ,body) ,closure-env)
            (let ([new-env (hash-set closure-env param args)])
              (interp body new-env))]
           
           [`(primitive ,op)
            (with-handlers ([exn:fail? (λ (e) `(error ,(exn-message e)))])
              (apply op args))]
           
           [_ `(error "not a function")]))]
      
      [_ `(error "invalid expression")]))

  ;; you need to cook up a starting environment: at first it can just
  ;; be the empty hash, but later on you may want to add things like
  ;; builtins here.
  (define prim-env
    (foldl (λ (op env) 
             (hash-set env op `(primitive ,(eval op (make-base-namespace)))))
           (hash)
           '(+ - * = equal? list cons car cdr null?)))

  (interp exp prim-env))
