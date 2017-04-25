;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss") 

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression

(define-datatype expression expression?  
  [var-exp        ; variable references
   (id symbol?)]
  [lit-exp        ; "Normal" data.  Did I leave out any types?
   (datum
    (lambda (x)
      (ormap 
       (lambda (pred) (pred x))
       (list number? vector? boolean? symbol? string? pair? null?))))]
  [app-exp        ; applications
   (rator expression?)
   (rands (list-of expression?))]
   ;Lets
   [let-exp 
    (vars (list-of symbol?))
    (vals (list-of expression?))
    (body (list-of expression?))]
  [named-let-exp 
    (name symbol?)
    (vars (list-of symbol?))
    (vals (list-of expression?))
    (body (list-of expression?))]
   [letrec-exp 
    (vars (list-of symbol?))
    (vals (list-of expression?))
    (body (list-of expression?))]
   [let*-exp
   (vars (list-of symbol?))
   (vals (list-of expression?))
   (body (list-of expression?))]
   ;Lambdas Need to come back and do the improper list lambda
   [lambda-exp
    (vars (list-of symbol?))
    (body (list-of expression?))]
   ;Ifs
   [if-exp
    (condition expression?)
    (then-exp expression?)]
   [if-else-exp
    (condition expression?)
    (then-exp expression?)
    (else-exp expression?)] 
   ;set
   [set!-exp
    (setvars symbol?)
    (newval expression?)]
  )

	
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)))

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

;Separate out into cases for more accurate checking
(define-datatype proc-val proc-val?
  [prim-proc
   (name (lambda (x) (list? (member x *prim-proc-names*))))]
  [proc
   (args (list-of symbol?))
   (bodies (list-of expression?))])
	 
	

;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

(define var-exp?
 (lambda (x)
   (cases expression x
     [var-exp (id) #t]
     [else #f])))
(define let-exp?
  (lambda (x)
    (cases expression x
	   [let-exp (vars vals bodies) #t]
	   [else #f])))


(define parse-exp         
  (lambda (datum)
    (cond
      [(null? datum) (lit-exp datum)]
      [(symbol? datum) (var-exp datum)]
      [(number? datum) (lit-exp datum)]
      [(boolean? datum) (lit-exp datum)]
      [(vector? datum) (lit-exp datum)]
      [(string? datum) (lit-exp datum)]
      [(eqv? (1st datum) 'quote) (lit-exp (2nd datum))]
      [(pair? datum)
        (cond 
        ;[non primitive procedures will go here]
        [(eqv? (1st datum) 'if)
          (cond [(= (length datum) 4)
                    (if-else-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (4th datum)))]
                [(= (length datum) 3)
                    (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))]
                [else (eopl:error 'parse-exp "invalid if statment: ~s" datum)])]
        [(eqv? (car datum) 'let)
            (if (< (length datum) 3) 
                (eopl:error 'parse-exp "lets must have at least a list of variables and a body: ~s" datum)
                (if (list? (2nd datum)) 
                  (let [(variableseval
                              (map (lambda (x) (if (and (list? x) (=(length x) 2)) 
                                                    (if (symbol? (1st x)) 
                                                        (list (1st x) (parse-exp (2nd x))) 
                                                        (eopl:error 'parse-exp "all variables must be symbols ~s" datum))
                                                    (eopl:error 'parse-exp "all variable definitions must be list of size two" datum))) (2nd datum)))]
                        (let-exp (map 1st variableseval) (map 2nd variableseval) (map parse-exp (cddr datum))))
                  (if (> (length datum) 3) 
                      (let [ (variableseval
                                (map (lambda (x) (if (and (list? x) (=(length x) 2)) 
                                                     (if (symbol? (1st x)) 
                                                         (list (1st x) (parse-exp (2nd x)))
                                                         (eopl:error 'parse-exp "all variables must be symbols: ~s" datum))
                                                      (eopl:error 'parse-exp "all variable definitions must be list of size two: ~s" datum))) (3rd datum))) ]
                            ( named-let-exp (2nd datum) (map car variableseval) (map 2nd variableseval) (map parse-exp (cddr datum))))
                      (eopl:error 'parse-exp "named-let must have a body: ~s" datum))))]     
        [(eqv? (car datum) 'lambda)
          (if   (>= (length datum) 3)
             (cond
              [(null? (2nd datum)) (lambda-exp (2nd datum) (map parse-exp (cddr datum)))] 
              [(list? (2nd datum)) 
                (if ((list-of symbol?) (2nd datum)) 
                    (lambda-exp (2nd datum) (map parse-exp (cddr datum)))
                    (eopl:error 'parse-exp "all variables must be symbols: ~s" datum))]
              [else (if (symbol? (2nd datum))
			(lambda-exp (2nd datum) (map parse-exp (cddr datum)))
                    (eopl:error 'parse-exp "lambda variable must be a symbol"))])
	     (eopl:error 'parse-exp "lambda expression too short: ~s" datum))]
        [else (app-exp (parse-exp (1st datum)) (map parse-exp (cdr datum)))])]
      [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))


;-------------------+
;                   |
;    UNPARSER       |
;                   |
;-------------------+
 
(define unparse-exp
  (lambda (exp)
    (cases expression exp
      [var-exp (id) id]
      [lit-exp (id) id]
      [lambda-exp (vars body)
        (if(list? vars)
        (append 'lambda (map unparse-exp vars) (unparse-exp body))
        (append 'lambda (list (unparse-exp vars)) (unparse-exp body)))]
      [app-exp (rator rand)
        (if (list? rand) 
            (cons (unparse-exp rator) (unparse-exp rand))
            (cons (unparse-exp rator) (list (unparse-exp rand))))]
       [if-exp (condition then-exp) (list 'if (unparse-exp condition) (unparse-exp then-exp))]
       [if-else-exp (condition then-exp else-exp)(list 'if (unparse-exp condition) (unparse-exp then-exp) (unparse-exp else-exp))]
       [let-exp (vars vals bodies) 
          (list 'let
          (map (lambda (x y) (list (unparse-exp x) (unparse-exp y))) vars vals)
          (unparse-exp bodies))]
       [named-let-exp (name vars vals bodies)
          (list 'let name
          (map (lambda (x y) (list (unparse-exp x) (unparse-exp y))) vars vals)
          (unparse-exp bodies))]
       [let*-exp (vars vals bodies) 
          (list 'let*
          (map (lambda (x y) (list (unparse-exp x) (unparse-exp y))) vars vals)
          (unparse-exp bodies))]
       [letrec-exp (vars vals bodies)
          (list 'letrec
          (map (lambda (x y) (list (unparse-exp x) (unparse-exp y))) vars vals)
          (unparse-exp bodies))]
       [set!-exp (setvars newval) (list 'set! (unparse-exp setvars) (unparse-exp newval))]
    )))



;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+





; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define apply-env
  (lambda (e sym succeed fail)
    (let ae ([tag 0] [ev e])
      (cases environment ev      
	     [empty-env-record () 
			       (if (equal? tag 0)
				   (ae 1 init-env)
				   (fail))]
	     [extended-env-record (syms vals env)
				  (let ((pos (list-find-position sym syms)))
				    (if (number? pos)
					(succeed (list-ref vals pos))
					(ae tag env)))]))))








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



; To be added later









;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form env)
    ; later we may add things that are not expressions.
    (eval-exp form env)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
	       (apply-env env id; look up its value.
			  (lambda (x) x) ; procedure to call if it is in the environment 
			  (lambda () (eopl:error 'apply-env ; procedure to call if it is not in env
		          "variable not found in environment: ~s"
			   id)))] 
      [app-exp (rator rands)
	       (let ([proc-value (eval-exp rator env)]
		     [var (if (var-exp? (car rands)) (unparse-exp (car rands)) (car rands))]
		     [args (eval-rands rands env)])
		 (if (proc-val? proc-value)
		     (apply-proc proc-value args var env)
		     (eopl:error 'eval-exp "Rator is not a procedure: ~a" rator)))]
      [if-else-exp (condition then-exp else-exp) (if (eval-exp condition exp) (eval-exp then-exp env) (eval-exp else-exp env))]
      [if-exp (condition then-exp) (if (eval-exp condition) (eval-exp then-exp env))]
      [lambda-exp (vars bodies) (proc vars bodies)]
      [let-exp (vars vals bodies) (get-last (map-first (lambda (x) (eval-exp x (extend-env vars (let loop ([v vals]) 
								      (if (null? v)
									  '()
									  (cons (eval-exp (1st v) env) (loop (cdr v))))) 
							       env))) bodies))]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

(define map-first
  (lambda (f x)
    (let loop ([val (f (car x))])
      (if (null? (cdr x))
	  (list val)
	  (cons val (map-first f (cdr x)))))))

(define get-last
  (lambda (x)
    (if (null? (cdr x))
	(car x)
	(get-last (cdr x)))))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-exp x env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args var env)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args var env)]
			; You will add other cases
      [proc (xs bodies)
	    (let loop ([bds bodies])
	      (if (null? (cdr bds))
		  (eval-exp (car bds) (extend-env xs args env))
		  (begin (eval-exp (car bds) (extend-env xs args env))
			 (loop (cdr bds)))))]
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 zero? not = < > <= >= cons car cdr 
                              list null? assq eq? equal? atom? length list->vector
                              list? pair? procedure? vector->list vector make-vector 
                              vector-ref vector? number? symbol? set-car! set-cdr! 
                              vector-set! display newline caar cadr cdar cddr
                              caaar caadr cadar cdaar caddr cdadr cddar cdddr ))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args var env)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (/ (1st args) (2nd args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [(zero?) (zero? (1st args))]
      [(not) (not (1st args))]
      [(<) (< (1st args) (2nd args))] 
      [(>) (> (1st args) (2nd args))] 
      [(<=) (<= (1st args) (2nd args))] 
      [(>=) (>= (1st args) (2nd args))] 
      [(car) (car (1st args))]
      [(cdr) (cdr (1st args))]
      [(list) args]
      [(null?) (null? (1st args))] 
      [(assq) (assq (1st args) (2nd args))] 
      [(eq?) (eq? (1st args) (2nd args))] 
      [(equal?) (equal? (1st args) (2nd args))] 
      [(atom?) (atom? (1st args))] 
      [(length) (length (1st args))] 
      [(list->vector)(list->vector (1st args))]
      [(list?)(list? (1st args))]
      [(pair?)(pair? args)]
      [(procedure?)(or (proc-val? (1st args)) (procedure? (1st args)))]
      [(vector->list)(vector->list (1st args))] 
      [(vector)(vector args)] 
      [(make-vector)(make-vector (1st args))]
      [(vector-ref)(vector-ref (1st args) (2nd args))]
      [(vector?) (vector? (1st args))] 
      [(number?)(number? (1st args))] 
      [(symbol?)(symbol? (1st args))] 
      [(set-car!) (apply-env env var (lambda (x) (set-car! x (2nd args)))
			    (lambda (x) (eopl:error 'set-car! "~s is not defined in environment." var)))]
      [(set-cdr!) (apply-env env var (lambda (x) (set-cdr! x (2nd args)))
			    (lambda (x) (eopl:error 'set-cdr! "~s is not defined in environment." var)))]
      [(vector-set!) (apply-env env var (lambda (x) (vector-set! x (2nd args) (3rd args)))
			       (lambda (x) (eopl:error 'vector-set! "~s is not defined in environment." var)))]
      [(display)(display (1st args))] 
      [(newline)(newline)] 
      [(caar) (caar (1st args))]
      [(cadr) (cadr (1st args))]
      [(cdar) (cdar (1st args))]
      [(cddr) (cddr (1st args))]
      [(caaar) (caaar (1st args))]
      [(caadr) (caadr (1st args))]
      [(cadar) (cadar (1st args))]
      [(cdaar) (cdaar (1st args))]
      [(caddr) (caddr (1st args))]
      [(cdadr) (cdadr (1st args))]
      [(cddar) (cddar (1st args))]
      [(cdddr) (cdddr (1st args))]
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)) (empty-env))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x) (empty-env))))









