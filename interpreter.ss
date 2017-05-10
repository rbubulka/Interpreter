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
       (list number? vector? boolean? symbol? string? pair? null? (lambda (x) (eqv? (void) x))))))]
  [app-exp        ; applications
   (rator expression?)
   (rands (list-of expression?))]
   ;Lets
  [let-exp 
    (vars (list-of symbol?))
    (vals (list-of expression?))
    (body (list-of expression?))]
  [let*-exp
   (vars (list-of symbol?))
   (vals (list-of expression?))
   (body (list-of expression?))]
  [named-let-exp 
   (name symbol?)
   (vars (list-of symbol?))
   (vals (list-of expression?))
   (body (list-of expression?))]
  [letrec-exp 
   (procs (list-of symbol?))
   (proc-vars (list-of (pair-of symbol?)))
   (proc-bodies (list-of (list-of expression?)))
   (body (list-of expression?))]
  [lambda-exp
   (vars (list-of symbol?))
   (body (list-of expression?))]
  [lambda-improp-exp
   (vars (list-of symbol?))
   (improps symbol?)
   (body (list-of expression?))]
   [lambda-ref-exp
    (varss (list-of symbol?))
    (refs list?)
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
    (var symbol?)
    (value expression?)]
  [define-exp
    (var symbol?)
    (body expression?)]
  [cond-exp 
   (conditions (list-of expression?))
   (thens (list-of expression?))]
  [and-exp
   (bodies (list-of expression?))]
  [or-exp
   (bodies (list-of expression?))]
  [begin-exp 
   (bodies (list-of expression?))]
  [case-exp 
   (tocompare expression?)
   (conditions (list-of expression?))
   (thens (list-of expression?))]
  [while-exp
   (condition expression?)
   (body (list-of expression?))]
  )

(define pair-of
  (lambda (pred?)
    (lambda (obj)
      (let loop ((obj obj))
  (if (null? obj)
      #t
      (if (pair? obj)
    (if (pred? (car obj))
        (loop (cdr obj))
        #f)
    (if (symbol? obj)
        #t
        #f)))))))

(define scheme-value?
  (lambda (x) #t))

(define cell? 
  (lambda (obj) 
    (box? obj)))
(define cell
  (lambda (val)
    (box val)))
(define cell-set!
  (lambda (cell val) 
    (set-box! cell val)))
(define cell-ref
  (lambda (cell)
    (unbox cell)))

(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of symbol?))
   (vals (list-of box?))
   (env environment?)]
  [recursively-extended-env-record
      (proc-names (list-of symbol?))
      (proc-vars (list-of (pair-of symbol?)))
      (proc-bodies (list-of (list-of expression?)))
      (env environment?)])

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

;Separate out into cases for more accurate checking
(define-datatype proc-val proc-val?
  [prim-proc
   (name (lambda (x) (list? (member x *prim-proc-names*))))]
  [proc
   (args (list-of symbol?))
   (bodies (list-of expression?))
   (envir environment?)]
  [improp-proc
   (args (list-of symbol?))
   (rest symbol?)
   (bodies (list-of expression?))
   (envir environment?)]
   [proc-ref
    (syms (lambda (x) (or ((list-of symbol?)x) (symbol? x) (pair? x))))
    (ref (list-of boolean?)) ;designeds which symbols are references
    (bodies (list-of expression?))
    (env environment?)]
   )
   
  

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
      [(eq? (void) datum) (lit-exp datum)]
      [(eqv? (1st datum) 'quote) (lit-exp (2nd datum))]
      [(pair? datum)
        (cond 
        ;[non primitive procedures will go here]
   [(eqv? (1st datum) 'begin)
          (begin-exp (map parse-exp (cdr datum)))]
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
      (named-let-exp (2nd datum) 
                      (map car variableseval) 
                      (map 2nd variableseval) 
                      (map parse-exp (cdddr datum))))
                      (eopl:error 'parse-exp "named-let must have a body: ~s" datum))))]  
   [(eqv? (car datum) 'letrec)
    (if (< (length datum) 3) (eopl:error 'parse-exp "lets must have at least a list of variables and a body: ~s" datum)
        (let [(variableseval
                 (map (lambda (x) (if (and (list? x) (=(length x) 2)) 
                          (if (symbol? (1st x)) 
                        (list (1st x) (2nd x)) 
                        (eopl:error 'parse-exp "all variables must be symbols ~s" datum))
                          (eopl:error 'parse-exp "all variable definitions must be list of size two" datum))) (2nd datum)))]
        (letrec-exp (map 1st variableseval) 
        (map (lambda (x) (if (eqv? (caadr x) 'lambda)(2nd (2nd x)) '())) variableseval);list of variables for the lambdas of the values of the letrecvariables
        (map (lambda (x) (if (eqv? (caadr x) 'lambda)
                 (map parse-exp (cddr (2nd x))) 
                 (map parse-exp (2nd x)))) variableseval)  ;after the variables shold be all the bodies 
        (map parse-exp (cddr datum)))))]
   [(eqv? (car datum) 'lambda)
          (if   (>= (length datum) 3)
    (cond
     [(null? (2nd datum)) (lambda-exp (2nd datum) (map parse-exp (cddr datum)))] 
     [(pair? (2nd datum))
      (let loop ([end (2nd datum)] [req '()]) 
        (if (null? (cdr end))
            (lambda-exp (2nd datum) (map parse-exp (cddr datum)))
            (if (ormap (lambda (x) (and (list? x) (eqv? (car x) 'ref))) end)
                (lambda-ref-exp
                    (get-ref-ids (2nd datum) '())
                    (refpos (cadr datum) '())
                    (map parse-exp (cddr datum)))
                (if (not (pair? (cdr end)))
                    (lambda-improp-exp (append req (list (car end))) (cdr end)  (map parse-exp (cddr datum)))
                    (loop (cdr end) (append req (list (car end))))))))]
     [else (if (symbol? (2nd datum))
         (lambda-improp-exp '() (2nd datum) (map parse-exp (cddr datum)))
         (eopl:error 'parse-exp "lambda variable must be a symbol"))])
    (eopl:error 'parse-exp "lambda expression too short: ~s" datum))]
   [(eqv? (1st datum) 'cond)
    (let ([conditions (map (lambda (x) (parse-exp (car x))) (cdr datum))]
    [thens (map (lambda (x) (parse-exp (2nd x))) (cdr datum))]) 
            (cond-exp conditions thens)
      )]
   [(eqv? (1st datum) 'case)
    (let ([bodies (let loop ([args (cddr datum)])
        (if (null? args) 
            '()
            (if (list? (1st (1st args)))
          (append (let loop2 ( [conditionlist (1st (1st args))]
                   [thencopy (list (parse-exp (2nd (1st args))))])
              (if (null? conditionlist) 
            '()
            (cons (list (parse-exp (car conditionlist)) thencopy) 
                  (loop2 (cdr conditionlist) thencopy)))) (loop (cdr args)))  
          (cons (list (parse-exp (car (1st args))) (list (parse-exp (2nd (1st args))))) (loop (cdr args))))))])
      (case-exp (parse-exp (2nd datum)) (map 1st bodies) (map caadr bodies)))]
   [(eqv? (1st datum) 'and)(and-exp (map parse-exp (cdr datum)))]
   [(eqv? (1st datum) 'or)(or-exp (map parse-exp (cdr datum)))]
   [(eqv? (car datum) 'set!)
            (set!-exp (cadr datum) (parse-exp (caddr datum)))]
   [(eqv? (car datum) 'define)
                (define-exp (2nd datum) (parse-exp (3rd datum)))]
   [(eqv? (1st datum) 'let*)
    (if (< (length datum) 3) 
        (eopl:error 'parse-exp "let*s must have at least a list of variables and a body: ~s" datum)
        (let [(variableseval
         (map (lambda (x) (if (and (list? x) (=(length x) 2)) 
            (if (symbol? (1st x)) 
                (list (1st x) (parse-exp (2nd x))) 
                (eopl:error 'parse-exp "all variables must be symbols ~s" datum))
            (eopl:error 'parse-exp "all variable definitions must be list of size two" datum))) (2nd datum)))]
    (let*-exp (map 1st variableseval) (map 2nd variableseval) (map parse-exp (cddr datum)))))]
   [(eqv? (1st datum) 'while) (while-exp (parse-exp (2nd datum)) (map parse-exp (cddr datum)))]
   [else (app-exp (parse-exp (1st datum)) (map parse-exp (cdr datum)))])]
    [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

(define get-ref-ids
  (lambda (args res)
    (cond
      [(null? args) (reverse res)]
      [(list? (car args)) (get-ref-ids (cdr args) (cons (cadr (car args)) res))]
      [else (get-ref-ids (cdr args) (cons (car args) res))])))

(define refpos
  (lambda (args res)
    (cond
      [(null? args) (reverse res)]
      [(list? (car args)) (refpos (cdr args) (cons #t res))]
      [else (refpos (cdr args) (cons #f res))])))


(define get-letrec-args
  (lambda (var varlist)
    (if (eq? (car var) (caar varlist))
  (list (car var))
  (cons (caar varlist) (get-letrec-args var (cdr varlist))))))

(define get-letrec-bodies
  (lambda (var varlist)
    (if (eq? (car var) (caar varlist))
  (list (cadr var))
  (cons (cadar varlist) (get-letrec-bodies var (cdr varlist))))))


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
    (extended-env-record syms (map cell vals) env)))

(define extend-env-recursively 
  (lambda (proc-names proc-vars proc-bodies old-env)[
    recursively-extended-env-record proc-names proc-vars proc-bodies old-env]))

(define extend-env-ref
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

(define list-set!
  (lambda (ls pos val)
    (if (zero? pos)
  (set-car! ls val)
  (list-set! (cdr ls) (- pos 1) val))))

(define apply-env
  (lambda (env sym succeed fail)
    (deref (apply-env-ref env sym succeed fail))))

(define deref (lambda (x) (if (cell? x) (cell-ref x) x)))

; (define apply-env
;   (lambda (e sym succeed fail)
;     (let ae ([tag 0] [ev e])
;       (cases environment ev      
;         [empty-env-record () 
;              (if (equal? tag 0)
;            (ae 1 init-env)
;            (fail))]
;         [extended-env-record (syms vals env)
;           (let ((pos (list-find-position sym syms)))
;             (if (number? pos)
;           (succeed (list-ref vals pos))
;           (ae tag env)))]
;         [recursively-extended-env-record (proc-names proc-vars proc-bodies old-env)
;           (let ([pos (list-find-position sym proc-names)])
;             (if (number? pos)
;     (if ((list-of symbol?) (list-ref proc-vars pos))
;         (proc (list-ref proc-vars pos)
;                           (list-ref proc-bodies pos) e)
;         (improp-proc (not-last-improp (list-ref proc-vars pos))
;          (get-last (list-ref proc-vars pos))
;          (list-ref proc-bodies pos) e))
;                 (apply-env old-env sym succeed fail)))]))))

(define apply-env-ref 
  (lambda (env sym succeed fail) 
    (cases environment env
      [empty-env-record ()
        (let ((pos (list-find-position sym (cadr global-env))))
          (if (number? pos)
              (succeed (list-ref (caddr global-env) pos))
              (fail)))]
      
      [extended-env-record (syms vals env)
        (let ((pos (list-find-position sym syms)))
          (if (number? pos)
              (succeed (list-ref vals pos))
              (apply-env-ref env sym succeed fail)))]
      
      [recursively-extended-env-record (proc-names proc-ids proc-bodies old-env)
        (let ((pos (list-find-position sym proc-names)))
          (if (number? pos)
              (succeed (cell (proc (list-ref proc-ids pos) (list-ref proc-bodies pos) env)))
              (apply-env-ref old-env sym succeed fail)))])))


(define list-find-position (lambda (sym ls)[cond
  [(null? ls) #f]
  [(eqv? sym (1st ls)) 0]
  [else (let ([pos (list-find-position sym (cdr ls))]) (if(number? pos) (add1 pos) pos))]
  ]))

(define not-last-improp
  (lambda (ls)
    (if (pair? ls)
  (cons (car ls) (not-last-improp (cdr ls)))
  '())))
  
  (define set-ref! cell-set!)
;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+

(define syntax-expand (lambda (exp)
  (cases expression exp
    [lit-exp (id) exp]
    [var-exp (id) exp]
    [app-exp (rator rands) (app-exp (syntax-expand rator) (map syntax-expand rands))]
    [let-exp (vars vals bodies) (app-exp (lambda-exp vars (map syntax-expand bodies)) (map syntax-expand vals))]
    [letrec-exp (procs proc-vars proc-bodies body) (letrec-exp procs proc-vars (map (lambda (x) (map syntax-expand x)) proc-bodies) (map syntax-expand body))]
    [lambda-exp (vars body) (lambda-exp vars (map syntax-expand body))]
    [lambda-improp-exp (vars improps body) (lambda-improp-exp vars improps (map syntax-expand body))]
    [if-exp (condit then-exp) (if-exp (syntax-expand condit) (syntax-expand then-exp))]
    [if-else-exp (condit then-exp else-exp) (if-else-exp (syntax-expand condit) (syntax-expand then-exp)(syntax-expand else-exp))]
    [set!-exp (setvars newval) (set!-exp setvars (syntax-expand newval))]
    [begin-exp (bodies) (syntax-expand (let-exp '() '() bodies))]
    [lambda-ref-exp (id refs body)
        (lambda-ref-exp id refs (map syntax-expand body))]
    [cond-exp (conditions thens) ;come back and fix in the event of no else statement
          (let loop ([remainingconds conditions] 
                      [remainingthens thens])
            (if (or (null? remainingconds) (equal? (1st remainingconds) (var-exp 'else)))
                (if (null? remainingconds) 
                    (lit-exp (void))
                    (syntax-expand (1st remainingthens))) 
                (if-else-exp (syntax-expand (1st remainingconds)) 
                             (syntax-expand (1st remainingthens)) 
                              (loop (cdr remainingconds) (cdr remainingthens)))))]
    

    [and-exp (bodies) (let loop ([remaining bodies])
                                (if (null? remaining) 
                                    (lit-exp #t)
                                    (let ([value (syntax-expand (1st remaining))])
                                          (syntax-expand (let-exp (list 'andvalue) (list value)
                                                    (list (if-else-exp (var-exp 'andvalue)
                                                                        (loop (cdr remaining))
                                                                        (var-exp 'andvalue))))))))]
    [or-exp (bodies) (let loop ([remaining bodies])
                                (if (null? remaining) 
                                    (lit-exp #f)
                                    (let ([value (syntax-expand (1st remaining))])
                                          (syntax-expand(let-exp (list 'orvalue) (list value)
                                              (list (if-else-exp (var-exp 'orvalue)
                                                                  (var-exp 'orvalue)
                                                                  (loop (cdr remaining)))))))))]
    [case-exp (tocompare conditions thens)(let loop ([remainingconds conditions]
                                                      [remainingthens thens])
                                          (if (null? (cdr remainingconds))
                                              (syntax-expand (1st remainingthens))
                                              (if-else-exp (app-exp (var-exp 'eqv?) (list (syntax-expand tocompare) (syntax-expand (1st remainingconds))))
                                                            (syntax-expand (1st remainingthens))
                                                            (loop (cdr remainingconds) (cdr remainingthens)))))]
    [let*-exp (vars vals bodies) (let loop ([var vars] [val vals])
           (if (null? (cdr var))
               (app-exp (lambda-exp (list (car var)) (map syntax-expand bodies)) (list (syntax-expand (car val))))
               (app-exp (lambda-exp (list (car var)) (list (loop (cdr var) (cdr val)))) (list (syntax-expand (car val))))))] 
    [named-let-exp (name vars vals bodies) (syntax-expand (letrec-exp (list name) (list vars) (list bodies) (list (app-exp (var-exp name) vals))))]
    [define-exp (var body)
        (define-exp var (syntax-expand body))]
    [else exp]
    )))



;-------------------+
;                   |
;   INTERPRETER     |
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
         [args (eval-rands rands env)])
     (if (proc-val? proc-value)
         (apply-proc proc-value args env)
         (eopl:error 'eval-exp "Rator is not a procedure: ~a" rator)))]
      [if-else-exp (condition then-exp else-exp) (if (eval-exp condition env) (eval-exp then-exp env) (eval-exp else-exp env))]
      [if-exp (condition then-exp) (if (eval-exp condition env) (eval-exp then-exp env))]
      [lambda-exp (vars bodies) (proc vars bodies env)]
      [lambda-improp-exp (vars improps bodies) (improp-proc vars improps bodies env)]
      [lambda-ref-exp (vars isrefs bodies)  (proc-ref vars isrefs bodies env)]
      [letrec-exp (procs proc-vars proc-bodies body)
              (get-last (eval-rands body (extend-env-recursively procs proc-vars proc-bodies env)))]
      [while-exp (condition bodies)
                    (if (eval-exp condition env)
                        (begin (map-first (lambda (x) (eval-exp x env)) bodies) 
                                (eval-exp exp env)))]
      [define-exp (var val)
	(apply-env-ref env var (lambda (x) (cell-set! x (eval-exp val env)))
		       (lambda () (set! global-env (cases environment global-env
							  (extended-env-record (syms vals old-env)
									       (extended-env-record (cons var syms)
												    (map cell (cons (eval-exp val env) (map unbox vals)))
												    old-env))
							  (else (eopl:error 'define-exp "Bad global environment"))))))]
      [set!-exp (var body)
          (set-box!
            (apply-env-ref env var (lambda (x) x) (lambda () (eopl:error "inputvariable not located")))
            (eval-exp body env))]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

(define map-first
  (lambda (f x)
    (let ([val (f (car x))])
      (if (null? (cdr x))
    (list val)
    (cons val (map-first f (cdr x)))))))


(define get-last
  (lambda (x)
    (if (symbol? x)
  x
  (if (null? (cdr x))
      (car x)
      (get-last (cdr x))))))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-exp x env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args env)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args env)]
      ; You will add other cases
      [proc (xs bodies envir)
      (let loop ([bds bodies] [xp (extend-env xs args envir)])
        (if (null? (cdr bds))
              (eval-exp (car bds) xp)
              (begin (eval-exp (car bds) xp)
               (loop (cdr bds) xp))))]
      [improp-proc (x rest bodies envir)
       (let loop ([bds bodies] [xp (let loop1 ([xs x] [as args] [vars '()] [vals '()])
             (if (null? xs)
                 (extend-env (append vars (list rest)) (append vals (list as)) envir)
                 (loop1 (cdr xs) (cdr as) (append vars (list (car xs))) (append vals (list (car as))))))])
         (if (null? (cdr bds))
       (eval-exp (car bds) xp)
       (begin (eval-exp (car bds) xp)
        (loop (cdr bds) xp))))]
       [proc-ref (syms isrefs bodies enviro)
        (let* ([nonrefs (get-non-refd-syms syms isrefs '())]
                [refsyms (get-refd-syms syms isrefs '())]
                [partial-enviro 
                  (extend-env nonrefs 
                      (eval-rands (get-non-refd-syms args isrefs '()) env) enviro)]
                [complete-envior 
                  (extend-env-ref 
                    refsyms 
                    (map (lambda (x) 
                      (apply-env-ref env (2nd x) 
                        (lambda (x) x) 
                        (lambda () eop:error 'apply-env "var not fount")))
                    (get-refd-syms args isrefs '()))
                    partial-enviro)])
        (map-first (lambda (x) (eval-exp x complete-envior) body)))]
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))


(define get-refd-syms
  (lambda (syms isrefs res)
    (cond
      [(null? syms) (reverse res)]
      [(car isrefs) (get-refd-syms (cdr syms) (cdr isrefs) (cons (car syms) res))]
      [else (get-refd-syms (cdr syms) (cdr isrefs) res)])))

(define get-non-refd-syms
  (lambda (syms isrefs res)
    (cond
      [(null? syms) (reverse res)]
      [(car isrefs) (get-non-refd-syms (cdr syms) (cdr isrefs) res)]
      [else (get-non-refd-syms (cdr syms) (cdr isrefs) (cons (car syms) res))])))

(define *prim-proc-names* '(+ - * / add1 sub1 zero? not = < > <= >= cons car cdr 
                              list null? assq eq? eqv? equal? atom? length list->vector
                              list? pair? procedure? vector->list vector make-vector 
                              vector-ref vector? number? symbol? set-car! set-cdr! 
                              vector-set! display newline caar cadr cdar cddr
                              caaar caadr cadar cdaar caddr cdadr cddar cdddr apply map quotient append list-tail))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))

(define global-env init-env)

(define reset-global-env
  (lambda () (set! global-env
    (extend-env
      *prim-proc-names*
      (map prim-proc
        *prim-proc-names*)
      (empty-env)))))


; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args env)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (/ (1st args) (2nd args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(append) (append (1st args) (2nd args))]
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
      [(assq) (apply assq args)] 
      [(eq?) (eq? (1st args) (2nd args))]
      [(eqv?) (eqv? (1st args) (2nd args))] 
      [(equal?) (equal? (1st args) (2nd args))] 
      [(atom?) (atom? (1st args))] 
      [(length) (length (1st args))] 
      [(list->vector)(list->vector (1st args))]
      [(list?)(list? (1st args))]
      [(pair?)(pair? args)]
      [(procedure?)(or (proc-val? (1st args)) (procedure? (1st args)))]
      [(vector->list)(vector->list (1st args))] 
      [(vector)(apply vector args)] 
      [(make-vector)(make-vector (1st args))]
      [(vector-ref)(vector-ref (1st args) (2nd args))]
      [(vector?) (vector? (1st args))] 
      [(number?)(number? (1st args))] 
      [(symbol?)(symbol? (1st args))] 
      [(set-car!) (apply set-car! args)]
      [(set-cdr!) (apply set-car! args)]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
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
      [(map) (map (lambda (x) (apply-proc (1st args) (list x) env)) (2nd args))]
      [(apply) (apply-proc (1st args) (2nd args) env)]
      [(quotient) (quotient (1st args) (2nd args))]
      [(list-tail) (apply list-tail args)]
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (syntax-expand (parse-exp (read))) (empty-env))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)) (empty-env))))
