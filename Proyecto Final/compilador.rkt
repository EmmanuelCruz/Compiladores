#lang nanopass

;; Módulo para tener un contador. 
(module m racket
    (provide counter increment!)
    (provide counter clean!)
    ;; Función que inicia el contador. 
    (define counter 0)
    ;; Función que aumenta en uno el contador. 
    (define (increment!)
      (set! counter (add1 counter)))
    ;; Función que reinicia el contador. 
    (define (clean!)
      (set! counter 0)))

;; Adquirimos modulos necesarios. 
(require nanopass/base)
(require racket/set)
(require 2htdp/batch-io)
(require 'm)

;;PREDICADOS

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))
(define (primitive? x) (memq x '(+ - * / length car cdr and or not < > equal? iszero? ++ --)))
(define (primitivePA? x) (memq x '(+ - * / length car cdr and or not < > equal?)))
(define (primitiveN? x) (memq x '(+ - * / length car cdr < > equal?)))
(define (len? x) (integer? x))
(define (arit? x) (memq x '(+ - * / < > equal?)))
(define (lst? x) (memq x '(length car cdr)))

(define (constant? x)
  (or (integer? x)
      (char? x)
      (boolean? x)))
      
;; SISTEMA DE TIPOS

;; Int | Char | Bool | Lambda | List | (List of T) | (T → T) | Void
(define (type? x) (or (b-type? x) (c-type? x)))
;;Verifica si es un tipo basico
(define (b-type? x) (memq x '(Bool Char Int List String Lambda Void)))
;; Verifica si es un tipo compuesto
(define (c-type? x) (if (list? x) 
  (let* (
    [f (car x)]
    [s (cadr x)]
    [t (caddr x)])
  (or (and (equal? f 'List) (equal? s 'of) (type? t)) 
    (and (type? f) (equal? s '→) (type? t))))
  #f))

;; Función que verifica si dos tipos son unificables, para mas detalle consultar 
;; la especificación.
(define (unify t1 t2)
  (if (and (type? t1) (type? t2))
    (cond 
      [(equal? t1 t2) #t]
      [(and (equal? 'List t1) (list? t2)) (equal? (car t2) 'List)]
      [(and (equal? 'List t2) (list? t1)) (equal? (car t1) 'List)]
      [(and (list? t1) (list? t2)) (and (unify (car t1) (car t2)) (unify (caddr t1) (caddr t2)))]
      [else #f])
    (error "Se esperaban 2 tipos")))

;; Encuentra el tipo mas particular de una lista de tipos. Para la inferencia de las listas.
(define (part lst)
  (if (equal? (car lst) 'List)
    (part (cdr lst))
    (car lst)))
    
;;LENGUAJES
            
;Lenguaje Fuente
(define-language LF
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (list (l))
   (string (s))
   (type (t)))
  (Expr (e body)
    x
    c
    l
    s
    pr
    (begin e* ... e)
    (if e0 e1)
    (if e0 e1 e2)
    (for [x e0] e1)
    (while [e0] e1)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (list e* ...)
    (e0 e1 ...)
    (define x e)))

;Lenguaje en el que se sustituye las multiples expresiones en el cuerpo de
;lambda, let y letrec por una única expresión begin
(define-language L0
  (extends LF)
  (Expr (e body)
        (- (lambda ([x* t*] ...) body* ... body)
           (let ([x* t* e*] ...) body* ... body)
           (letrec ([x* t* e*] ...) body* ... body))
        (+ (lambda ([x* t*] ...) body)
           (let ([x* t* e*] ...) body)
           (letrec ([x* t* e*] ...) body))))

;; Definición del lenguaje L1 para eliminar los if then . 
(define-language L1
  (extends L0)
  (terminals)
  (Expr (e body)
    (- (if e0 e1)))
)

;; Definimos el lenguaje L3 para eliminar los Strings del lenguaje. 
(define-language L3
  (extends L1)
  (terminals
   (- (string (s))))
  (Expr (e body)   
    (- s)))

;; Definición del lenguaje L4 para eliminar las operaciones ++, -- e iszero?. 
(define-language L4PA
  (extends L3)
  (terminals
   (- (primitive (pr)))
   (+ (primitivePA (prA))))
  (Expr (e body)
    (- pr)
    (+ prA)))

;; Definición del lenguaje L4 para eliminar las operaciones booleanas. 
(define-language L4
  (extends L4PA)
  (terminals
   (- (primitivePA (prA)))
   (+ (primitiveN (prN))))
  (Expr (e body)
    (- prA)
    (+ prN)))

;; Definición del lenguaje L5 para añadir primapp. 
(define-language L5
  (extends L4)
  (terminals)
  (Expr (e body)
    (- prN)
    (+ (primapp prN e* ...))))

;; Definición del lenguaje L6 con un nuevo constructor. 
(define-language L6
  (extends L5)
  (terminals)
  (Expr (e body)
    (- c)
    (+ (cuote c))))

;; Definición del lenguaje L7 con un nuevo constructor. 
(define-language L7
  (extends L6)
  (terminals)
  (Expr (e body)
    (- (let ([x* t* e*] ...) body)
       (letrec ([x* t* e*] ...) body))
    (+ (let ([x t e]) body)
       (letrec ([x t e]) body))))

;; Definición del lenguaje L8 con un nuevo constructor. 
(define-language L8
  (extends L7)
  (terminals)
  (Expr (e body)
    (+ (letfun ([x t e]) body))))

;; Definición del lenguaje L9 con nuevos constructores. 
(define-language L9
  (extends L8)
  (terminals)
  (Expr (e body)
    (- (lambda ([x* t*] ...) body)
       (e0 e1 ...))
    (+ (lambda ([x t]) body)
       (e0 e1))))

;; Definición del lenguaje L10 con nuevos constructores. 
(define-language L10
  (extends L9)
  (terminals)
  (Expr (e body)
    (- (cuote c))
    (+ (const t c))))

;; Definición del lenguaje L11 con nuevos constructores. 
(define-language L11
  (extends L10)
  (terminals)
  (Expr (e body)
    (- (lambda ([x t]) body)
        (e0 e1))
    (+ (lambda ([x* t*]...) body)
        (e0 e1 ...))))

;; Definición del lenguaje L13 con nuevos constructores. 
(define-language L13
  (extends L11)
  (terminals
   (+ (len (le))))
  (Expr (e body)
    (- (list e* ...))
    (+ (array le t (e ...)))))
   
;; PARSERS

(define-parser parser-LF LF)
(define-parser parser-L0 L0)
(define-parser parser-L1 L1)
(define-parser parser-L3 L3)
(define-parser parser-L4PA L4PA)
(define-parser parser-L4 L4)
(define-parser parser-L5 L5)
(define-parser parser-L6 L6)
(define-parser parser-L7 L7)
(define-parser parser-L8 L8)
(define-parser parser-L9 L9)
(define-parser parser-L10 L10)
(define-parser parser-L11 L11)
(define-parser parser-L13 L13)

;; PROCESOS

;Proceso que cambia el cuerpo de lambda, let y letrec por un begin.
(define-pass make-explicit : LF (ir) -> L0 ()
  (Expr : Expr (ir) -> Expr ()
    [(lambda ([,x* ,t*] ...) ,[body*] ... ,[body])
     `(lambda ([,x* ,t*] ...) (begin ,body* ... ,body))]
    [(let ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]))
    
;; Definción del proceso que elimina los if con dos parametros. 
(define-pass remove-one-armed-if : L0 (ir) -> L1 ()
  (Expr : Expr (ir) -> Expr()
    [(if ,[e0] ,[e1]) `(if ,e0 ,e1 (void))]))

;; Verifica si es un tipo compuesto
(define (tipoLista? x) (if (list? x) 
  (let* (
    [f (car x)]
    [s (cadr x)]
    [t (caddr x)])
  (and (equal? f 'List) (equal? s 'of) (type? t)))
  #f))
    
;; Definición del proceso para eliminar las cadenas y convertirlos en listas de chars. 
(define-pass remove-string : L1 (ir) -> L3 ()
  (Expr : Expr (ir) -> Expr()
    ;[,s (parser-L3 (append (list 'list) (remove* (list #\space) (string->list s))))]))
    [,s (parser-L3 (append (list 'list) (string->list s)))]))

;; Definición del proceso para eliminar las primitivas ++, --, iszero?. 
(define-pass remove-primA : L3 (ir) -> L4PA ()
  (definitions 
    (define (primitive p)
      p))
  (Expr : Expr (ir) -> Expr()
    [,pr (if (memq pr '(++ -- iszero?)) #t (primitive pr))]
    [(,e0 ,e1 ...) (cond
                       [(equal? e0 '++) `(+ ,(car e1) 1)]
                       [(equal? e0 '--) `(- ,(car e1) 1)]
                       [(equal? e0 'iszero?) `(equal? ,(car e1) 0)]
                       ;[else `(,(parser-L4PA (unparse-L3 e0)) ,e1)]
                       [else (parser-L4PA (unparse-L3 ir))])]))

;; Definición del proceso que sustituye las operaciones booleanas
;; por equivalencias de ifs. 
(define-pass remove-logical-operators : L4PA (ir) -> L4 ()
  (definitions
    ;; Función que genera los ifs que sustituyen a la operación or, donde lst es una lista de
    ;; expresiones. 
    (define (generarOr lst)
      (if (= (length lst) 0) #t
      (if (= (length lst) 1) (unparse-L4 (list-ref lst 0))
          (if (= (length lst) 2) `(if ,(unparse-L4 (list-ref lst 0)) #t ,(unparse-L4 (list-ref lst 1)))
                                  `(if ,(unparse-L4 (list-ref lst 0)) #t ,(generarOr (list-tail lst 1)))))))
    ;; Función que genera los ifs que sustituyen a la operación and, donde lst es una lista de
    ;; expresiones. 
    (define (generarAnd lst)
      (if (= (length lst) 0) #t
      (if (= (length lst) 1) (unparse-L4 (list-ref lst 0))
          (if (= (length lst) 2) `(if ,(unparse-L4 (list-ref lst 0)) ,(unparse-L4 (list-ref lst 1)) #f)
                                  `(if ,(unparse-L4 (list-ref lst 0)) ,(generarAnd (list-tail lst 1)) #f)))))
    ;; Función que genera los ifs que sustituyen a la operación not, donde lst es una lista de
    ;; expresiones. 
    (define (generarNot lst)
      (if (= (length lst) 0) #t
          `(if ,(generarOr lst) #f #t)))
    ;; Función que regresa el valor de la primitiva.
    (define (ret prim)
      prim)
    )  
  (Expr : Expr (ir) -> Expr()
    [,prA (if (memq prA '(or and not)) `#t
             `,(ret prA))]
    [(,e0 ,[e1] ...) (if (equal? e0 'or) (parser-L4 (generarOr e1))
                         (if (equal? e0 'and) (parser-L4 (generarAnd e1))
                             (if (equal? e0 'not) (parser-L4 (generarNot e1))
                             `(,(remove-logical-operators e0) ,e1 ...))))]))

;; Currifica las expresiones primitivas
(define-pass curry-prim : L4 (ir) -> L4 ()
  (definitions
    (define (gen cad expr op)
      (for ([i expr])
       (set! cad (list op cad (unparse-L4 i))))
       (parser-L4 cad)))
  (Expr : Expr (ir) -> Expr()
    [(,e0 ,[e1] ...) (if (primitiveN? e0)
                             (if (or (= (length e1) 1) (= (length e1) 2)) ir
                             (gen (list e0 (unparse-L4 (car e1)) (unparse-L4 (cadr e1))) (cddr e1) e0))
                         `(,(curry-prim e0) ,e1 ...))]))

;; Diccionario con los tipos correspondientes a cada primitiva. 
(define ht #hash((+ . Int)
                 (- . Int)
                 (* . Int)
                 (/ . Int)
                 (< . Int)
                 (> . Int)
                 (equal? . Int)
                 (length . List)
                 (car . List)
                 (cdr . List)))

;; Definción del proceso que añade lambdas cada vez que ve una primitiva. 
(define-pass eta-expand : L4 (ir) -> L5 ()
  (definitions
    ;; Función para actualizar el contador de la variable xn. 
    (define (update)
      (increment!)
      (string->symbol (string-append "x" (number->string counter))))
    ;; Función para obtener variables nuevas para la lambda. 
    (define (newVar valores)
      (define v '())
      (for ([i valores])
        (set! v (append v (list (update)))))
      v)
    ;; Función para obtener una lista de tipos de tamaño dependiendo de
    ;; la lista de valores. 
    (define (tipos valores op)
      (define v '())
      (for ([i valores])
        (set! v (append v (list (hash-ref ht op)))))
      v)
    )
  (Expr : Expr (ir) -> Expr()
    [,prN
     (if (memq prN '(+ - * / < > equal?))
            (let ([varT (newVar (list "x" "y"))]) `(lambda ([,varT ,(tipos varT prN)] ...) (primapp ,prN ,varT ...)))
            (let ([varL (newVar (list "x"))]) `(lambda ([,varL ,(tipos varL prN)] ...) (primapp ,prN ,varL ...))))]
    [(,e0 ,[e1] ...)
     (if (primitiveN? e0)
        (let ([variables (newVar e1)]) `((lambda ([,variables ,(tipos e1 e0)] ...) (primapp ,e0 ,variables ...)) ,e1 ...))
       `(,(eta-expand e0) ,e1 ...))]))

;; Definición del proceso que añade el constructor nuevo a las constantes. 
(define-pass quote-const : L5 (ir) -> L6 ()
  (Expr : Expr (ir) -> Expr()
    [,c `(cuote ,c)]))
    
;; Definción del proceso que añade let a letrec si es necesario. 
(define-pass purify-recursion : L6 (ir) -> L6 ()
  (definitions
    ;; Obtiene una lista de expresiones dependiendo del tipo.
    (define (obtC var type find)
      (define v '())
      (if find
          (for ([i var] [t type])
            (if (equal? t 'Lambda) (set! v (append v (list i)))
            4))
          (for ([i var] [t type])
            (if (not (equal? t 'Lambda)) (set! v (append v (list i)))
            4)))
      v)
    )
  (Expr : Expr (ir) -> Expr()
    [(letrec ([,x* ,t* ,[e*]] ...) ,[body])
     (if (equal? (length (obtC t* t* #f)) 0)
         `(letrec ([,x* ,t* ,e*] ...) ,body)
         (if (equal? (length (obtC t* t* #t)) 0)
             `(let ([,x* ,t* ,e*] ...) ,body)
             `(letrec ([,(obtC x* t* #t) ,(obtC t* t* #t) ,(obtC e* t* #t)] ...) (let ([,(obtC x* t* #f) ,(obtC t* t* #f) ,(obtC e* t* #f)] ...) ,body))))]))

;; Definción del proceso que traduce de una aplicación de función a una expresión let. 
(define-pass direct-app : L6 (ir) -> L6 ()
  (Expr : Expr (ir) -> Expr()
    [((lambda ([,x* ,t*] ...) ,[body]) ,[e1] ...)
     `(let ([,x* ,t* ,e1] ...) ,body)]))
     
;; Definción del proceso que currifica una expresión let o letrec.  
(define-pass curry-let : L6 (ir) -> L7 ()
  (definitions
    ;; Función que va obteniendo el primer elemento de las listas recibidas, y genera una expresión
    ;; utilizando el operador opd. 
    (define (curryA var type exp body opd)
      (if (= (length var) 0)
          `,(unparse-L7 body)
          `(,opd ([,(list-ref var 0) ,(list-ref type 0) ,(unparse-L7 (list-ref exp 0))])
             ,(curryA (list-tail var 1) (list-tail type 1) (list-tail exp 1) body opd))) 
      ))
  (Expr : Expr (ir) -> Expr()
    [(let ([,x* ,t* ,[e*]] ...) ,[body])
      (parser-L7 (curryA x* t* e* body 'let))]
    [(letrec ([,x* ,t* ,[e*]] ...) ,[body])
     (parser-L7 (curryA x* t* e* body 'letrec))]))
     
;; Definción del proceso que añade let a letrec si es necesario. 
(define-pass indentify-assigments : L7 (ir) -> L7 ()
  (Expr : Expr (ir) -> Expr()
    [(let ([,x ,t ,[e]]) ,[body])
     (if (equal? t 'Lambda)
         `(letrec ([,x ,t ,e]) ,body)
         ir)]))
   
;; Contador
(define fun-count 0)

;; Definición del proceso encargado de asignarle un identificador a las funciones anónimas. 
(define-pass un-anonymous : L7 (ir) -> L8 ()
  (definitions
    ;; Función para obtener un nuevo nombre para el identificador de la función.
    (define (new-name)
        (begin
          (define cad (string-append "foo" (number->string fun-count)))
          (set! fun-count (+ fun-count 1))
          (string->symbol cad))))
  (Expr : Expr (ir) -> Expr()
    [(lambda ([,x* ,t*] ...) ,[body])
     (let ([n (new-name)])
     `(letfun ([,n Lambda (lambda ([,x* ,t*] ...) ,body)]) ,n))])
  (Expr ir))
  
;; Función que verifica la aridad de las operaciones. 
(define-pass verify-arity : L8 (e) -> L8 ()
  (definitions
    (define (arity? o)
      (memq o '(+ - * / < > equal?)))
    (define (lista? o)
      (memq o '(car cdr length))))
  (Expr : Expr (e) -> Expr ()
        [(primapp ,prN ,[e1] ,[e2])
         (cond
           [(arity? prN) e]
           [else (error "Arity mismatch")])]
        [(primapp ,prN ,e1)
         (cond
           [(lista? prN) e]
           [else (error "Arity mismatch")])]))
     
;; Función que regresa la unión de dos listas. 
(define (union l1 l2)
  (for ([i l2])
    (if (memq i l1) 4
        (set! l1 (append l1 (list i))))
    )
  l1)

;; Función para obtener las variables definidas de manera global. 
(define-pass globalVar : L8 (ir) -> * (list)
  (Expr : Expr (ir) -> * (list)
    [(begin ,e* ... ,e) (union (globalVar e) (foldr union '() (map globalVar e*)))]
    [(if ,e0 ,e1 ,e2) (union (globalVar e0) (union (globalVar e1) (globalVar e2)))]
    [(let ([,x ,t ,e]) ,body) (union (globalVar e) (globalVar body))]
    [(for [,x ,e0] ,e1) (globalVar e1)]
    [(while [,e0] ,e1) (union (globalVar e0) (globalVar e1))]
    [(define ,x ,e) (list x)]
    [else '()])
  (Expr ir))

;; Función que encuentra variables libres en una expresión. 
(define (Fv e ctx)
    (nanopass-case (L8 Expr) e
      [,x (remove* ctx (list x))]
      [(cuote ,c) '()]
      [(begin ,e* ... ,e) (begin (define lista '()) 
                                 (for ([i e*]) 
                                    (set! lista (union lista (Fv i ctx)))
                                    (set! ctx (union ctx (globalVar i))))
                                 (set! lista (union lista (Fv e ctx)))
                                 lista)]
      [(list ,e* ... ) '()]
      [(if ,e0 ,e1 ,e2) (if (equal? (~a (unparse-L8 e2)) "void") (remove* ctx (union (Fv e0 ctx) (Fv e1 ctx)))
                                          (remove* ctx (union (Fv e0 ctx) (union (Fv e1 ctx) (Fv e2 ctx)))))]
      [(while [,e0] ,e1) (remove* ctx (union (Fv e0 ctx) (Fv e1 ctx)))]
      [(for [,x ,e0] ,e1) (remove* (append ctx '(x)) (union (Fv e1 ctx) (Fv e0 ctx)))]
      [(primapp ,prN ,e1 ...) (remove* ctx(foldr union '() (map (lambda (n) (Fv n ctx)) e1)))]
      [(lambda ([,x* ,t*] ...) ,body) (remove* (append ctx x*) (Fv body ctx))]
      [(let ([,x ,t ,e]) ,body) (remove* ctx (union (Fv e ctx) (remq x (Fv body ctx))))]
      [(letrec ([,x ,t ,e]) ,body) (remove* (append ctx '(x)) (union (Fv e ctx) (Fv body ctx)))]
      [(letfun ([,x ,t ,e]) ,body) (remove* ctx (union (Fv e ctx) (remq x (Fv body ctx))))]
      [(,e0 ,e1 ...) (remove* ctx (union (Fv e0 ctx) (foldr union '() (map (lambda (n) (Fv n ctx)) e1))))]
      [(define ,x ,e) (remove* ctx (Fv e ctx))]
      [else '()]))

;; Definición del proceso que se encarga de ver que no haya variables libres.
(define-pass verify-vars : L8 (ir) -> L8 ()
  (if (empty? (Fv ir '())) ir (begin (write (Fv ir '())) (error 'verify-vars "Free variable"))))
  
;; Proceso que currifica las lambdas y la aplicación. 
(define-pass curry : L8 (ir) -> L9 ()
  (definitions
    (define (aux-curry var type body)
      (if  (= (length var) 0)
           (unparse-L9 body)
           `(lambda ([,(car var) ,(car type)])
             ,(aux-curry (cdr var) (cdr type) body))))
    (define (app a b)
      (if  (empty? b)
           a 
           (app `(,a ,(car b)) (cdr b)))))
  (Expr : Expr (ir) -> Expr()
    [(lambda ([,x* ,t*] ...) ,[body]) (parser-L9 (aux-curry x* t* body))]
    [(,[e0] ,[e1] ...) (parser-L9 (app (unparse-L9 e0) (map unparse-L9 e1)))]))
 
 ;; Definción del proceso que currifica una expresión let o letrec.  
(define-pass type-const : L9 (ir) -> L10 ()
  (definitions)
  (Expr : Expr (ir) -> Expr()
    [(cuote ,c) (cond
                 [(integer? c) `(const Int ,c)]
                 [(char? c) `(const Char ,c)]
                 [else `(const Bool ,c)])]))

;; Busca el tipo de una variable en el contexto. 
(define (buscar var lista)
  (define x #f)
  (for ([i lista])
        (if (equal? var (car i)) (set! x (cdr i)) #f))
  x)

;; Verifica que sea tipo List of T. 
(define (tipoLista x) (if (list? x) 
  (let* (
    [f (car x)]
    [s (cadr x)]
    [t (caddr x)])
  (and (equal? f 'List) (equal? s 'of) (type? t)))
  #f))

;; Verifica que sea tipo Función.
(define (tipoFuncion x) (if (list? x) 
  (let* (
    [f (car x)]
    [s (cadr x)]
    [t (caddr x)])
  (and (type? f) (equal? s '→) (type? t)))
  #f))

;; Función auxiliar para obtener el tipo que debe de regresar una primitiva. 
(define (getTipo op t)
  (cond
   [(equal? op 'car) (caddr t)]
   [(equal? op 'length) 'Int]
   [(equal? op 'cdr) t]))

;; Función que une dos diccionarios. 
(define (union-hash h1 h2)
  (begin
    (if (hash-empty? h2) 4
    (for ([i (hash-keys h2)])
      (if (hash-has-key? h1 i) 4
        (hash-set! h1 i (hash-ref h2 i)))))
     h1))

;; Función que hace la union de los diccionarios que generen expresiones en una lista. 
(define (agregar e lista tabla)
  (begin (union-hash tabla (getTable e tabla))
         (for ([i lista])
           (union-hash tabla (getTable i tabla)))
         tabla))


;; Función que genera la tabla de símbolos de una expresión del lenguaje.
(define (getTable expr tabla)
  (nanopass-case (L10 Expr) expr
      [(begin ,e* ... ,e) (agregar e e* tabla)]
      [(if ,e0 ,e1 ,e2) (union-hash (getTable e0 tabla) (union-hash (getTable e1 tabla) (getTable e2 tabla)))]
      [(let ([,x ,t ,e]) ,body) (union-hash (getTable e tabla) (getTable body tabla))]
      [(while [,e0] ,e1) (union-hash (getTable e0 tabla) (getTable e1 tabla))]
      [(for [,x ,e0] ,e1) (getTable e1 tabla)]
      [(define ,x ,e) (begin (hash-set! tabla x (J e tabla (make-hash))) tabla)]
      [else tabla]))

;; Función que verifica que no se regrese un tipo Void. 
(define (verif t)
  (if (equal? t 'Void) (error 'J "No puedes regresar un tipo Void") t))

;; Implementación del algoritmo J. 
(define (J e ctx global)
    (nanopass-case (L10 Expr) e
      [,x (if (hash-has-key? global x) (hash-ref global x) (buscar x ctx))]
      [(const ,t ,c) (verif t)]
      [(list) 'List]
      [(begin ,e* ... ,e) (begin 
                            (for ([i e*]) 
                              (J i ctx global)
                              (set! global (getTable i global)))
                            (verif (J e ctx global)))]
      [(list ,e* ... ,e) (let*
                           ([types (append (map (lambda (x) (J x ctx global)) e*) (list (J e ctx global)))]
                            [t (part types)]
                            [eqt (map (lambda (x) (unify t x)) types)])
                           (if (foldr (lambda (x y) (and x y)) #t eqt)
                               `(List of ,(verif t))
                           (error 'J "La Lista debe ser homogenea")))]
      [(if ,e0 ,e1 ,e2) (if (equal? (~a (unparse-L10 e2)) "void") 
                          (let*
                            ([t0 (J e0 ctx global)]
                             [t1 (J e1 ctx global)])
                            (if (equal? t0 'Bool)
                                t1
                                (error 'J "Se esperaba tipo Bool 2")))
                          (let*
                            ([t0 (J e0 ctx global)]
                             [t1 (J e1 ctx global)]
                             [t2 (J e2 ctx global)])
                            (if (equal? t0 'Bool)
                                (if (unify t1 t2) t1 (error 'J "No unificable"))
                                (begin (write e0) (error 'J "Se esperaba tipo Bool 1")))))]
      [(while [,e0] ,e1) (let
                             ([condicion (J e0 ctx global)])
                           (if (equal? condicion 'Bool)
                               (verif (J e1 ctx global))
                               (error 'J "Se esperaba tipo Bool en la condición")))]
      [(for [,x ,e0] ,e1) (let
                             ([condicion (J e0 ctx global)])
                           (if (equal? (substring (~a condicion) 1 5) "List")
                               (verif (J e1 ctx global))
                               (error 'J "Se esperaba tipo List en el for")))]
      [(primapp ,prN ,e1) (let*
                             ([t (J e1 ctx global)])
                           (if (lst? prN)
                               (if (tipoLista t)
                                        (verif (getTipo prN t))
                                        (error 'J "Se esperaba tipo List of T"))
                               (error 'J "Aridad Incorrecta")))]
      [(primapp ,prN ,e1 ,e2) (let*
                               ([t1 (J e1 ctx global)]
                                [t2 (J e2 ctx global)])
                              (if (arit? prN)
                                  (if (and (equal? t1 'Int) (equal? t2 'Int))
                                    (if (memq prN '(< > equal?)) 'Bool 'Int)
                                    (error 'J "Se esperaba tipo Int"))
                                  (error 'J "Aridad Incorrecta")))]
      [(lambda ([,x ,t]) ,body) (let*
                                    ([newCtx (set-add ctx (cons x t))]
                                     [s (J body newCtx global)])
                                    `(,t → ,(verif s)))]
      [(let ([,x ,t ,e]) ,body) (let*
                                   ([t1 (J e ctx global)]
                                    [newCtx (set-add ctx (cons x t1))]
                                    [s (J body newCtx global)])
                                  (if (unify t1 t) (verif s) (error 'J "El tipo no corresponde con el valor 1")))]
      [(letrec ([,x ,t ,e]) ,body) (let*
                                   ([newCtx (set-add ctx (cons x t))]
                                    [t1 (J e newCtx global)]
                                    [s (J body newCtx global)])
                                  (if (unify t1 t) (verif s) (error 'J "El tipo no corresponde con el valor")))]
      [(letfun ([,x ,t ,e]) ,body) (let*
                                   ([newCtx (set-add ctx (cons x t))]
                                    [t0 (J e ctx global)]
                                    [s (J body newCtx global)])
                                  (if (or (unify t t0) (equal? t 'Lambda))
                                      (verif s) 
                                      (error 'J "El tipo no corresponde con el valor 2")))]
      [(,e0 ,e1) (let*
                   ([t0 (J e0 ctx global)]
                    [t1 (J e1 ctx global)])
                 (if (tipoFuncion t0)
                     (if (unify t0 `(,t1 → ,(caddr t0))) 
                     (caddr t0)
                     (error 'J "El tipo no corresponde con el valor 3"))
                     (error 'J "Se esperaba tipo función")))]
      [(define ,x ,e) (let 
                        ([t (J e ctx global)])
                        (if (or (equal? t 'Lambda) (tipoFuncion t)) (error 'J "Define no puede guardar una funcion") 'Void))]
      [else (begin (write e) (error 'J "Expresión inválida"))]))
         
;; Proceso auxiliar que obtiene el contexto. 
(define (getCtx e)
    (nanopass-case (L10 Expr) e
      [(begin ,e* ... ,e) (append (map (lambda (x) (getCtx x)) e*) (getCtx e))]
      [(if ,e0 ,e1 ,e2) (if (equal? (~a (unparse-L10 e2)) "void") (append (getCtx e0) (getCtx e1))
                                       (append (getCtx e0) (getCtx e1) (getCtx e2)))]
      [(lambda ([,x ,t]) ,body) (set-add (getCtx body) (cons x t))]
      [(let ([,x ,t ,e]) ,body) (append (set-add (getCtx body) (cons x t)) (getCtx e))]
      [(letrec ([,x ,t ,e]) ,body) (append (set-add (getCtx body) (cons x t)) (getCtx e))]
      [(letfun ([,x ,t ,e]) ,body) (append (set-add (getCtx body) (cons x t)) (getCtx e))]
      [(,e1 ,e2) (append (getCtx e1) (getCtx e2))]
      [else '()]))

;; Se encarga de quitar las anotaciones de tipo Lambda y de tipo List (de ser necesario). 
(define-pass type-infer : L10 (ir) -> L10 ()
  (definitions)
  (Expr : Expr (ir) -> Expr()
    [(lambda ([,x ,t]) ,[body]) (if (or (equal? t 'List) (equal? t 'Lambda))
                                    `(lambda ([,x ,(J body (getCtx ir) (getTable ir (make-hash)))]) ,body) 
                                     ir)]
    [(let ([,x ,t ,[e]]) ,[body]) (if (equal? t 'List)
                                  `(let ([,x ,(J e (getCtx ir) (getTable ir (make-hash))) ,e]) ,body)
                                  ir)]
    [(letrec ([,x ,t ,[e]]) ,[body]) (if (or (equal? t 'List) (equal? t 'Lambda))
                                  `(letrec ([,x ,(J e (getCtx ir) (getTable ir (make-hash))) ,e]) ,body)
                                      ir)]
    [(letfun ([,x ,t ,[e]]) ,[body]) (if (or (equal? t 'List) (equal? t 'Lambda))
                                  `(letfun ([,x ,(J e (getCtx ir) (getTable ir (make-hash))) ,e]) ,body)
                                      ir)])) 
  
;; Definción del proceso que currifica una expresión let o letrec.  
(define-pass uncurry : L10 (ir) -> L11 ()
  (definitions
    ;; Función para obtener la aplicación descurrificada. 
    (define (getApp expr sol)
      (nanopass-case (L10 Expr) expr
                     [(,e1 ,e2) (getApp e1 (set-add sol (unparse-L10 e2)))]
                     [else `,(set-add sol (unparse-L11 (uncurry expr)))]))
    ;; Función para obtener una expresión lambda descurrificada. 
    (define (getExpr expr sol)
      (nanopass-case (L10 Expr) expr
                     [(lambda ([,x ,t]) ,body) (getExpr body (set-add sol `[,x ,t]))]
                     [else `(lambda ,sol ,(unparse-L11 (uncurry expr)))])))
  (Expr : Expr (ir) -> Expr()
    [(lambda ([,x ,t]) ,body) (parser-L11 (getExpr ir '()))]
    [(,e1 ,e2) (parser-L11 (getApp ir '()))]))

;; Proceso para convertir las listas en arreglos
(define-pass list-to-array : L11 (ir) -> L13 ()
  (definitions
    (define (genList lst ir)
      (let* ([expresion (parser-L10 (unparse-L11 ir))]
             [tipo (J expresion (getCtx expresion) (getTable ir (make-hash)))]
             [a (map unparse-L11 lst)])
      `(array ,(length (unparse-L11 ir)) ,(caddr tipo) ,a))))
  (Expr : Expr (ir) -> Expr()
    [(list ,e* ...) (parser-L13 (genList e* ir))]))

;; Función que elimina los f últimos elementos de la expresion. 
(define (elimElem cad i f)
  (substring cad i (- (string-length cad) f)))

;; Función auxiliar para generar una lista de elementos. 
(define (genElem lst)
  (define cad "")
  ;(write lst)
  (for ([i lst])
    (nanopass-case (L13 Expr) i
      [(const ,t ,c) (if (not (equal? t 'Char)) (set! cad (~a cad (elimElem (aux-python i "") 0 1) ", "))
                (set! cad (~a cad "\"" (elimElem (aux-python i "") 0 1) "\" , ")))]
      [else (set! cad (~a cad (elimElem (aux-python i "") 0 1) ", "))])
  )
  (elimElem cad 0 2))

;; Función que genera una cadena traducida con una lista de expresiones. 
(define (genBody lst indent)
  (define cad "")
  (for ([i lst])
    (set! cad (~a cad (aux-python i indent))))
  cad)

;; Genera el cuerpo de una función. 
(define (regresa expr indent)
  (nanopass-case (L13 Expr) expr
    [,x (~a indent "return " x "\n")]
    [(const ,t ,c) (~a indent "return " (constante c) "\n")]
    [(array ,le ,t (,e ...)) (~a indent "return " (aux-python expr ""))]
    [(begin ,e* ... ,e) (~a (genBody e* indent) (regresa e indent))]
    [(if ,e0 ,e1 ,e2) (if (equal? (~a (unparse-L13 e2)) "void") (~a indent "if " (elimElem (aux-python e0 "") 0 1) ":\n" (regresa e1 (~a indent "  ")))
                                     (~a indent "if " (elimElem (aux-python e0 "") 0 1) ":\n" (regresa e1 (~a indent "  ")) indent "else:\n" (regresa e2 (~a indent "  "))))]
    [(primapp ,prN ,e* ...) (~a indent "return " (aux-python expr ""))]
    [(let ([,x ,t ,e]) ,body) (~a indent x " = " (aux-python e "") (regresa body indent))]
    [(letrec ([,x ,t ,e]) ,body) (~a indent "def " x (genFuncion e indent) (regresa body indent))]
    [(,e0 ,e1 ...) (~a indent "return " (aux-python expr ""))]
    [else (aux-python expr indent)]))

;;Genera los parametros que recibe la función como el cuerpo de esta.  
(define (genFuncion expr indent)
  (nanopass-case (L13 Expr) expr
      [(lambda ([,x* ,t*]...) ,body) (~a "(" (genElem x*) "):\n" (regresa body (~a indent "  ")))]
      [(letfun ([,x ,t ,e]) ,body) (~a "():\n" (aux-python expr (~a indent "  "))) ]
      [else (error 'python "Mala definición de función")]))

;; Función para saber si la constante es de tipo boolean.
(define (constante c)
  (if (boolean? c) 
    (if c "True" "False") 
    c))

;; Función que realiza la traducción a python. 
(define (aux-python e indent)
  (nanopass-case (L13 Expr) e
    [,x (~a indent x "\n")]
    [(const ,t ,c) (~a indent (constante c) "\n")]
    [(array ,le ,t (,e ...)) (~a indent "[" (genElem e) "]\n")]
    [(begin ,e* ... ,e) (~a (genBody e* indent) (aux-python e indent))]
    [(if ,e0 ,e1 ,e2) (if (equal? (~a (unparse-L13 e2)) "void") (~a indent "if " (elimElem (aux-python e0 "") 0 1) ":\n" (aux-python e1 (~a indent "  ")))
                                      (~a indent "if " (elimElem (aux-python e0 "") 0 1) ":\n" (aux-python e1 (~a indent "  ")) indent "else:\n" (aux-python e2 (~a indent "  "))))]
    [(primapp ,prN ,e) (cond 
                          [(equal? prN 'car) (~a (elimElem (aux-python e indent) 0 1) "[0]\n")]
                          [(equal? prN 'length) (~a indent "len(" (elimElem (aux-python e "") 0 1) ")\n")]
                          [(equal? prN 'cdr) (~a (elimElem (aux-python e indent) 0 1) "[1:len(" (elimElem (aux-python e "") 0 1) ")]\n")])]
    [(primapp ,prN ,e1 ,e2) ( let ([r (if (equal? prN 'equal?) "==" prN)]) (~a (elimElem (aux-python e1 indent) 0 1) " " r " " (elimElem (aux-python e2 "") 0 1) "\n"))]
    [(lambda ([,x* ,t*]...) ,body) (error 'python "No se definio la función previamente.")] 
    [(let ([,x ,t ,e]) ,body) (~a indent x " = " (aux-python e "") (aux-python body indent))]
    [(letrec ([,x ,t ,e]) ,body) (~a indent "def " x (genFuncion e indent) (aux-python body indent))]
    [(letfun ([,x ,t ,e]) ,body) (~a indent "def " x (genFuncion e indent))]
    [(,e0 ,e1 ...) (~a (elimElem (aux-python e0 indent) 0 2) "(" (genElem e1) ")\n")]
    [(define ,x ,e) (~a indent "global " x "\n" indent x " = " (aux-python e ""))]
    [(while [,e0] ,e1) (~a indent "while " (elimElem (aux-python e0 "") 0 1) ":\n" (aux-python e1 (~a indent "  ")))]
    [(for [,x ,e0] ,e1) (~a indent "for " x " in " (elimElem (aux-python e0 "") 0 1) ":\n" (aux-python e1 (~a indent "  ")))]
    ))

;; Funcion que pasa una expresion a python. 
(define (python e)
  (aux-python e ""))


;; Función que nos permite compilar el archivo de entrada con terminación .mt y regresa los archivos .fe, .me, .py
(define (compilador entrada)

  (define arch (~a entrada))

  ;; Verificamos la terminacion del archivo. 
  (define termina (substring arch (- (string-length arch) 3) (string-length arch)))
  (if (not (equal? termina ".mt")) (error 'compilador "El archivo debe tener terminación .mt") (void))

  ;; Leemos el archivo
  (define name (substring arch 0 (- (string-length arch) 3)))
  (define p (file->list arch))
  (define program "")
  (if (equal? 1 (length p)) 
    (set! program (car p))
    (set! program (append (list 'begin) p)))

  (define a (verify-arity (un-anonymous (indentify-assigments (curry-let (direct-app (purify-recursion (quote-const (eta-expand (curry-prim (remove-logical-operators (remove-primA (remove-string (remove-one-armed-if (make-explicit (parser-LF program))))))))))))))))
  (define b (verify-vars a))
  (write-file (string-append name ".fe") (~a (unparse-L8 b)))

  ;; Middle-end
  (define c (type-const (curry b)))
  (J c '() (make-hash)) ;; Verifica los tipos
  (define e (uncurry (type-infer c)))
  (write-file (string-append name ".me") (~a (unparse-L11 e)))

  ;; Back-end
  (define f (python (list-to-array e)))
  (write-file (string-append name ".py") f)
)


;; Compila mi archivo

(define a (read))
(compilador a)
