#lang nanopass

(require nanopass/base)
(require racket/set)

;;PREDICADOS

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x) (memq x '(+ - * / length car cdr and or not)))

(define (primitive2? x) (memq x '(+ - * / length car cdr)))

(define (constant? x)
  (or (integer? x)
      (char? x)
      (boolean? x)))

(define (type? x) (memq x '(Bool Char Int List String Lambda)))

;; LENGUAJES

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
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (list e* e)
    (e0 e1 ...)))

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

(define-language L1
  (extends L0)
  (Expr (e body)
         (- (if e0 e1))))

(define-language L2
  (extends L1)
  (terminals
   (- (string (s))))
  (Expr (e body)
         (- s)))

(define-language L4
  (extends L2)
  (terminals
   (- (primitive (pr)))
   (+ (primitive2 (npr))))
  (Expr (e body)
         (- pr)
         (+ npr)))
            
(define-language L5
  (extends L4)
  (Expr (e body)
        (+
         (primapp npr e1)
         (primapp npr e1 e2))))
         
(define-language L6
  (extends L5)
  (Expr (e body)
        (- c)
        (+ (kuote c))))

(define-language L7
  (extends L6)
  (Expr (e x t body)
        (+
         (letrec ([x t e]) body)
         (let ([x t e]) body))))

(define-language L8
  (extends L7)
  (Expr (e x t body)
        (+
         (letfun ([x t e]) body)))) 
        
;; PARSERS

(define-parser parser-LF LF)
(define-parser parser-L0 L0)
(define-parser parser-L1 L1)
(define-parser parser-L2 L2)
(define-parser parser-L4 L4)
(define-parser parser-L5 L5)
(define-parser parser-L6 L6)
(define-parser parser-L7 L7)
(define-parser parser-L8 L8)

;; PROCESOS

;Proceso que cambia el cuerpo de lambda, let y letrec por un begin.
(define-pass make-explicit : LF (ir) -> L0 ()
  (Expr : Expr (ir) -> Expr ()
    [,c `',c]
    [(lambda ([,x* ,t*] ...) ,[body*] ... ,[body])
     `(lambda ([,x* ,t*] ...) (begin ,body* ... ,body))]
    [(let ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]))

;PRACTICA 02
(define-pass remove-one-armed-if : LF (e) -> L1 ()
  (Expr : Expr (e) -> Expr ()
      [(if, [e0] , [e1])
       `(if ,e0 ,e1 (void))]))

(define-pass remove-string : L1 (e) -> L2 ()
  (Expr : Expr (e) -> Expr ()
      [,s (string->list s)]))

;PRACTICA 03
(define-pass remove-logical-operators : L2 (e) -> L4 ()
  (Expr : Expr (e) -> Expr ()
        [(,e0 ,[e1]) (if (equal? e0 'not)
                       `(if ,e1 #f #t)
                       e)]
        [(,e0 ,[e1] ,[e2])
         (cond
           [(equal? e0 'and) `(if ,e1 ,e2 #f)]
           [(equal? e0 'or) `(if ,e1 #t ,e2)]
           [else e])]))

(define-pass eta-expand : L4 (e) -> L5 ()
  (Expr : Expr (e) -> Expr ()
        [(,e0) (cond
                 [(equal? e0 '+) `(lambda ([x Int] [y Int]) (primapp + x y))]
                 [(equal? e0 '-) `(lambda ([x Int] [y Int]) (primapp - x y))]
                 [(equal? e0 '*) `(lambda ([x Int] [y Int]) (primapp * x y))]
                 [(equal? e0 '/) `(lambda ([x Int] [y Int]) (primapp / x y))]
                 [(equal? e0 'length) `(lambda ([x List]) (primapp length x))]
                 [(equal? e0 'car) `(lambda ([x List]) (primapp car x))]
                 [(equal? e0 'cdr) `(lambda ([x List]) (primapp cdr x))])]
        [(,e0 ,[e1]) (cond
                     [(equal? e0 'length) `((lambda ([x List]) (primapp length x)) ,(unparse-L5 e1))]
                     [(equal? e0 'car) `((lambda ([x List]) (primapp car x)) ,(unparse-L5 e1))]
                     [(equal? e0 'cdr) `((lambda ([x List]) (primapp cdr x)) ,(unparse-L5 e1))])]
        [(,e0 ,[e1] ,[e2]) (cond
                         [(equal? e0 '+) `((lambda ([x Int] [y Int]) (primapp + x y)) ,e1 ,e2)]
                         [(equal? e0 '-) `((lambda ([x Int] [y Int]) (primapp - x y)) ,e1 ,e2)]
                         [(equal? e0 '*) `((lambda ([x Int] [y Int]) (primapp * x y)) ,e1 ,e2)]
                         [(equal? e0 '/) `((lambda ([x Int] [y Int]) (primapp / x y)) ,e1 ,e2)])]))
        
(define-pass quote-const : L5(e) -> L6 ()
  (Expr : Expr (e) -> Expr ()
        [,c `(kuote ,c)]))

(define-pass purify-recursion : L6(e) -> L6 ()
  (definitions
    (define (obtenLambda lvar ltipo lexp)
      (cond
        [(empty? lvar) empty]
        [(equal? (car ltipo) 'Lambda)
         (list (car lvar) (unparse-L6 (car lexp)) (obtenLambda (cdr lvar) (cdr ltipo) (cdr lexp)))]
        [else (obtenLambda (cdr lvar) (cdr ltipo) (cdr lexp))]))
    (define (obtenNoLambda lvar ltipo lexp)
      (cond
        [(empty? lvar) empty]
        [(equal? (car ltipo) 'Lambda)
         (obtenNoLambda (cdr lvar) (cdr ltipo) (cdr lexp))]
        [else (list (car lvar) (car ltipo) (unparse-L6 (car lexp)) (obtenNoLambda (cdr lvar) (cdr ltipo) (cdr lexp)))]))
    (define (organizaLetrec l-letrec)
      (cond
        [(empty? (car l-letrec)) empty]
        [else (cons (list (first l-letrec) 'Lambda (second l-letrec)) (organizaLetrec (rest (rest l-letrec))))]))
    (define (organizaLet l-let)
      (cond
        [(or (empty? l-let)
             (empty? (car l-let))) empty]
        [else (cons (list (first l-let) (second l-let) (third l-let)) (organizaLet (rest (rest (rest l-let)))))]))
    (define (organiza expr)
      (nanopass-case (L6 Expr) expr
                     [(letrec ([,x* ,t* ,e*] ...) ,body)
                      (letrec ([listaLambda (obtenLambda x* t* e*)]
                               [listaNoLambda (obtenNoLambda x* t* e*)]
                               [parametrosLambda (organizaLetrec listaLambda)]
                               [parametrosNoLambda (organizaLet listaNoLambda)])
                        (if (empty? parametrosNoLambda)
                            `(letrec ,parametrosLambda ,(unparse-L6 body))
                            `(letrec ,parametrosLambda (let ,parametrosNoLambda ,(unparse-L6 body)))))]
                     [else expr])))
  (Expr : Expr (e) -> Expr ()
        [(letrec ([,x* ,t* ,[e*]] ...) ,[body]) (organiza e)]))

(define-pass direct-app : L6(e) -> L6 ()
  (definitions
    (define (regresaParametros expr)
      (nanopass-case (L6 Expr) expr
                     [(lambda ([,x* ,t*] ...) ,body) `([,x* ,t*] ...)]))
    (define (regresaCuerpo expr)
      (nanopass-case (L6 Expr) expr
                     [(lambda ([,x* ,t*] ...) ,body) `,body])))
  (Expr : Expr (e) -> Expr ()
        [(,e0 ,e1 ,e2)
         (let ([vars (first (first (regresaParametros e0)))]
               [tipos (second (first (regresaParametros e0)))]
               [cuerpo (regresaCuerpo e0)])
           `(let ((,(first vars) ,(first tipos) ,e1) (,(second vars) ,(second tipos) ,e2)) ,cuerpo))]))

;PRACTICA 04
(define-pass curry-let : L6 (e) -> L7 ()
  (definitions
    (define (currificaLet e l1 l2 l3)
      (nanopass-case (L6 Expr) e
                     [(let ([,x* ,t* ,e*] ...) ,body)
                      (if (empty? l1)
                          (unparse-L6 `,body)
                          `(let ([,(first l1) ,(first l2) ,(first l3)])
                             (,(currificaLet e (rest l1) (rest l2) (rest l3)))))]
                     [(letrec ([,x* ,t* ,e*] ...) ,body)
                      (if (empty? l1)
                          (unparse-L6 `,body)
                          `(letrec ([,(first l1) ,(first l2) ,(first l3)])
                             (,(currificaLet e (rest l1) (rest l2) (rest l3)))))]))
    (define get-list (lambda (expr)
       (nanopass-case (L6 Expr) expr
                      [(let ([,x* ,t* ,[e*]] ...) ,[body]) `([,x* ,t* ,e*] ...)]
                      [(letrec ([,x* ,t* ,[e*]] ...) ,[body]) `([,x* ,t* ,e*] ...)]
                      [else expr]))))
  (Expr : Expr (e) -> Expr ()
      [(let ([,x* ,t* ,[e*]] ...) ,[body])
       (let ([lista (get-list e)])
         (currificaLet e (first (first lista)) (second (first lista)) (map unparse-L6 (third (first lista)))))]
      [(letrec ([,x* ,t* ,[e*]] ...) ,[body])
       (letrec ([lista (get-list e)])
         (currificaLet e (first (first lista)) (second (first lista)) (map unparse-L6 (third (first lista)))))]))

(define-pass identify-assigments : L7 (exp) -> L7 ()
  (Expr : Expr (exp) -> Expr ()
        [(let ([,x ,t ,[e]]) ,[body])
         (if (equal? t `Lambda)
             `(letrec ([,x ,t ,e]) ,body)
             exp)]))

(define amount-functions 0)

(define-pass un-anonymous : L7 (e) -> L8 ()
  (definitions
    (define (concatena n)
      (let ([new-function n])
        (begin
          (set! amount-functions (+ n 1))
          (string->symbol (string-append "foo" (number->string new-function)))))))
  (Expr : Expr (e) -> Expr ()
        [(lambda ([,x* ,t*] ...) ,body)
         (let ([nombre (concatena amount-functions)])
               `(letfun ([,nombre ,'Lambda ,(unparse-L7 e)]) ,nombre))]))

(define-pass verify-arity : L8 (e) -> L8 ()
  (definitions
    (define (arity? o)
      (memq o '(+ - * /)))
    (define (lista? o)
      (memq o '(car cdr length))))
  (Expr : Expr (e) -> Expr ()
        [(primapp ,npr ,e1 ,e2)
         (cond
           [(and (arity? npr)) e]
           [else (error "Arity mismatch")])]
        [(primapp ,npr ,e1)
         (cond
           [(and (lista? npr)) e]
           [else (error "Arity mismatch")])]))

(define-pass verify-vars : L8 (e) -> L8 ()
  (definitions
    (define (Fu expr)
      (nanopass-case (L8 Expr) expr
                     [,x `(,x)]
                     [(kuote ,c) '()]
                     [(begin ,e* ... ,e) (append* (Fu e) (foldr append* '() (map Fu e*)))]
                     [(primapp ,npr ,e1 ,e2) (append* (Fu e1) (Fu e2))]
                     [(primapp ,npr ,e1) (Fu e1)]
                     [(if ,e0 ,e1 ,e2) (append* (Fu e0) (Fu e1) (Fu e2))]
                     [(lambda ([,x* ,t*] ...) ,body) (remove* x* (Fu body))]
                     [(let ([,x ,t ,e]) ,body) (remove (append* (Fu body) (Fu e)) x)]
                     [(letrec ([,x ,t ,e]) ,body) (remove (append* (Fu body) (Fu e)) x)]
                     [(letfun ([,x ,t ,e]) ,body) (remove (append* (Fu body) (Fu e)) x)]
                     [(list ,e* ,e) (append* (Fu e) (foldr append* '() (map Fu e*)))])))
  (Expr : Expr (e) -> Expr ()
        [(kuote ,c) e]
        [else
         (if (empty? (Fu e))
            e
            (error "Free variable x"))]))

; Funciones Auxiliares

;*************************** PRUEBAS ***************************;
;; (unparse-L7 (curry-let (parser-L6 '(let ([x Int (kuote 4)] [y Int (kuote 6)]) (+ x y)))))
;; (unparse-L7 (curry-let (parser-L6 '(let ([x Int (kuote 4)] [y Int (kuote 6)] [y Int (kuote 67)]) (+ x y)))))
;; (unparse-L7 (curry-let (parser-L6 '(letrec ([x Int (kuote 4)] [y Int (kuote 6)] [y Int (kuote 67)]) (+ x y)))))

;; (unparse-L7 (identify-assigments (parser-L7 '(let ([foo Lambda (lambda ([x Int]) x)]) (foo (kuote 5))))))
;; (unparse-L7 (identify-assigments (parser-L7 '(let ([x Int (kuote 4)]) (kuote 5)))))

;; (unparse-L8 (un-anonymous (parser-L7 '(lambda ([x Bool]) (if x (kuote 1) (kuote 2))))))

;; (unparse-L8 (verify-arity (parser-L8 '(primapp car (kuote 1) (kuote 2)))))
;; (unparse-L8 (verify-arity (parser-L8 '(primapp + (kuote 1) (kuote 2)))))

;; (unparse-L8 (verify-vars (parser-L8 '(primapp + (kuote 1) x))))
;; (unparse-L8 (verify-vars (parser-L8 '(primapp + (kuote 1) (kuote 2)))))
