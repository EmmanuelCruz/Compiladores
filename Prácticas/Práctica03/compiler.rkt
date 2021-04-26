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
        
;; PARSERS

(define-parser parser-LF LF)
(define-parser parser-L0 L0)
(define-parser parser-L1 L1)
(define-parser parser-L2 L2)
(define-parser parser-L4 L4)
(define-parser parser-L5 L5)
(define-parser parser-L6 L6)

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

;Funciones Auxiliares

;*************************** PRUEBAS ***************************;
; (unparse-L4 (remove-logical-operators (parser-L2 '(and (not #f) #t))))
; (unparse-L4 (remove-logical-operators (parser-L2 '(and #t #t))))
; (unparse-L4 (remove-logical-operators (parser-L2 '(or #t #t))))
; (unparse-L4 (remove-logical-operators (parser-L2 '(not #f))))

; (unparse-L5 (eta-expand (parser-L4 '(+))))
; (unparse-L5 (eta-expand (parser-L4 '(car))))
; (unparse-L5 (eta-expand (parser-L4 '(length))))
; (unparse-L5 (eta-expand (parser-L4 '(+ 3 4))))
; (unparse-L5 (eta-expand (parser-L4 '(car (list 3 3 3)))))
; (unparse-L5 (eta-expand (parser-L4 '(length (list 3 3 3)))))

; (unparse-L6 (quote-const (parser-L5 '(5))))

; (unparse-L6 (purify-recursion (parser-L6 '(letrec ([foo Lambda (lambda ([x Int]) x)] [z Int (kuote 4)]) (foo z)))))
; (unparse-L6 (purify-recursion (parser-L6 '(letrec ([foo Lambda (lambda ([x Int]) x)]) (foo z)))))

; (unparse-L6 (direct-app (parser-L6 '((lambda ([x Int] [y Int]) (+ x y)) (kuote 5) (+ (kuote 3) (kuote 4))))))
