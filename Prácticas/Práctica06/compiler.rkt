
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

(define (type? x) (or
                   (memq x '(Bool Char Int List String Lambda))
                   (equal? '(Bool -> Bool) x)
                   (equal? '(Bool -> Char) x)
                   (equal? '(Bool -> Int) x)
                   (equal? '(Bool -> List) x)
                   (equal? '(Bool -> String) x)
                   (equal? '(Bool -> Lambda) x)
                   (equal? '(Char -> Bool) x)
                   (equal? '(Char -> Char) x)
                   (equal? '(Char -> Int) x)
                   (equal? '(Char -> List) x)
                   (equal? '(Char -> String) x)
                   (equal? '(Char -> Lambda) x)
                   (equal? '(Int -> Bool) x)
                   (equal? '(Int -> Char) x)
                   (equal? '(Int -> Int) x)
                   (equal? '(Int -> List ) x)
                   (equal? '(Int -> String) x)
                   (equal? '(Int -> Lambda) x)
                   (equal? '(String -> Bool) x)
                   (equal? '(String -> Char) x)
                   (equal? '(String -> Int) x)
                   (equal? '(String -> List) x)
                   (equal? '(String -> String) x)
                   (equal? '(String -> Lambda) x)
                   (equal? '(Lambda -> Bool) x)
                   (equal? '(Lambda -> Char) x)
                   (equal? '(Lambda -> Int) x)
                   (equal? '(Lambda -> List) x)
                   (equal? '(Lambda -> String) x)
                   (equal? '(Lambda -> Lambda) x)
                   (equal? '(List of Bool) x)
                   (equal? '(List of Char) x)
                   (equal? '(List of Int) x)
                   (equal? '(List of List) x)
                   (equal? '(List of String) x)
                   (equal? '(List of Lambda) x)))

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

(define-language L9
  (extends L8)
  (Expr (e)
        (-
         (lambda ([x* t*] ...) body))
        (+
         (lambda ([x t]) body))))

(define-language L10
  (extends L9)
  (Expr (e t)
        (-
         (kuote c))
        (+
         (const t c))))

(define-language L11
  (extends L10)
  (Expr (e)
        (-
         (lambda ([x t]) body))
        (+
         (lambda ([x* t*] ...) body))))

(define-language L12
  (extends L11)
  (Expr (e)
        (-
         (letrec ([x t e]) body)
         (let ([x t e]) body)
         (letfun ([x t e]) body)
         )
        (+
         (letrec body)
         (let body)
         (letfun body)
         )
        )
  )

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
(define-parser parser-L9 L9)
(define-parser parser-L10 L10)
(define-parser parser-L11 L11)
(define-parser parser-L12 L12)

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

;;PRACTICA 06

(define-pass uncurry : L10 (ir) -> L11 ()
  (definitions
    (define (uncurryLambda params cuerpo)
      (nanopass-case (L10 Expr) cuerpo
                     [(lambda ([,x ,t]) ,body) (uncurryLambda (append `([,x ,t]) params) body)]
                     [else `(lambda ,params ,(unparse-L11 (uncurry cuerpo)))])))
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x ,t]) ,body) (uncurryLambda empty ir)]))

(define tablaSimbolos (make-hash))

(define (symbol-table-var expr)
  (nanopass-case (L11 Expr) expr
                 [(letrec ([,x ,t ,e]) ,body) (begin
                                                (hash-set! tablaSimbolos x (cons t (unparse-L11 e)))
                                                (symbol-table-var body))]
                 [(let ([,x ,t ,e]) ,body) (begin
                                                (hash-set! tablaSimbolos x (cons t (unparse-L11 e)))
                                                (symbol-table-var body))]
                 [(letfun ([,x ,t ,e]) ,body) (begin
                                                (hash-set! tablaSimbolos x (cons t (unparse-L11 e)))
                                                (symbol-table-var body))]
                 [else tablaSimbolos]))

(define-pass assigment : L11 (ir) -> L12 (lst)
  (definitions
    (define tablita (make-hash))
    )
  (Expr : Expr (ir) -> Expr()
        [(let ([,x ,t ,e]) ,[body]) (begin
              (hash-set! tablita x (cons t (unparse-L11 e)))
              `(let ,body))]
        [(letrec ([,x ,t ,e]) ,[body]) (begin
              (hash-set! tablita x (cons t (unparse-L11 e)))
              `(letrec ,body))]
        [(letfun ([,x ,t ,e]) ,[body]) (begin
              (hash-set! tablita x (cons t (unparse-L11 e)))
              `(letfun ,body))])
  (values (Expr ir) tablita))

;*************************** PRUEBAS ***************************;
;;EJERCICIO 1 Y 2
;(unparse-L11 (uncurry (parser-L10 '(lambda ([x Int]) (lambda ([y Int]) (let ([(foo Int (const Int 5))]) (const Bool #t)))))))


;;EJERCICIO 3
;(assigment (parser-L11 '(let ([a Bool (const Bool #t)]) (let ([b Bool (const Bool #t)]) b))))



