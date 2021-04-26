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
;;PRACTICA 05
(define-pass curry : L8 (e) -> L9 ()
  (definitions
    (define (currificaLambda e l1 l2)
      (nanopass-case (L8 Expr) e
                     [(lambda ([,x* ,t*] ...) ,body)
                      (if (empty? l1)
                          (unparse-L8 `,body)
                          `(lambda ([,(first l1) ,(first l2)])
                             (,(currificaLambda e (rest l1) (rest l2)))))]))
    (define (currificaAF l)
      (cond
       [(= (length l) 1) `,l]
       [(= (length l) 2) `(,(car l) ,(second l))]
       [else `((,(car l) ,(second l)) ,(currificaAF (cddr l)))]))
    (define get-list (lambda (expr)
       (nanopass-case (L8 Expr) expr
                      [(lambda ([,x* ,t*] ...) ,body) `([,x* ,t*] ...)]
                      [else expr]))))
  (Expr : Expr (e) -> Expr ()
      [(lambda ([,x* ,t*] ...) ,[body])
       (let ([lista (get-list e)])
         (currificaLambda e (first (first lista)) (second (first lista))))]
      [(,e0 ,e1 ...)
       (let ([lista `(,e0 ,e1)])
         `((,e0 ,(car e1)) ,(currificaAF e1)))]))
(define-pass type-const : L9 (e) -> L10 ()
  (Expr : Expr (e) -> Expr ()
        [(kuote ,c) (if (number? (unparse-L9 c)) `(const Int ,c)
                       (if (char? (unparse-L9 c)) `(const Char ,c)
                           (if (boolean? (unparse-L9 c)) `(const Bool ,c)
                                   '(Error no es un tipo valido))))]))
(define (J expr contexto)
  (nanopass-case (L10 Expr) expr
                 [,x (lookup x contexto)]
                 [(const ,t ,c) `,t]
                 [(begin ,e* ... ,e)
                  (let*
                      ([types (map (lambda(x)(J x contexto)) (unparse-L10 e*))])
                    (J e contexto)
                  )]
                 [(primapp ,npr ,e0)
                  (let*
                   ([t (J e0 contexto)])
                     (if (equal? 'car (unparse-L10 npr)) (if (list? t)
                                                                (if (equal? (car t) 'List)
                                                                    (last t)
                                                                    (error "El tipo no corresponde con el valor"))
                                                                ((error "El tipo no corresponde con el valor")))
                         (if (equal? 'cdr (unparse-L10 npr)) (if (list? t)
                                                                (if (equal? (car t) 'List)
                                                                    t
                                                                    (error "El tipo no corresponde con el valor"))
                                                                ((error "El tipo no corresponde con el valor")))
                         (if (equal? 'length (unparse-L10 npr)) (if (list? t)
                                                                (if (equal? (car t) 'List)
                                                                    'Int
                                                                    (error "El tipo no corresponde con el valor"))
                                                                ((error "El tipo no corresponde con el valor")))
                         (error "El tipo no corresponde con el valor")))))]
                 [(primapp ,npr ,e0 ,e1)
                  (let*
                   ([t (J e0 contexto)]
                    [t1 (J e1 contexto)])
                    (if
                     (or (equal? '+ (unparse-L10 npr)) (equal? '* (unparse-L10 npr)) (equal? '/ (unparse-L10 npr)) (equal? '- (unparse-L10 npr)))
                     (if (unify 'Int t)
                         (if (unify 'Int t1)
                             'Int
                             (error "El tipo no corresponde con el valor"))
                         (error "El tipo no corresponde con el valor"))                
                     (error "El tipo no corresponde con el valor")
                    ))]
                 [(list ,e ,e*)
                  (let*
                      ([types (map (lambda(x)(J x contexto)) (unparse-L10 (list e e*)))]
                    [t (part types)]
                    [eqt (map (lambda(x) (unify t x)) types)])
                    (if (foldr (lambda(x y) (and x y)) #t eqt)
                        `(List of ,t)
                        (error "La lista debe ser homogenea"))
                  )]
                 [(letrec ([,x ,t ,e]) ,body)
                  (let*
                      ([newctx (append (cons (cons x t) '())  contexto)]
                       [t2 (J e newctx)]
                       [S (J body newctx)])
                    (if (unify t t2)
                        S
                        (error "El tipo no corresponde con el valor")))
                  ]
                 [(letfun ([,x ,t ,e]) ,body)
                  (let*
                      ([newctx (append (cons (cons x t) '())  contexto)]
                       [t2 (J e contexto)]
                       [S (J body newctx)])
                    (if (and (unify t t2) (equal? (cadr t) '->))
                        S
                        (error "El tipo no corresponde con el valor")))
                  ]
                 [(if ,e0 ,e1 ,e2)
                  (let*
                      ([t0 (J e0 contexto)]
                       [t1 (J e1 contexto)]
                       [t2 (J e2 contexto)])
                    (if (and (unify t0 'Bool) (unify t1 t2))
                        t1
                        (error "El tipo no corresponde con el valor")))
                  ]
                 [(lambda ([,x ,t]) ,body)
                  (let*
                      ([newctx (append (cons (cons x t) '())  contexto)]
                       [S (J body newctx)])
                    `(,t -> ,S)
                    )
                  ]
                 [(let ([,x ,t ,e]) ,body)
                  (let*
                      ([newctx (append (cons (cons x t) '())  contexto)]
                       [t2 (J e contexto)]
                       [S (J body newctx)])
                    (if (unify t t2)
                        S
                        (error "El tipo no corresponde con el valor")))
                  ]
                 [(,e0 ,e1)
                  (let*
                      ([t0 (J e0 contexto)]
                       [t1 (J e1 contexto)])
                    (if (unify t0 `(,t1 -> ,(last t0)))
                        (last t0)
                        (error "El tipo no corresponde con el valor")))
                  ]))

(define-pass type-infer : L10 (e) -> L10 ()
  (Expr : Expr (expr) -> Expr ()
        [(letrec ([,x ,t ,e]) ,body) `(letrec ([,x ,(J e empty) ,e]) ,body)]
        [(letfun ([,x ,t ,e]) ,body) `(letfun ([,x ,(J e empty) ,e]) ,body)]
        [(let ([,x ,t ,e]) ,body) `(let ([,x ,(J e empty) ,e]) ,body)]))

(define (lookup x ctx)
  (if (equal? (length ctx) 0) "Error variable libre"
      (if (equal? x (car (car ctx)))
          (cdr (car ctx))
          (lookup x (cdr ctx)))))


;;FUNCIONES AUXILIARES

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
;*************************** PRUEBAS ***************************;
;;EJERCICIO 1 Y 2
;; (unparse-L9 (curry (parser-L8 '(lambda ([x Int] [y Int]) (+ x y)))))
;; (unparse-L10 (type-infer (parser-L10 '(letrec ([foo Lambda (lambda ([x Int]) x)]) (foo (const Int 5))))))
;; (unparse-L10 (type-infer (parser-L10 '(let ([x List (list (const Bool #t) (const Bool #f))]) x))))
;; (unparse-L10 (type-infer (parser-L10 '(letfun ([foo Lambda (lambda ([x Bool]) (if x (const Int 1) (const Int 2)))]) foo))))


		
;; PRUEBAS PARA LA FUNCIÓN J			
;(J (parser-L10 'x) `( ,(cons 'x 'Int)))
;; Salida : 'Int
;(J (parser-L10 '(const Int 5)) '())
;; Salida : 'Int
;(J (parser-L10 '(begin x x x (const Int 5) x x x x (const Bool #t))) `( ,(cons 'x 'Int)))
;; Salida : 'Bool
;(J (parser-L10 '(primapp + (const Int 6) (const Int 5))) '())
;; Salida : 'Int
;(J (parser-L10 '(primapp cdr (list (const Int 6) (const Int 5)))) '())
;; Salida : '(List of Int)
;(J (parser-L10 '(primapp car (list (const Int 6) (const Int 5)))) '())
;; Salida : 'Int
;(J (parser-L10 '(primapp length (list (const Int 6) (const Int 5)))) '())
;; Salida : 'Int
;(J (parser-L10 '(if (const Bool #t) x (const Int 5))) `( ,(cons 'x 'Int)))
;; Salida : 'Int
;(J (parser-L10 '(lambda ([x Int]) x)) '())
;; Salida : '(Int → Int)
;(J (parser-L10 '(let ([x Int (const Int 5)]) x)) '())
;; Salida : 'Int
;(J (parser-L10 '(letrec ([x Int (const Int 5)]) x)) '())
;; Salida : 'Int
;(J (parser-L10 '(list)) '())
;; Salida : 'List
;(J (parser-L10 '(list (const Bool #t) (const Bool #f))) '())
;; Salida : '(List of Bool)
;;(J (parser-L10 '(list (list) (list (const Bool #f) (const Bool #t)))) '())
;; Salida : '(List of (List of Bool))
;; CASOS DE ERROR
;(J (parser-L10 '(list (const Int 5) (const Bool #f))) '())
;; Salida : error : Listas homogeneas
; (J (parser-L10 '(list (list) (list (list (const Bool #t) (const Bool #f))) (list (list (const Int 5) (const Int 6))))) '())
;; Salida : error : Listas homogeneas
