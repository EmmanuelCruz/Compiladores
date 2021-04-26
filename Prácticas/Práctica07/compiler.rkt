#lang nanopass

(require nanopass/base)
(require racket/set)

;;PREDICADOS

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x) (memq x '(+ - * / length car cdr and or not)))

(define (primitive2? x) (memq x '(+ - * / length car cdr)))

(define (arraylength? x) (integer? x))

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

(define-language L12
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (type (t)))
  (Expr (e body)
    x
    (const t c)
    (begin e* ... e)
    (primapp pr e* ...)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body)
    (let ([x t e]) body)
    (letrec ([x t e]) body)
    (letfun ([x t e]) body)
    (list e* ...)
    (e0 e1 ...)))

(define-parser parser-L12 L12)

(define-language L13
  (extends L12)
  (terminals
   (+ (arraylength (len))))
  (Expr (e len t)
         (- (list e* ...))
         (+
          c
          (array len t [e* ...]))))

(define-parser parser-L13 L13)

;; Encuentra el tipo mas particular de una lista de tipos. Para la inferencia de las listas.
(define (part lst)
  (if (equal? (car lst) 'List)
    (part (cdr lst))
    (car lst)))

(define (lookup x ctx)
  (if (equal? (length ctx) 0) (error "Error de variable libre")
      (if (equal? x (car (car ctx)))
          (cdr (car ctx))
          (lookup x (cdr ctx)))))

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

(define (J expr contexto)
  (nanopass-case (L13 Expr) expr
                 [,x (lookup x contexto)]
                 [(const ,t ,c) `,t]
                 [(begin ,e* ... ,e)
                  (let*
                      ([types (map (lambda(x)(J x contexto)) (unparse-L10 e*))])
                    (J e contexto))]
                 [(primapp ,pr ,e* ...)
                  (cond
                    [(= (length e*) 1)
                     (let*
                         ([t (J (first e*) contexto)])
                       (if (equal? 'car (unparse-L13 pr))
                           (if (list? t)
                               (if (equal? (car t) 'List)
                                   (last t)
                                   (error "El tipo no corresponde con el valor"))
                               ((error "El tipo no corresponde con el valor")))
                           (if (equal? 'cdr (unparse-L13 pr))
                               (if (list? t)
                                   (if (equal? (car t) 'List)
                                       t
                                       (error "El tipo no corresponde con el valor"))
                                   ((error "El tipo no corresponde con el valor")))
                               (if (equal? 'length (unparse-L13 pr)) (if (list? t)
                                                                         (if (equal? (car t) 'List)
                                                                             'Int
                                                                             (error "El tipo no corresponde con el valor"))
                                                                         ((error "El tipo no corresponde con el valor")))
                                   (error "El tipo no corresponde con el valor")))))]
                    [else
                     (let*
                         ([t (J (first e*) contexto)]
                          [t1 (J (second e*) contexto)])
                       (if
                        (or (equal? '+ (unparse-L13 pr))
                            (equal? '* (unparse-L13 pr))
                            (equal? '/ (unparse-L13 pr))
                            (equal? '- (unparse-L10 pr)))
                        (if (unify 'Int t)
                            (if (unify 'Int t1)
                                'Int
                                (error "El tipo no corresponde con el valor"))
                            (error "El tipo no corresponde con el valor"))
                        (error "El tipo no corresponde con el valor")))])]
                 [(if ,e0 ,e1 ,e2)
                  (let*
                      ([t0 (J e0 contexto)]
                       [t1 (J e1 contexto)]
                       [t2 (J e2 contexto)])
                    (if (and (unify t0 'Bool) (unify t1 t2))
                        t1
                        (error "El tipo no corresponde con el valor")))]
                 [(lambda ([,x* ,t*] ...) ,body)
                  (let*
                      ([newctx (append (cons (cons (first x*) (first t*)) '())  contexto)]
                       [S (J body newctx)])
                    S)]
                 [(let ([,x ,t ,e]) ,body)
                  (let*
                      ([newctx (append (cons (cons x t) '())  contexto)]
                       [S (J body newctx)])
                    `(,t -> ,S))]
                 [(letrec ([,x ,t ,e]) ,body)
                  (let*
                      ([newctx (append (cons (cons x t) '())  contexto)]
                       [t2 (J e newctx)]
                       [S (J body newctx)])
                    (if (unify t t2)
                        S
                        (error "El tipo no corresponde con el valor")))]
                 [(letfun ([,x ,t ,e]) ,body)
                  (let*
                      ([newctx (append (cons (cons x t) '())  contexto)]
                       [t2 (J e contexto)]
                       [S (J body newctx)])
                    (if (and (unify t t2) (equal? (cadr t) '->))
                        S
                        (error "El tipo no corresponde con el valor")))]
                 [(array ,len ,t [,e* ...]) `,t]
                 [(,e0 ,e1 ...)
                  (let*
                      ([t0 (J e0 contexto)]
                       [t1 (J e1 contexto)])
                    (if (unify t0 `(,t1 -> ,(last t0)))
                        (last t0)
                        (error "El tipo no corresponde con el valor")))]))

;; Práctica 07

(define-pass list-to-array : L12 (ir) -> L13 ()
  (definitions
    (define (createList expresiones)
      (cond
        [(= (length expresiones) 1)
         (list (third (first expresiones)))]
        [else
         (append (list (third (first expresiones))) (createList (rest expresiones)))]))
    (define (createTypeList expresiones)
      (cond
        [(= (length expresiones) 1)
         (list (second (first expresiones)))]
        [else
         (append (list (second (first expresiones))) (createTypeList (rest expresiones)))])))
  (Expr : Expr (ir) -> Expr()
        [(list ,e* ...) (let*
                            ([lista (map parser-L13 (createList (first (map unparse-L12 e*))))]
                             [types (createTypeList (first (map unparse-L12 e*)))]
                             [t (part types)])
                          `(array ,(length lista) ,t ,(parser-L13 lista)))]))

(define contexto (list (cons 'x 'Int)))

(define numvar 0)

(define (stringType x)
  (cond
    [(integer? x) (number->string x)]
    [(char? x) (symbol->string x)]
    [(boolean? x) (format "~a" x)]))

;(Bool Char Int List String Lambda)

(define (cType x)
  (cond
    [(equal? x 'Bool) "boolean"]
    [(equal? x 'Char) "char"]
    [(equal? x 'Int) "int"]
    [(equal? x 'String) "char*"]))
      
(define (c expr)
  (nanopass-case (L13 Expr) expr
                 [,x (string-append (cType (lookup x contexto)) " " (symbol->string x))]
                 [(const ,t ,c) (if(equal? (unparse-L13 c) '#t) "1" (if(equal? (unparse-L13 c) '#f) "0" (string-append (stringType c))))]
                 [(begin ,e* ... ,e) (display (string-append
                                                    (foldr string-append ""
                                                           (map (lambda (x) (string-append (c x) ";\n")) e*))
                                                    (c e) "\n"))]
                 [(primapp ,pr ,e* ...) (cond
                                          [(memq pr '(+ - * /))
                                           (letrec ([identifyVar (lambda (x)
                                                                   (nanopass-case (L13 Expr) x
                                                                                  [,x (symbol->string x)]
                                                                                  [(const ,t ,c) (stringType c)]))]
                                                    [val1 (identifyVar (first e*))]
                                                    [val2 (identifyVar (second e*))])
                                           (string-append val1 (symbol->string pr) val2))]
                                          [(equal? pr 'length)
                                           (nanopass-case (L13 Expr) (first e*)
                                                          [(array ,len ,t [,e* ...]) (number->string len)])]
                                          [(equal? pr 'car)
                                           (nanopass-case (L13 Expr) (first e*)
                                                          [(array ,len ,t [,e* ...]) (c (first e*))])]
                                          [(equal? pr 'cdr)
                                           (nanopass-case (L13 Expr) (first e*)
                                                          [(array ,len ,t [,e* ...])
                                                           (let ([valores (foldr string-append ""
                                                                                 (map (lambda (x) (string-append (c x) ",")) (cdr e*)))])
                                                             (string-append "{"
                                                                            (substring valores 0 (- (string-length valores) 1))
                                                                            "}"))])])]
                 [(if ,e0 ,e1 ,e2) (display (string-append "if(" (c e0) "){\n" (c e1) "\n} else {\n" (c e2) "\n}"))]
                 [(let ([,x ,t ,e]) ,body)
                  (if (and (list? (unparse-L13 e)) (equal? (car (unparse-L13 e)) 'array))
                      ;Caso donde es un array
                      (cond
                      [(equal? t 'Int) (display (string-append "int " (c x) " = " (c e) ";"))]
                        [(equal? t 'Char) (display (string-append "char " (c x) " = " (c e) ";"))]
                        [(equal? t 'Bool) (display (string-append "int " (c x) " = " (c e) ";"))]
                      ;Caso donde no es un array
                      (cond 
                        [(equal? t 'Int) (display (string-append "int " (c x) " = " (c e) ";"))]
                        [(equal? t 'Char) (display (string-append "char " (c x) " = " (c e) ";"))]
                        [(equal? t 'Bool) (display (string-append "int " (c x) " = " (c e) ";"))]
                        [else (display (string-append (symbol->string (last t)) (c x) " = " (c e) ";"))])
                 )]
                 [(letrec ([,x ,t ,e]) ,body1)
                  (nanopass-case (L13 Expr) e
                                 [(lambda ([,x* ,t*] ...) ,body)
                                  (let ([tipo (J e '())])
                                    (string-append
                                     (cType tipo)
                                     " "
                                     (symbol->string x)
                                     "("
                                     (traduceParametros x* t*)
                                     "){\n"
                                     (c body)
                                     ";\n};\n\n"
                                     (c body1)))])]
                 [(letfun ([,x ,t ,e]) ,body)
                  (nanopass-case (L13 Expr) e
                                 [(lambda ([,x* ,t*] ...) ,body)
                                  (let ([tipo (J e '())])
                                    (string-append
                                     (cType tipo)
                                     " "
                                     (symbol->string x)
                                     "("
                                     (traduceParametros x* t*)
                                     "){\n"
                                     (c body)
                                     ";\n};"))])]
                 [(array ,len ,t [,e* ...])
                  (let ([valores (foldr string-append ""
                                (map (lambda (x) (string-append (c x) ",")) e*))])
                    (string-append "{"
                                   (substring valores 0 (- (string-length valores) 1))
                                   "}"))]
                 [(,e0 ,e1 ...)
                  (nanopass-case (L13 Expr) e0
                                 [(letfun ([,x ,t ,e]) ,body) (string-append (symbol->string x) "" (let ([valores (foldr string-append ""
                                                                                                                         (map (lambda (x) (string-append (c x) ",")) e1))])
                                                                                                     (string-append "("
                                                                                                                    (substring valores 0 (- (string-length valores) 1))
                                                                                                                    ")")) ";\n" (c e0) "\n")]
                                 [(letrec ([,x ,t ,e]) ,body) (string-append (symbol->string x) "" (let ([valores (foldr string-append ""
                                                                                                                         (map (lambda (x) (string-append (c x) ",")) e1))])
                                                                                                     (string-append "("
                                                                                                                    (substring valores 0 (- (string-length valores) 1))
                                                                                                                    ")")) ";\n" (c e0))]
                                 [else (string-append (symbol->string e0) ""(let ([valores (foldr string-append ""
                                                                                                                         (map (lambda (x) (string-append (c x) ",")) e1))])
                                                                                                     (string-append "("
                                                                                                                    (substring valores 0 (- (string-length valores) 1))
                                                                                                                    ")")) ";")])]))

(define (traduceParametros parametros tipos)
  (cond
    [(= (length parametros) 1) (string-append (cType (car tipos)) " " (format "~a" (car parametros)))]
    [else (string-append (cType (car tipos)) " " (format "~a" (car parametros)) ", " (traduceParametros (cdr parametros) (cdr tipos)))]))

;;;PRUEBAS:
; (unparse-L13 (list-to-array (parser-L12 '(list ((const Int 1) (const Int 2) (const Int 3) (const Int 4))))))
; (c (parser-L13 'x))
; (c (parser-L13 '(const Int 5)))
; (c (parser-L13 '(const Bool #t)))
; (c (parser-L13 '(begin x (const Int 4) x (const Int 5) (primapp - (const Int 9) (const Int 7)))))
; (c (parser-L13 '(primapp + (const Int 5) (const Int 5))))
; (display (c (parser-L13 '(letrec ([multiplica Lambda (lambda ([x Int] [y Int]) (primapp * (const Int 3) (const Int 6)))]) (letrec ([suma Lambda (lambda ([x Int] [y Int]) (primapp + (const Int 1) (const Int 4)))]) (const Bool #f))))))
; (display (c (parser-L13 '(letfun ([foo Lambda (lambda ([x Int] [y Int]) (primapp * x x))]) foo))))
; (c (parser-L13 '(array 2 Int [(const Int 234) (const Int 6)])))
; (c (parser-L13 '(if (const Bool #t) (const Bool #t) (const Bool #t))))
; (c (parser-L13 '(let ([x Int (array 1 Int ((const Int 5) (const Int 6)))]) (const Int 5))))
; (display (c (parser-L13 '((letfun ([foo Lambda (lambda ([x Int] [y Int]) (primapp * x x))]) foo) (const Int 5)))))
; (display (c (parser-L13 '(foo (const Int 5)))))
; 
