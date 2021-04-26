#lang nanopass

(require nanopass/base)

;; Definición del Lenguaje Fuente
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
    pr
    c
    l
    t
    s
    (pr c* ... c)
    (begin e* ... e)
    (if e0 e1)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (e0 e1 ...)))

;; Definición del predicado que verifica las variables
(define (variable? x)
  (symbol? x))

;; Definición del predicado que verifica los tipos
(define (type? x)
  (or
   (symbol? x)
   (boolean? x)
   (integer? x)
   (list? x)
   (string? x)))

;; Definición del predicado que verifica las constantes
(define (constant? x)
  (or
   (symbol? x)
   (boolean? x)
   (integer? x)))

;; Definición del predicado que verifica las primitivas
(define (primitive? x)
  (or (equal? x +)
      (equal? x -)
      (equal? x *) 
      (equal? x /)
      (equal? x 'and)
      (equal? x 'or)
      (equal? x 'length)
      (equal? x 'car)
      (equal? x 'cdr)))

;; Proceso del compilador encargado de hacer explicitas las expresiones
;; begin en el cuerpo de lambda, let y letrec
(define-pass make-explicit : LF (ir) -> LF ()
  (Expr : Expr (ir) -> Expr ()
    [,c `',c]
    [(lambda ([,x* , t*] ...) ,[body*] ... ,[body])
     `(lambda ([,x*, t*] ...) (begin ,body* ... ,body))]
    [(let ([,x* , t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t*, e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* , t*,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* , t*, e*] ...) (begin ,body* ... ,body))]))

(define-language L1
  (extends LF)
  (terminals
   (+ (void (void))))
   (Expr (e body)
         (- (if e0 e1))))

(define-language L2
  (extends L1)
  (terminals
   (- (string (s))))
  (Expr (e body)
         (- s)))

(define-pass remove-one-armed-if : LF (e) -> L1 ()
  (Expr : Expr (e) -> Expr ()
      [(if, [e0] , [e1])
       `(if ,e0 ,e1 (void))]))

(define-pass remove-string : L1 (e) -> L2 ()
  (Expr : Expr (e) -> Expr ()
      [,s (string->list s)]))

(define dicoVar (make-hash))
(define-pass rename-var : L2 (e r lst) -> L2 ()
  (Expr : Expr (e) -> Expr ()
        [,x  (if (and (dict-has-key? dicoVar x) (not (void? x))) (hash-ref dicoVar x) (dict-set! dicoVar x (format "x ~a" r)))]
        [(if ,[e0 (set! r (+ r 1)) -> e0] ,[e1] ,[e3]) `(if ,e0 ,e1 ,e3)]))



;; Función parser del lenguaje LF
(define-parser parser-LF LF)

(define-parser parser-L1 L1)

(define-parser parser-L2 L2)

