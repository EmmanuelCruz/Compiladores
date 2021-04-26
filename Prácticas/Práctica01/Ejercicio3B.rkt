#lang nanopass

;************ EJERCICIO 3B ************;
;************ PRODUCTO DE FACTORES PRIMOS ************;
;; INTEGRANTES DEL EQUIPO:
;; Cruz Hernández Emmanuel
;; Hernández Martínez Luis Eduardo
;; Vega Monroy Daniela Susana

;; Funcion que calcula una lista con los primos de un numero
;; prime-fac: number -> (listof number)
(define (prime-fac n)
  (quitarRepetidos (descomposicionPrimos n) '()))

;; Función que determina si un número es primo o no.
;; esPrimo?: number -> boolean
(define (esPrimo? n)
  (letrec ([evaluaPrimo (lambda (c)
                          (cond
                            [(= n 1) #f]
                            [(= n 2) #t]
                            [(= n c) #t]
                            [(= (modulo n c) 0) #f]
                            [else (evaluaPrimo (+ c 1))]))])
    (evaluaPrimo 2)))

;; Función que regresa una lista con los primeros n números primos.
;; creaListaPrimos: number -> (listof number)
(define (creaListaPrimos n)
  (letrec ([creaListaEnteros (lambda (c)
                               (cond
                                 [(= n c) (cons c empty)]
                                 [else (cons c (creaListaEnteros (+ c 1)))]))])
    (let ([l (creaListaEnteros 1)])
      (filter esPrimo? l))))

;; Función que regresa una lista con la descomposición en números primos de un número n.
;; descomposicionPrimos: number -> (listof number)
(define (descomposicionPrimos n)
  (let ([primos (creaListaPrimos n)])
    (letrec ([buscaDivisorPrimo (lambda (l n1)
                                  (cond
                                    [(empty? l) empty]
                                    [(= (modulo n1 (car l)) 0) (cons (car l) (buscaDivisorPrimo l (quotient n1 (car l))))]
                                    [else (buscaDivisorPrimo (cdr l) n1)]))])
      (buscaDivisorPrimo primos n))))

;Funcion auxiliar que quita los repetidos de una lista,multiplicandolos
;;quitarRepetidos: (listof number),(listof number) -> (listof number)
(define (quitarRepetidos listal resul)
  (let loop1 ([lista listal] [resu resul])
    (if (= (length lista) 0)
      (reverse resu)
      (let ([n (car lista)])
        (if (empty? n) (loop1 (cdr lista) resu)
        (let loop2 ([aux lista] [contador 1])
          (if (= (length aux) 0)
              (loop1 (map (lambda (r) (if (= r n) '() r)) (cdr lista)) (cons contador resu))
              (let-values ([(actual) (car aux)])
                (if (= n actual) (loop2 (cdr aux) (* contador n)) (loop2 (cdr aux) contador))))))))))

;*************************** EJEMPLOS ***************************;
'(La descomposición de primos de 90 es:)
(prime-fac 90)

'(La descomposición de primos de 24 es:)
(prime-fac 24)

'(La descomposición de primos de 18 es:)
(prime-fac 18)

'(La descomposición de primos de 69 es:)
(prime-fac 69)