#lang nanopass

;************ EJERCICIO 1 ************;
;************ FRACTAL ************;
;; INTEGRANTES DEL EQUIPO:
;; Cruz Hernández Emmanuel
;; Hernández Martínez Luis Eduardo
;; Vega Monroy Daniela Susana

;; Función que calcula los primeros n elementos de una serie fractal.
;; fractal: number -> (listof number)
(define (fractal n)
  (fractalAuxS (fractalAux n 0)))

;; Función que regresa una lista de números naturales en posiciones
;; pares y * en las impares.
;; fractalAux: number -> number -> (listof (number & '*))
(define (fractalAux n i)
  (cond
    [(= n 0) empty]
    [(= (modulo n 2) 0) (cons i (fractalAux (- n 1) (+ i 1)))]
    [else (cons '* (fractalAux (- n 1) i))]))

;; Función que reemplaza todas las apariciones de '* por un número natural.
;; rellena: (listof (number & '*)) -> number -> number -> (listof number)
(define (rellena l i c)
  (cond
    [(empty? l) empty]
    [(and (not (number? (car l))) (= (modulo i 2) 0)) (cons c (rellena (cdr l) (+ i 1) (+ c 1)))]
    [(not (number? (car l))) (cons '* (rellena (cdr l) (+ i 1) c))]
    [else (cons (car l) (rellena (cdr l) i c))]))

;; Función que permite saber si hay un elemento que no es número en una lista.
;; contiene: (listof (number & '*)) -> boolean
(define (contiene? l)
  (cond
    [(empty? l) #f]
    [(not (number? (car l))) #t]
    [else (contiene? (cdr l))]))

;; Función que aplica fractal y rellena espacios hasta que no haya apariciones de '*.
;; fractalAuxS: (listof (number & '*)) -> (listof number)
(define (fractalAuxS l)
  (cond
    [(contiene? l) (fractalAuxS (rellena l 0 0))]
    [else l]))


;*************************** EJEMPLO ***************************;
'(Fractal de 20 es:)
(fractal 20)