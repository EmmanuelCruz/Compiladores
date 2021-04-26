#lang nanopass

;************ EJERCICIO 4 ************;
;************ DOBLE PALÍNDROMO ************;
;; INTEGRANTES DEL EQUIPO:
;; Cruz Hernández Emmanuel
;; Hernández Martínez Luis Eduardo
;; Vega Monroy Daniela Susana

;; Convierte un número a un equivalente en una base dentro de una lista.
;; convertTo: number -> number -> (listof number)
(define (convertTo n base)
  (cond
    [(< n base) (cons n empty)]
    [else (append (convertTo (quotient n base) base)  (list (modulo n base)))]))

;; Función que permite saber si dos listas son iguales.
;; esIgual?: (listof number) -> (listof number) -> boolean
(define (esIgual? l1 l2)
  (cond
    [(and (empty? l1) (empty? l2)) #t]
    [(= (car l1) (car l2)) (esIgual? (cdr l1) (cdr l2))]
    [else #f]))

;; Función que nos permite saber si un número es doble palíndromo.
;; esDoblePalindromo?: number -> boolean
(define (esDoblePalindromo? n)
  (letrec ([lista10 (convertTo n 10)] [lista2 (convertTo n 2)])
    (cond
      [(and (esIgual? lista10 (reverse lista10))
            (esIgual? lista2 (reverse lista2))) #t]
      [else #f])))

;; Función que calcula la suma de los números menores a n que son doble palindromos.
;; sum-pal: number -> number
(define (sum-pal n)
  (sumaPalindromos (- n 1) 0))

;; Función que suma los primeros n doble palindromos.
;; sumaPalindromos: number -> number -> number
(define (sumaPalindromos n c)
  (cond
    [(= n 0) c]
    [(esDoblePalindromo? n) (sumaPalindromos (- n 1) (+ c n))]
    [else (sumaPalindromos (- n 1) c)]))

;*************************** EJEMPLOS ***************************;

'(La suma de todos los números dobles palíndromos antes de 10 es:)
(sum-pal 10)

'(La suma de todos los números dobles palíndromos antes de 30 es:)
(sum-pal 30)

'(La suma de todos los números dobles palíndromos antes de 40 es:)
(sum-pal 40)

'(La suma de todos los números dobles palíndromos antes de 25 es:)
(sum-pal 25)