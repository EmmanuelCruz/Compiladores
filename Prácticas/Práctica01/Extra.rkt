#lang nanopass

;************ EJERCICIO EXTRA ************;
;************ FIBONACCI ************;
;; INTEGRANTES DEL EQUIPO:
;; Cruz Hernández Emmanuel
;; Hernández Martínez Luis Eduardo
;; Vega Monroy Daniela Susana

;; Función que regresa el número n de la sucesión fibonacci.
;; fibonacci: number -> number
(define (fibonacci n)
  (fibonacciCola n 1 0))

;; Función auxiliar que calula fibonacci con recursión de cola.
;; fibonacciCola: number -> number -> number -> number
(define (fibonacciCola n acc1 acc2)
  (cond
    [(= n 0) acc2]
    [(= n 1) acc1]
    [else (fibonacciCola (- n 1) (+ acc1 acc2) acc1)]))

;; Función que regresa la posición del primer término en tener n dígitos.
;; primerDigitoFibonacci: number -> number
(define (primerDigitoFibonacci n)
  (encuentraDigito (expt 10 (- n 1)) 0))

;; Función que encuentra el primer termino de la serie fibonacci en tener n dígitos.
;; encuentraDigito: number -> number -> number
(define (encuentraDigito n c)
  (cond
    [(= n 1) 0]
    [(> (fibonacci c) n) c]
    [else (encuentraDigito n (+ c 1))]))

;*************************** RESPUESTA A LA PREGUNTA ***************************;

'(El primer término en tener 1000 dígitos en fibonacci es:)
(primerDigitoFibonacci 1000)

'(Ese número de 1000 dígitos es:)
(fibonacci (primerDigitoFibonacci 1000))