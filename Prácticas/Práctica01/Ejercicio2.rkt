#lang nanopass

(require gregor)

;************ EJERCICIO 2 ************;
;************ SIGLO XX ************;
;; INTEGRANTES DEL EQUIPO:
;; Cruz Hernández Emmanuel
;; Hernández Martínez Luis Eduardo
;; Vega Monroy Daniela Susana

;; Cuenta cuántos viernes ha tenido un periodo determinado.
;; cuantosViernes?: date -> date -> number
(define (cuantosViernes? in fin)
  (letrec ([buscaViernes (lambda (puntero contador)
                           (let ([fechaActual (+days in puntero)])
                             (cond
                               [(date>? fechaActual fin) contador]
                               [(friday? fechaActual) (buscaViernes (+ puntero 1) (+ contador 1))]
                               [else (buscaViernes (+ puntero 1) contador)])))])
    (buscaViernes 0 0)))

;; Cuenta cuántos días domingos han sido primero en un periodo determinado.
;; cuantosDomingoPrimero?: date -> date -> number
(define (cuantosDomingoPrimero? in fin)
  (letrec ([buscaDomingoPrimero (lambda (puntero contador)
                           (let ([fechaActual (+days in puntero)])
                             (cond
                               [(date>? fechaActual fin) contador]
                               [(and (sunday? fechaActual) (= (->day fechaActual) 1))
                                (buscaDomingoPrimero (+ puntero 1) (+ contador 1))]
                               [else (buscaDomingoPrimero (+ puntero 1) contador)])))])
    (buscaDomingoPrimero 0 0)))

;; Definimos una fecha: elprimer día del siglo XX
(define inicio (date 1901 1 1))

;; Definimos una fecha: el último día del siglo XX
(define final (date 2000 12 31))

;************ PRIMERA PREGUNTA ************;

'(¿Cuántos viernes tiene este periodo?)
(cuantosViernes? inicio final)

;************ SEGUNDA PREGUNTA ************;

'(¿Cuántos días 1 han sido domingo?)
(cuantosDomingoPrimero? inicio final)