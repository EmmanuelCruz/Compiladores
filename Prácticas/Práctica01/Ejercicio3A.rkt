#lang nanopass

;************ EJERCICIO 3A ************;
;************ ÁRBOL DE DIVISORES ************;
;; INTEGRANTES DEL EQUIPO:
;; Cruz Hernández Emmanuel
;; Hernández Martínez Luis Eduardo
;; Vega Monroy Daniela Susana

;; Definicion de la estructura Árbol
(define (make-tree dato lista-hijos) (cons (list dato) (list lista-hijos)))

;; Función para encontrar el árbol de divisores de un número n.
;; div-tree: number -> (listof number)
(define (div-tree n)
  (construyeArbol n))

;; Función que calcula los divisores de un número y los guarda en el árbol.
;; factors: number -> (listof number)
(define (construyeArbol factor)
  (let tailfactors ([dividendo factor] [primo 2])
      (let-values ([(cociente residuo) (quotient/remainder dividendo primo)])
        (if (= cociente 1) (list dividendo) 
            (if (zero? residuo)
                (cons dividendo (make-tree primo (tailfactors cociente primo)))
                (tailfactors dividendo (add1 primo)))))))

;*************************** EJEMPLO ***************************;
'(El árbol de divisores de 20 es)
(div-tree 20)