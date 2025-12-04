; empty oneof
(define empty-or ()
    (case 3 
        [(oneof) 'impossible]))

(check-error (empty-or))

(define single-or-lit-succ ()
    (case 3 
        [(oneof 3) 'single]))

(check-expect (single-or-lit-succ) 'single)

(define single-or-lit-fail ()
    (case 3 
        [(oneof 1 2) 'no]))

(check-error (single-or-lit-fail))

(define multi-or-lit-succ ()
    (case 3 
        [(oneof 1 2) 'no]
        [(oneof 3 4) 'yes]))

(check-expect (multi-or-lit-succ) 'yes)

(define single-var-or-succ ()
    (case 3 
        [(oneof x) x]))

(check-expect (single-var-or-succ) 3)

(define multi-var-or-succ ()
    (case 3 
        [(oneof x y z) x]))

(check-expect (multi-var-or-succ) 3)

(define multi-var-or-fail ()
    (case 3 
        [(oneof x y z) z]))

(check-error (multi-var-or-fail))

(define single-constructor-or-fail ()
    (case 3 
        [(oneof (cons x xs)) x]))

(define single-constructor-or-succ ()
    (case '(3 2)
        [(oneof (cons x xs)) x]))

(check-expect (single-constructor-or-succ) 3)

(define multi-constructor-or-succ ()
    (case '(3 2)
        [(oneof (SOME y) (cons x xs)) x]))

(check-expect (multi-constructor-or-succ) 3)

(define multi-constructor-or-fail ()
    (case '(3 2)
        [(oneof (SOME y) (PAIR a b)) y]))

(check-error (multi-constructor-or-fail))

; ocaml's type system would prevent this 
(define name-clash-or-fail ()
    (case (SOMESYM 3)
        [(oneof (SOMENUM y) (SOMESYM y)) (+ y 1)]))

(check-error (name-clash-or-fail))

(define multi-oneof-or-succ ()
    (case '(3 2)
        [(cons (oneof 3 1) x) x]))

(check-expect (multi-oneof-or-succ) 2)


; (let ([result 
;     (case f 
;         [(oneof) 'empty] ; empty oneof
;         [(oneof 3) 'single] ; single literal case 
;         [(oneof x) x] ; single literal case 
;         [(oneof (cons x xs) (SOME x)) x] ; multi-or with different types
;         [(oneof (cons x xs) (NUM xs)) (+ xs 3)]
;                         ; multi-or with different types s.t. an error may occur
;         [(oneof (cons ))]
;         [(oneof x y z) z] ; multi-or with bindings; should error 
;         )])

; (println result))
