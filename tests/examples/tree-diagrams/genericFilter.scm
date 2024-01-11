(define genericFilter (xs test)
    (case xs
        ['() '()]
        [(cons x xr)
            (if (test xr)
                (cons x (genericFilter xr))
                (genericFilter xr))]))
