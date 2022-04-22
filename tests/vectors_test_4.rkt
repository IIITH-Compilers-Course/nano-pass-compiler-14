(let ([v (vector 1 #t 42)])
    (if (vector-ref v 1) 42 5))