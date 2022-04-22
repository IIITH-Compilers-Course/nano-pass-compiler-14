(let ([v (vector 1 2 42)]) 
    (let ([w (vector #t (vector-ref v 2) 3)]) 
        (vector-ref w 1)))