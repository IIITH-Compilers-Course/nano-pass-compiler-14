(let ([i 0]) 
    (let ([v (vector 1 2 3
        (begin
            (while (< i 42)
                (begin
                (set! i (+ i 1))
                (let ([w (vector 1 2 3)])
                    (vector-ref w 1))))
            i)
            )])
        (vector-ref v 3)))