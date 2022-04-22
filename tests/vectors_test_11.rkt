(let ([v (vector 1 2 3)])
  (let ([i 0])
      (begin
       (while (< i 42)
           (begin
           (set! i (+ i 1))
           (vector-set! v 1 i)
           (vector-set! v 2 -1)
           (let ([w (vector 1 2 3)])
            (vector-set! v 0 (+ 10 (vector-ref w 2))))
             )
            )
            (vector-ref v 1))))