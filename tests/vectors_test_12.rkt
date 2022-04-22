(let ([v (vector 1 2 3)])
  (let ([i 0])
      (begin
       (while (< i 42)
           (begin
           (set! i (+ i 1))
           (vector-set! v 1 i)
           (vector-ref v 1)
           (vector-set! v 2 -1)
             )
            )
            (vector-ref v 1))))