(let ([x (+ (if (and #t #t) 42 2) (let ([x (+ 42 (- 10))]) 
                 (+ x 10)))]) 
  (+ x (- 42)))