(let ([x (let ([x (let ([x 2]) (+ x 1))]) (+ x 40))]) 
    (let ([y (let ([y (let ([y 4]) (+ x y))]) (+ y (- 48)))]) 
     (let ([z (+ x (+ y 1))])
    (+ z (- 1)))))