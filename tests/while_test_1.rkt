(let ([x 10])
(let ([y 0])
(+ (+ (begin (set! y (read)) x) (begin (set! x (read)) y)) x)))