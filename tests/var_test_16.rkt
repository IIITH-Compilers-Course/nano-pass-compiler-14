(let ([x (+ (read) (read))])
    (+ (let ([x (- x)]) (+ x (read)) ) x ))