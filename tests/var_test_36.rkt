(let ([x (read)])
  (let ([y (read)])
    (+ x
       (let ([z (read)])
         (+ z (- y))))))

