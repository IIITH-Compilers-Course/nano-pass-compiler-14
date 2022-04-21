(let ([x (read)])
  (let ([y (not (eq? x 0))])
    (if y
        42
        777)))
