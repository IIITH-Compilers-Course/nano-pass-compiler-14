(let ([a 42]) ;; test constant propagation
  (let ([b a])
    (let ([c b])
      (let ([d c])
        d))))
