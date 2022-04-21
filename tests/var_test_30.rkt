(let ([a (read)]) ;; test copy propagation
  (let ([b a])
    (let ([c b])
      (let ([d c])
        d))))
