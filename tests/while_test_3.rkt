(let ([sum 42])
(let ([i 5])
(begin
(while (and #t #f)
(begin
(set! sum (+ sum i))
(set! i (- i 1))))
sum)))
