
(define (minus [n : Integer] [m : Integer]) : Integer
  (+ n (- m)))

(define (mapvector [f : (Integer Integer -> Integer)]
                    [v : (Vector Integer)]) : (Vector Integer)
  (vector (f (vector-ref v 0) 1)))

(vector-ref (mapvector minus (vector 43)) 0)


