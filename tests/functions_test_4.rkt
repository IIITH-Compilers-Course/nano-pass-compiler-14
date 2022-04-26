(define (mapvec [f : (Integer -> Integer)]
                 [v : (Vector Integer Integer)])
       : (Vector Integer Integer)
  (vector (f (vector-ref v 0)) (f (vector-ref v 1))))
(define (add1 [x : Integer]) : Integer
  (+ x 1))
(vector-ref (mapvec add1 (vector 0 41)) 1)
