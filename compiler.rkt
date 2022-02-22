#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
        (define var_sampled (gensym x))
        (define env^ (dict-set env x var_sampled))
        (Let var_sampled ((uniquify-exp env) e) ((uniquify-exp env^) body))
      ]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (rco_atm e)
    (match e
        [(Var n) #t]
        [(Int n) #t]
        [_ #f]
    )
)

(define (rco_exp e)
    (match e
        [(Var n) (Var n)]
        [(Int n) (Int n)]
        [(Prim 'read '()) (Prim 'read '())]
        [(Prim op (list e1 e2))
            (cond
                [(and (rco_atm e1) (rco_atm e2)) e]
                [(and (rco_atm e1) (not (rco_atm e2))) 
                    (define var1 (gensym))
                    (Let var1 (rco_exp e2) (Prim op (list e1 (Var var1))))
                ]
                [(and (rco_atm e2) (not (rco_atm e1))) 
                    (define var1 (gensym))
                    (Let var1 (rco_exp e1) (Prim op (list e2 (Var var1))))
                ]
                [else e
                    (define var1 (gensym))
                    (Let var1 (rco_exp e1) (Prim op (list (rco_exp e2) (Var var1))))
                ]
            )
        ]
        [(Prim '- (list e1)) 
            (cond
                [(rco_atm e1) e]
                [else 
                    (define var1 (gensym))
                    (Let var1 (rco_exp e1) (Prim '- (list (Var var1))))
                ]
            )
        ]
        [(Let x e body) (Let x (rco_exp e) (rco_exp body))]
    )
)

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) 
        (Program info (rco_exp e))]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (error "TODO: code goes here (explicate-control)"))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (error "TODO: code goes here (select-instructions)"))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
     ("uniquify", uniquify, interp-Lvar)
     ("remove complex opera*", remove-complex-opera*, interp-Lvar)
     ;; ("explicate control" ,explicate-control ,interp-Cvar)
     ;; ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

