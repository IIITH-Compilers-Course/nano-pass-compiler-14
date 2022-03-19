#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "interp.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
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
    [(Var v) (Var v)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Let var e1 e2) (Let var (pe-exp e1) (pe-exp e2))]
))


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
        (define var1 (gensym x))
        (define env^ (dict-set env x var1))
        (Let var1 ((uniquify-exp env) e) ((uniquify-exp env^) body))
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
                    (define var2 (gensym))
                    (Let var1 (rco_exp e1) (
                        Let var2 (rco_exp e2) (Prim op (list (Var var1) (Var var2)))
                    ))
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

(define (explicate_tail e)
    (match e
        [(Var x) (Return (Var x))]
        [(Int n) (Return (Int n))]
        [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
        [(Prim op es) (Return (Prim op es))]
        [else (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e x cont)
    (match e
        [(Var xvar) (Seq (Assign (Var x) (Var xvar)) cont)]
        [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
        [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
        [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
        [else (error "explicate_assign unhandled case" e)]))

;; explicate-control : R1 -> C0
(define (explicate_control p)
    (match p
    [(Program info body) (CProgram info (list (cons 'start (explicate_tail body))))]))

(define (select-instructions-atomic e)
    (match e
        [(Int n) (Imm n)]
        [(Var n) (Var n)]
    )
)

(define (select-instructions-statement stm)
    (match stm
        ['() '()]
        [(Seq (Assign var exp) t*) (append (select-instructions-assignment exp var) (select-instructions-statement t*))]
        [(Return exp) (append (select-instructions-assignment exp (Reg 'rax)) (list (Jmp 'conclusion)))]
    )
)

(define (select-instructions-assignment e x)
    (match e
        [(Int i) (list (Instr 'movq (list (select-instructions-atomic e) x)))]
        [(Var v) (list (Instr 'movq (list e x)))]
        [(Prim '+ (list e1 e2))
            (cond 
              [(equal? x e1) (list (Instr 'addq (list (select-instructions-atomic e2) x)))]
              [(equal? x e2) (list (Instr 'addq (list (select-instructions-atomic e1) x)))]
              [else (list (Instr 'movq (list (select-instructions-atomic e1) x))
                          (Instr 'addq (list (select-instructions-atomic e2) x)))]
            )
        ]
        [(Prim '- (list e1 e2))
            (cond 
                [(equal? x e1) (list (Instr 'subq (list (select-instructions-atomic e2) x)))]
                [(equal? x e2) (list (Instr 'subq (list (select-instructions-atomic e1) x)))]
                [else (list (Instr 'movq (list (select-instructions-atomic e1) x))
                      (Instr 'subq (list x (select-instructions-atomic e2))))]
            )
        ]
        [(Prim '- (list e1))
            (list (Instr 'movq (list (select-instructions-atomic e1) x))
                  (Instr 'negq (list x)))
        ]
        [(Prim 'read '()) 
            ;;; default argument of Callq
            (list (Callq 'read_int 0)  
                  (Instr 'movq (list (Reg 'rax) x)))
        ]
    )
)

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info e) 
        (X86Program info `((start . ,(Block info (select-instructions-statement (dict-ref e 'start))))))]))

(define (assign-homes-map vars [offset -8] [varmap '()])
    (match vars
        ['() varmap]
        [(cons a c) (assign-homes-map c (- offset 8) (dict-set varmap (car a) offset))]
    )   
)

(define (assign-homes-convert e varmap)
    (match e
        [(Var e) (Deref 'rbp (dict-ref varmap e))]
        [_ e]
    )
)

(define (assign-homes-mapvars varmap stm)
    (match stm
        [(Instr op args) (Instr op (map (lambda (x) (assign-homes-convert x varmap)) args))]
        [(Block info body) (Block info (for/list ([nxt body]) (assign-homes-mapvars varmap nxt)))] 
        [_ stm]
    )
)

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info e) (X86Program (dict-set info 'stack-space (* 8 (length (dict-ref info 'locals-types))) ) (map (lambda (x) `(,(car x) . ,(assign-homes-mapvars (assign-homes-map (dict-ref info 'locals-types)) (cdr x)))) e))]))

(define (patch-instructions-convert stm)
    (match stm
        [(Instr op (list (Deref 'rbp offset_1) (Deref 'rbp offset_2))) 
            (list
                (Instr 'movq (list (Deref 'rbp offset_1) (Reg 'rax)))
                (Instr op (list (Reg 'rax) (Deref 'rbp offset_2)))
            )
        ]
        [(Block info body) (Block info (append-map patch-instructions-convert body))] 
        [_ (list stm)]
    )
)

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info es) (X86Program info (map (lambda (x) `(,(car x) . ,(patch-instructions-convert (cdr x)))) es))]))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
    (match p
        [(X86Program info es) (X86Program info `( 
            (start . ,(dict-ref es 'start))
            (main . ,(Block info (list (Instr 'pushq (list (Reg 'rbp))) (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))) (Instr 'subq (list (Imm (align (dict-ref info 'stack-space) 16)) (Reg 'rsp))) (Jmp 'start))))
            (conclusion . ,(Block info (list (Instr 'addq (list (Imm (align (dict-ref info 'stack-space) 16)) (Reg 'rsp))) (Instr 'popq (list (Reg 'rbp))) (Retq))))
        ))
]))

(define (check-int e)
    (if (not (Imm? e) ) #t #f)
)

(define (list-to-set lst)
    (list->set (for/list ([e lst] #:when (check-int e)) e))  
)


(define (extract-reads instr)
    (
        match instr
        [(Instr 'movq es) (list-to-set (list (car es))) ]
        [(Instr 'addq es) (list-to-set es)]
        [(Instr 'subq es) (list-to-set es)]
        [(Instr 'negq es) (list-to-set es)]
        [(Jmp _) (set (Reg 'rax) (Reg 'rsp))]
        [_ (set)]
    )
)

(define (extract-writes instr)
    (
        match instr
        [(Instr 'movq es) (list->set (cdr es))]
        [(Instr 'addq es) (list->set (cdr es))]
        [(Instr 'subq es) (list->set (cdr es))]
        [(Instr 'negq es) (list->set es)]
        [_ (set)]
    )
)

;; auxiliary function that takes a list of instructions and an initial live-after set (typically empty) and returns the list of live-after sets
(define (get-live-after listOfInstructions)
    (
        match listOfInstructions
        [(list a) (list (extract-reads a ) ) ] 
        [_ (let ([list-live-after (get-live-after (cdr listOfInstructions))])
            (append
                (list
                    (set-union (extract-reads (car listOfInstructions)) 
                        (set-subtract (car list-live-after)  
                            (extract-writes (car listOfInstructions)) 
                        )
                    )
                )
                list-live-after
            ))
        ]
    )
)

;; uncover_live 
(define (uncover-live p)
    (
        match p
        [(X86Program info body) (X86Program info (for/list ([func body]) (cons (car func) (match (cdr func) [(Block info bbody) (Block (dict-set info 'live-after (get-live-after bbody)) bbody)]))))]
    )
) 

(define (add-edges d curInstr curLive interference-graph)
    (for ([v curLive]) 
        (when (not (eq? v d)) 
            (match curInstr
                [(Instr 'movq (list src dest)) (when (not (eq? src v)) (add-edge! interference-graph v d))]
                [_ (add-edge! interference-graph v d)]
            )
        )
    )
    interference-graph
)

(define (set-to-list s) 
    (for/list ([e s]) e)
)

(define (build-graph list-live-after listOfInstructions [interference-graph (undirected-graph '()) ]) 
    (match listOfInstructions
        ['() 
        (print-graph interference-graph)
        interference-graph]
        [_ 
            (define curInstr (car listOfInstructions))
            (define curWrite (set-to-list (extract-writes curInstr)) )
            (define curLive (car list-live-after))
            
            (match curWrite 
                ['() (build-graph (cdr list-live-after) (cdr listOfInstructions) interference-graph )]
                [(list a) (build-graph (cdr list-live-after) (cdr listOfInstructions) (add-edges a curInstr curLive interference-graph) )]
            )
         ])
)

(define (build-interference p)
  (match p
    [(X86Program info body) (X86Program info (for/list ([func body]) (cons (car func) (match (cdr func) [(Block info bbody) (Block (append info (cons 'conflicts (build-graph (dict-ref info 'live-after) bbody (undirected-graph '())))) bbody)]))))]
  )    
)

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
     ("pe lint", pe-Lint, interp-Lvar, type-check-Lvar)
     ("uniquify", uniquify, interp-Lvar, type-check-Lvar)
     ("remove complex opera*", remove-complex-opera*, interp-Lvar, type-check-Lvar)
     ("explicate control", explicate_control, interp-Cvar, type-check-Cvar)
     ("instruction selection", select-instructions, interp-x86-0)
     ("uncover live", uncover-live, interp-x86-0)
     ("interference graph", build-interference, interp-x86-0)
     ("assign homes", assign-homes, interp-x86-0)
     ("patch instructions", patch-instructions, interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))