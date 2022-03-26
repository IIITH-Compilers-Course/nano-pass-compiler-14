#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "interp.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lif.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "graph-printing.rkt")
(require "./priority_queue.rkt")
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

(define (shrink-helper e)
    (match e
        [(Prim 'and (list e1 e2)) (If (shrink-helper e1) (shrink-helper e2) (Bool #f))]
        [(Prim 'or (list e1 e2)) (If (shrink-helper e1) (Bool #t) (shrink-helper e2) )]
        [(Let x e body) (Let (shrink-helper x) (shrink-helper e) (shrink-helper body))]
        [(If cond e1 e2) (If (shrink-helper cond) (shrink-helper e1) (shrink-helper e2))]
        [(Prim '- (list e1 e2)) ((Prim '+ (list (shrink-helper e1) (Prim '- (list (shrink-helper e2))))))] 
        [(Prim op es) (Prim op (for/list ([e es]) (shrink-helper e)))]
        [_ e]
    )
)

(define (shrink p)
    (match p
        [(Program info e) (Program info (shrink-helper e))]
    )
)

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x e body)
        (define var1 (gensym x))
        (define env^ (dict-set env x var1))
        (Let var1 ((uniquify-exp env) e) ((uniquify-exp env^) body))
      ]
      [(If cond exp1 exp2)
        (If ((uniquify-exp env) cond) ((uniquify-exp env) exp1) ((uniquify-exp env) exp2))
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
        [(Bool n) #t]
        [_ #f]
    )
)

(define (rco_exp e)
    (match e
        [(Var n) (Var n)]
        [(Int n) (Int n)]
        [(Bool n) (Bool n)]
        [(Prim 'read '()) (Prim 'read '())]
        [(Prim 'not (list e1)) 
            (cond
                [(rco_atm e1) e]
                [else
                    (define var (gensym))
                    (Let var (rco_exp e1) (Prim 'not (list (Var var))))
                ]
            )
        ]
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
                [else
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
        ;;; [(Prim op (e1 e2))]
        [(Let x e body) (Let x (rco_exp e) (rco_exp body))]
        [(If cond exp1 exp2) ((If (rco_exp cond) (rco_exp exp1) (rco_exp exp2)))]
    )
)

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) 
        (Program info (rco_exp e))]))

(define (explicate_pred cnd thn els)
    (match cnd
        ;;; [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t)) (create_block thn)
        ;;; (create_block els)))]
        ;;; [(Let x rhs body) ]
        ;;; [(Prim 'not (list e)) (IfStmt (Prim 'eq? (list (Var x) (Bool #f)) (create_block thn)
        ;;; (create_block els)))]
        ;;; [(Prim op es) #:when (or (eq? op 'eq?) (eq? op '<))
        ;;; (IfStmt (Prim op es) (create_block thn)
        ;;; (create_block els))]
        [(Bool b) (if b thn els)]
        ;;; [(If cnd^ thn^ els^) ___]
        [_ (error "explicate_pred unhandled case" cnd)]))


(define (explicate_tail e)
    (match e
        [(Var x) (Return (Var x))]
        [(Int n) (Return (Int n))]
        [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
        ;;; [(If cond exp1 exp2) (explicate_pred cond (explicate_tail exp1) (explicate_tail exp2))]
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

(define (assign-homes-convert e varmap usedCalleeNum)
    (match e
        [(Var e) 
            (define color (dict-ref varmap (Var e)))
            (cond   
                [(< color 12) (color-to-register color)]
                [else (Deref 'rbp (* 8 (- (- 11 color) usedCalleeNum)))]
            )
        ]
        [_ e]
    )
)

(define (assign-homes-mapvars varmap stm usedCalleeNum)
    (match stm
        [(Instr op args) (Instr op (map (lambda (x) (assign-homes-convert x varmap usedCalleeNum)) args))]
        [_ stm]
    )
)

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes instrs varmap usedCalleeNum)
    (for/list ([stm instrs]) (assign-homes-mapvars varmap stm usedCalleeNum))
)

(define (check-int e)
    (if (not (Imm? e) ) #t #f)
)

(define (list-to-set lst)
    (list->set (for/list ([e lst] #:when (check-int e)) e))  
)

(define caller-saved-registers (set
                                (Reg 'rax)
                                (Reg 'rcx)
                                (Reg 'rdx)
                                (Reg 'rsi)
                                (Reg 'rdi)
                                (Reg 'r8)
                                (Reg 'r9)
                                (Reg 'r10)
                                (Reg 'r11)))

(define callee-saved-registers (list
                                (Reg 'rsp)
                                (Reg 'rbp)
                                (Reg 'rbx)
                                (Reg 'r12)
                                (Reg 'r13)
                                (Reg 'r14)
                                (Reg 'r15)))

(define argument-registers (set
                            (Reg 'rdi)
                            (Reg 'rsi)
                            (Reg 'rdx)
                            (Reg 'rcx)
                            (Reg 'r8)
                            (Reg 'r9)))

(define (extract-reads instr)
    (match instr
        [(Instr 'movq es) (list-to-set (list (car es))) ]
        [(Instr 'addq es) (list-to-set es)]
        [(Instr 'subq es) (list-to-set es)]
        [(Instr 'negq es) (list-to-set es)]
        [(Jmp _) (set (Reg 'rax) (Reg 'rsp))]
        [(Callq _ _) argument-registers]
        [_ (set)]
    )
)

(define (extract-writes instr)
    (match instr
        [(Instr 'movq es) (list->set (cdr es))]
        [(Instr 'addq es) (list->set (cdr es))]
        [(Instr 'subq es) (list->set (cdr es))]
        [(Instr 'negq es) (list->set es)]
        [(Callq _ _) caller-saved-registers]
        [_ (set)]
    )
)

(define (get-live-after listOfInstructions)
    (match listOfInstructions
        [(list a) (list (extract-reads a))] 
        [_ (let ([list-live-after (get-live-after (cdr listOfInstructions))])
            (append (list
                    (set-union (extract-reads (car listOfInstructions))
                        (set-subtract (car list-live-after)  
                            (extract-writes (car listOfInstructions)) 
                        )
                    )
                )
            list-live-after))
        ]
    )
)

(define (uncover-live p)
    (match p
        [(X86Program info body)
            (match body
                [`((start . ,(Block sinfo instrs)))
                    (X86Program info `((start . ,(Block (dict-set sinfo 'live-after (get-live-after instrs)) instrs))))]
            )
        ]
    )
)

(define (set-to-list s) 
    (for/list ([e s]) e)
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

(define (add-edges-helper curWrite curInstr curLive interference-graph)
    (match curWrite
        ['() interference-graph]
        [(cons a c) (add-edges-helper c curInstr curLive (add-edges a curInstr curLive interference-graph)) ]
    )
)

(define (build-graph list-live-after listOfInstructions [interference-graph (undirected-graph '())]) 
    (match listOfInstructions
        ['() interference-graph]
        [_  (define curInstr (car listOfInstructions))
            (define curWrite (set-to-list (extract-writes curInstr)) )
            (define curLive (car list-live-after))
            (build-graph (cdr list-live-after) (cdr listOfInstructions) (add-edges-helper curWrite curInstr curLive interference-graph))
        ]
    )
)

(define (build-interference p)
    (match p
        [(X86Program info body)
            (match body
                [`((start . ,(Block sinfo instrs)))
                (X86Program (dict-set info 'conflicts (build-graph (dict-ref sinfo 'live-after) instrs)) `((start . ,(Block sinfo instrs))))])
        ]
    )
)

(define (color-to-register color)
  (match color
    [0 (Reg 'rcx)]
    [1 (Reg 'rdx)]
    [2 (Reg 'rsi)]
    [3 (Reg 'rdi)]
    [4 (Reg 'r8)]
    [5 (Reg 'r9)]
    [6 (Reg 'r10)]
    [7 (Reg 'r11)]
    [8 (Reg 'rbx)]
    [9 (Reg 'r12)]
    [10 (Reg 'r13)]
    [11 (Reg 'r14)]
  )
)

(define (register-to-color reg)
  (match reg
    [(Reg 'rcx) 1]
    [(Reg 'rdx) 2]
    [(Reg 'rsi) 3]
    [(Reg 'rdi) 4]
    [(Reg 'r8) 5]
    [(Reg 'r9) 6]
    [(Reg 'r10) 7]
    [(Reg 'r11) 8]
    [(Reg 'rbx) 9]
    [(Reg 'r12) 10]
    [(Reg 'r13) 11]
    [(Reg 'r14) 12]
    [(Reg 'rax) -1]
    [(Reg 'rsp) -2]
    [(Reg 'rbp) -3]
    [(Reg 'r15) -4]
  )
)

(struct node (name [blockedColorsSet #:mutable]))

(define cmp-<                 
  (lambda (node1 node2)         
    (< (length (set-to-list (node-blockedColorsSet node1))) (length (set-to-list (node-blockedColorsSet node2)))) )
)

(define (mex s [i 0])
    (match (member i s)
        [#f i]
        [_ (mex s (+ i 1))]
    )
)

(define (update-neighbours q vname-pointer curColor neighbors)
    (match neighbors
        ['() q]
        [_ 
            (define curNeighbour (dict-ref vname-pointer (car neighbors)) )
            (define nk  (node-key curNeighbour) )
            (define st (set-to-list (node-blockedColorsSet nk)))
            (define newSet (list->set (append (list curColor) st)))
            (set-node-blockedColorsSet! nk newSet) 
            (pqueue-decrease-key! q curNeighbour)
            (update-neighbours q vname-pointer curColor (cdr neighbors))                                       
        ]
    )   
)

(define (assign-next q vname-pointer graph [var-colors '()] ) 
    (cond 
        [(eq? (pqueue-count q) 0) var-colors]
        [else 
            (define curNode (pqueue-pop! q))
            (match (node-name curNode)
                [(Reg r) 
                   (define curColor (register-to-color (Reg r)) )
                   (assign-next q vname-pointer graph (dict-set var-colors (node-name curNode) curColor))
                ]
                [_ 
                    (define curColor (mex (set-to-list (node-blockedColorsSet curNode)) ))
                    (define updatedQ (update-neighbours q vname-pointer curColor (sequence->list (in-neighbors graph (node-name curNode))) ))
                    (assign-next updatedQ vname-pointer graph (dict-set var-colors (node-name curNode) curColor))
                ]
            )
        ]
    )
)

(define (allocate-registers-helper variableList graph [vname-pointer '()] [q (make-pqueue cmp-<)] [registerList '()]) 
    (match variableList
        ['()
            (for ([rg registerList]) (update-neighbours q vname-pointer (register-to-color rg) (sequence->list (in-neighbors graph rg)))) 
            (assign-next q vname-pointer graph)]
        [_ 
            (define curVar (car variableList))
            (match curVar
                [(Reg _) (allocate-registers-helper (cdr variableList) graph 
                    (dict-set vname-pointer curVar (pqueue-push! q (node curVar (set)))) q (cons curVar registerList))] 
                [_ (allocate-registers-helper (cdr variableList) graph 
                (dict-set vname-pointer curVar (pqueue-push! q (node curVar (set)))) q registerList)]
            )
        ]
    )
)

(define (num-spilled-var varColors [max 0]) 
    (match varColors
        ['()
            (cond
                [(> max 11) (- max 11)]
                [else 0]
            ) 
        ]
        [_  
            (match (car (car varColors))
                [(Var _) (define color (cdr (car varColors)) )
                    (cond 
                        [(< color max) (num-spilled-var (cdr varColors) max)]
                        [else (num-spilled-var (cdr varColors) color)]
                    )
                ]
                [_ (num-spilled-var (cdr varColors) max)]
            )
        ]
    )
)


(define (used-callee varColors [usedCallee '()]) 
    (match varColors
        ['() (list->set usedCallee)]
        [_  
            (match (car (car varColors))
                [(Var _) 
                    (define color (cdr (car varColors)))
                    (cond 
                        [(< color 12) 
                            (define reg (color-to-register color))
                            (cond 
                                [(eq? #f (member reg callee-saved-registers)) (used-callee (cdr varColors) usedCallee)]
                                [else (used-callee (cdr varColors) (cons reg usedCallee))]
                            )
                        ]
                        [else (used-callee (cdr varColors) usedCallee)]
                    )
                ]
                [_ (used-callee (cdr varColors) usedCallee)]
            )
        ]
    )
)

(define (allocate-registers p)
    (match p
        [(X86Program info body)
            (match body
                [`((start . ,(Block sinfo instrs)))
                (print-dot  (dict-ref info 'conflicts) "testGraph.txt")
                (define graph (dict-ref info 'conflicts))
                (define varColors (allocate-registers-helper (sequence->list (in-vertices graph)) graph))
                (define numSpilledVariables (num-spilled-var varColors))
                (define usedCallee (used-callee varColors) )
                (X86Program (dict-set (dict-set info 'stack-space numSpilledVariables) 'used_callee usedCallee) `((start . ,(Block sinfo (assign-homes instrs varColors (length (set-to-list usedCallee)))))))])
        ]
    )
)

(define (patch-instructions-convert stm)
    (match stm
        [(Instr op (list (Deref 'rbp offset_1) (Deref 'rbp offset_2))) 
            (cond
                [(eq? offset_1 offset_2) '()]
                [else 
                    (list
                        (Instr 'movq (list (Deref 'rbp offset_1) (Reg 'rax)))
                        (Instr op (list (Reg 'rax) (Deref 'rbp offset_2)))
                    )
                ]
            )
        ]
        [(Instr op (list (Reg reg1) (Reg reg2)))
            (cond
                [(eq? reg1 reg2) '()]
                [else 
                    (list (Instr op (list (Reg reg1) (Reg reg2))))
                ]
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

(define (push-calle-saved registers)
    (for/list ([rg (set-to-list registers)]) (Instr 'pushq (list rg)))
)

(define (pop-calle-saved registers)
    (for/list ([rg (reverse (set-to-list registers))]) (Instr 'popq (list rg)))
)


;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
    (match p
        [(X86Program info es) 
            (define S (dict-ref info 'stack-space))
            (define C (length (set-to-list (dict-ref info 'used_callee))))
            (define A (- (align (+ (* 8 S) (* 8 C)) 16) (* 8 C)))
            (X86Program info `( 
            (start . ,(dict-ref es 'start))
            (main . ,(Block info (append (list (Instr 'pushq (list (Reg 'rbp)))) 
                                         (list (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))) 
                                         (push-calle-saved (dict-ref info 'used_callee)) 
                                         (list (Instr 'subq (list (Imm A) (Reg 'rsp))))
                                         (list (Jmp 'start))
                                  )
                        )
            )
            (conclusion . ,(Block info (append  (list (Instr 'addq (list (Imm A) (Reg 'rsp)))) 
                                                (pop-calle-saved (dict-ref info 'used_callee))
                                                (list (Instr 'popq (list (Reg 'rbp))))
                                                (list (Retq))
                                        )
                            )
            )
        ))
]))




;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
    ;;;  ("pe lint", pe-Lint, interp-Lvar, type-check-Lvar)
     ("shrink", shrink, interp-Lif, type-check-Lif)
     ("uniquify", uniquify, interp-Lif, type-check-Lif)
    ;;;  ("remove complex opera*", remove-complex-opera*, interp-Lvar, type-check-Lvar)
    ;;;  ("explicate control", explicate_control, interp-Cvar, type-check-Cvar)
    ;;;  ("instruction selection", select-instructions, interp-x86-0)
    ;;;  ("uncover live", uncover-live, interp-x86-0)
    ;;;  ("interference graph", build-interference, interp-x86-0)
    ;;;  ("allocate registers", allocate-registers, interp-x86-0)
    ;;;  ("patch instructions", patch-instructions, interp-x86-0)
    ;;;  ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))