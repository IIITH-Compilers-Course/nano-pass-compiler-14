#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "interp.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Cif.rkt")
(require "interp-Cwhile.rkt")
(require "interp-Lif.rkt")
(require "interp-Lwhile.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Cwhile.rkt")
(require "utilities.rkt")
(require "multigraph.rkt")
(require "graph-printing.rkt")
(require "./priority_queue.rkt")
(require data/queue)	
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
        [(Let x e1 body) (Let (shrink-helper x) (shrink-helper e1) (shrink-helper body))]
        [(If cond e1 e2) (If (shrink-helper cond) (shrink-helper e1) (shrink-helper e2))]
        [(Prim '- (list e1 e2)) (Prim '+ (list (shrink-helper e1) (Prim '- (list (shrink-helper e2)))))] 
        [(Prim op es) (Prim op (for/list ([e1 es]) (shrink-helper e1)))]
        [(SetBang v exp) (SetBang v (shrink-helper exp))]
        [(Begin es exp) (Begin (for/list ([e es]) (shrink-helper e)) (shrink-helper exp))]
        [(WhileLoop exp1 exp2) (WhileLoop (shrink-helper exp1) (shrink-helper exp2))]
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
      [(Void) (Void)]
      [(Let x e body)
        (define var1 (gensym x))
        (define env^ (dict-set env x var1))
        (Let var1 ((uniquify-exp env) e) ((uniquify-exp env^) body))
      ]
      [(If cond exp1 exp2)
        (If ((uniquify-exp env) cond) ((uniquify-exp env) exp1) ((uniquify-exp env) exp2))
      ]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(SetBang v exp) (SetBang (dict-ref env v) ((uniquify-exp env) exp))]
      [(Begin es exp) (Begin (for/list ([e es]) ((uniquify-exp env) e)) ((uniquify-exp env) exp))]
      [(WhileLoop exp1 exp2) (WhileLoop ((uniquify-exp env) exp1) ((uniquify-exp env) exp2))]
)))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (collect-set! e) 
    (match e
        [(Var x) (set)]
        [(Int n) (set)]
        [(Bool b) (set)]
        [(Void) (set)]
        [(Let x rhs body) (set-union (collect-set! rhs) (collect-set! body))]
        [(SetBang var rhs) (set-union (set var) (collect-set! rhs))]
        [(Prim op es) (set-union* (for/list ([e es]) (collect-set! e)))]
        [(If cond exp1 exp2) (set-union (collect-set! cond) (collect-set! exp1) (collect-set! exp2))]
        [(Begin es exp) (set-union (set-union* (for/list ([e es]) (collect-set! e))) 
                                   (collect-set! exp))
        ]
        [(WhileLoop exp1 exp2) (set-union (collect-set! exp1) (collect-set! exp2))]
))

(define ((uncover-get!-exp set!-vars) e)
    (match e
        [(Var x) (Var x)
            (if (set-member? set!-vars x) (GetBang x) (Var x))
        ]
        [(Int n) (Int n)]
        [(Bool b) (Bool b)]
        [(Void) (Void)]
        [(Let x e body) (Let x ((uncover-get!-exp set!-vars) e) ((uncover-get!-exp set!-vars) body))]
        [(If cond exp1 exp2) (If ((uncover-get!-exp set!-vars) cond) ((uncover-get!-exp set!-vars) exp1) ((uncover-get!-exp set!-vars) exp2))]
        [(Prim op es) (Prim op (for/list ([e es]) ((uncover-get!-exp set!-vars) e)))]
        [(SetBang v exp) (SetBang v ((uncover-get!-exp set!-vars) exp))]
        [(Begin es exp) (Begin (for/list ([e es]) ((uncover-get!-exp set!-vars) e)) ((uncover-get!-exp set!-vars) exp))]
        [(WhileLoop exp1 exp2) (WhileLoop ((uncover-get!-exp set!-vars) exp1) ((uncover-get!-exp set!-vars) exp2))]
    )
)

(define (uncover-get! p) 
    (match p 
        [(Program info body) 
            (define setVars (collect-set! body))
            (Program info ((uncover-get!-exp setVars) body))]
    )
)

(define (rco_atm e)
    (match e
        [(Var n) #t]
        [(Int n) #t]
        [(Bool n) #t]
        [(Void) #t]
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
                    (Let var1 (rco_exp e1) (Prim op (list (Var var1) e2)))
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
        [(Let x e body) (Let x (rco_exp e) (rco_exp body))]
        [(If cond exp1 exp2) (If (rco_exp cond) (rco_exp exp1) (rco_exp exp2))]
        [(GetBang v) (GetBang v)]
        [(SetBang v exp) (SetBang v (rco_exp exp))]
        [(Begin es exp) (Begin (for/list ([e es]) (rco_exp e)) (rco_exp exp))]
        [(WhileLoop exp1 exp2) (WhileLoop (rco_exp exp1) (rco_exp exp2))]
    )
)

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) 
        (Program info (rco_exp e))]))

(define basic-blocks '())

(define (create_block tail)
    (match tail
        [(Goto label) (Goto label)]
        [else (let ([label (gensym 'block)])
            (set! basic-blocks (cons (cons label tail) basic-blocks))
            (Goto label))
        ]
    )
)

(define (check-cmp cmp)
    (match cmp
        ['< #t]
        ['<= #t]
        ['> #t]
        ['>= #t]
        ['eq? #t]
        [_ #f]
    )
)

(define (explicate_pred cnd thn els)
    (match cnd
        [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (create_block thn)
                    (create_block els))]
        [(Let x rhs body) 
            (explicate_assign rhs x (explicate_pred body thn els))    
        ]
        [(Prim 'not (list e)) (IfStmt (Prim 'eq? (list e (Bool #f))) (create_block thn)
                    (create_block els))]
        [(Prim op es) #:when (check-cmp op)
                    (IfStmt (Prim op es) (create_block thn) (create_block els))]
        [(Bool b) (if b thn els)]
        [(If cnd^ thn^ els^)
            (define thnBlock (create_block thn))
            (define elsBlock (create_block els)) 
            (explicate_pred cnd^ (explicate_pred thn^ thnBlock elsBlock)
                                 (explicate_pred els^ thnBlock elsBlock)
            )
        ]
        [(Begin es exp)
            (define thnBlock (create_block thn))
            (define elsBlock (create_block els)) 
            (foldr explicate_effect (explicate_pred exp thnBlock elsBlock) es)]
        [_ (error "explicate_pred unhandled case" cnd)]
    )
)

(define (explicate_effect e cont) 
    (match e
        [(Prim 'read '()) (Seq e cont)]
        [(WhileLoop cnd bdy) 
            (let ([loop (gensym 'loop)])
            (define body (explicate_pred cnd (explicate_effect bdy (Goto loop)) cont)) 
            (set! basic-blocks (cons (cons loop body) basic-blocks))
            (Goto loop))
        ]
        [(SetBang v exp) (explicate_assign exp v cont)]
        [(Begin es exp) (explicate_effect exp (foldr explicate_effect cont es))]
        [(If cond exp1 exp2) (explicate_pred cond (explicate_effect exp1 cont) (explicate_effect exp2 cont))]
        [(Let x rhs body) (explicate_assign rhs x (explicate_effect body cont))]
        [_ cont]


    ) 
)

(define (explicate_tail e)
    (match e
        [(Var x) (Return (Var x))]
        [(Int n) (Return (Int n))]
        [(Bool b) (Return (Bool b))]
        [(GetBang var) (Return (Var var))]
        [(Let x rhs bdy) (explicate_assign rhs x (explicate_tail bdy))]
        [(If cond exp1 exp2) (explicate_pred cond (explicate_tail exp1) (explicate_tail exp2))]
        [(Prim op es) (Return (Prim op es))]
        [(SetBang v exp) (explicate_effect e (Return (Void)))]
        [(WhileLoop cnd bdy) (explicate_effect e (Return (Void)))]
        [(Begin es exp) (foldr explicate_effect (explicate_tail exp) es)]
        [else (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e x cont)
    (match e
        [(Var xvar) (Seq (Assign (Var x) (Var xvar)) cont)]
        [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
        [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
        [(GetBang var) (Seq (Assign (Var x) (Var var)) cont)]
        [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
        [(If cond exp1 exp2) (explicate_pred cond (explicate_assign exp1 x cont) (explicate_assign exp2 x cont))]
        [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
        [(SetBang v exp) (explicate_effect e (Seq (Assign (Var x) (Void)) cont))]
        [(WhileLoop cnd body) (explicate_effect e (Seq (Assign (Var x) (Void)) cont))]
        [(Begin es exp) (foldr explicate_effect (explicate_assign exp x cont) es)]
        [else (error "explicate_assign unhandled case" e)]))

;; explicate-control : R1 -> C0
(define (explicate_control p)
    (match p
        [(Program info body) 
            (set! basic-blocks '())
            (define instrBlocks (make-hash))
            (dict-set! instrBlocks 'start (explicate_tail body))
            (for ([e basic-blocks]) (dict-set! instrBlocks (car e) (cdr e)))
            (CProgram info instrBlocks)
        ]    
    )
)

(define (select-instructions-atomic e)
    (match e
        [(Int n) (Imm n)]
        [(Var n) (Var n)]
        [(Bool #t) (Imm 1)]
        [(Bool #f) (Imm 0)]
        [(Void) (Imm 0)]
    )
)

(define (cmp-jcc cmprtr)
  (match cmprtr
    ['eq? 'e]
    ['< 'l]
    ['<= 'le]
    ['>= 'ge]
    ['> 'g]
  )
)

(define (select-instructions-statement stm)
    (match stm
        ['() '()]
        [(Seq (Prim 'read '()) t*) (append (list (Callq 'read_int 0)) (select-instructions-statement t*))]
        [(Seq (Assign var exp) t*) (append (select-instructions-assignment exp var) (select-instructions-statement t*))]
        [(Return exp) (append (select-instructions-assignment exp (Reg 'rax)) (list (Jmp 'conclusion)))]
        [(Goto lbl) (list (Jmp lbl))]
        [(IfStmt (Prim cmp (list e1 e2)) (Goto l1) (Goto l2)) 
                 (list (Instr 'cmpq (list (select-instructions-atomic e2) (select-instructions-atomic e1)))
                       (JmpIf (cmp-jcc cmp) l1)
                       (Jmp l2)
                 )
        ]
    )
)

(define (cmp-setcc cmprtr)
  (match cmprtr
    ['eq? 'sete]
    ['< 'setl]
    ['<= 'setle]
    ['>= 'setge]
    ['> 'setg]
  )
)

(define (select-instructions-assignment e x)
    (match e
        [(Int i) (list (Instr 'movq (list (select-instructions-atomic e) x)))]
        [(Var v) (list (Instr 'movq (list e x)))]
        [(Bool b) (list (Instr 'movq (list (select-instructions-atomic e) x)))]
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
                ;;; [(equal? x e2) (list (Instr 'subq (list (select-instructions-atomic e1) x)))]
                [else (list (Instr 'movq (list (select-instructions-atomic e1) x))
                      (Instr 'subq (list (select-instructions-atomic e2) x)))]
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
        [(Prim 'not (list e1)) 
            (cond 
                [(eq? e1 x) (list (Instr 'xorq (list (select-instructions-atomic (Bool #t)) 
                                                     (select-instructions-atomic x))))
                ]
                [else 
                     (list (Instr 'movq (list (select-instructions-atomic e1) x))
                           (Instr 'xorq (list (select-instructions-atomic (Bool #t)) 
                                              (select-instructions-atomic x))))
                ]
            )
        ]
        [(Prim cmp (list e1 e2))
            (list (Instr 'cmpq (list (select-instructions-atomic e2) (select-instructions-atomic e1)))
                  (Instr (cmp-setcc cmp) (list (ByteReg 'al)))
                  (Instr 'movzbq (list (ByteReg 'al) x))
            )
        ]
    )
)

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info e) 
        (define instrBlocks (make-hash))
        (dict-for-each e (lambda (lbl instrs) (dict-set! instrBlocks lbl (Block '() (select-instructions-statement instrs)))))
        (X86Program info instrBlocks)
    ]
  )
)
        
(define (assign-homes-convert e varmap usedCalleeNum)
    (match e
        [(Var e) 
            (define color (dict-ref varmap (Var e)))
            (cond   
                [(< color 13) (color-to-register color)]
                [else (Deref 'rbp (* 8 (- (- 12 color) usedCalleeNum)))]
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
        [(Instr 'movq es) (list-to-set (list (car es)))]
        [(Instr 'cmpq es) (list-to-set es)]
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
        [(Instr 'movzbq es) (list->set (cdr es))]
        [(Instr 'addq es) (list->set (cdr es))]
        [(Instr 'subq es) (list->set (cdr es))]
        [(Instr 'negq es) (list->set es)]
        [(Callq _ _) caller-saved-registers]
        [_ (set)]
    )
)

(define (get-live-after listOfInstructions initialSet)
    (match listOfInstructions
        [(list a) (list 
                    (set-union (extract-reads a)
                        (set-subtract initialSet (extract-writes a)))
                  )
        ] 
        [_ (let ([list-live-after (get-live-after (cdr listOfInstructions) initialSet)])
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

(define (makeCFG lbl instrs [cfgEdge '()])
    (match instrs
        ['() cfgEdge]
        [(cons a c) 
            (match a
               [(Jmp dest) (makeCFG lbl c (append cfgEdge (list (list lbl dest))))] 
               [(JmpIf cmp dest) (makeCFG lbl c (append cfgEdge (list (list lbl dest))))] 
               [_ (makeCFG lbl c cfgEdge)]
        )]
    )
)

(define label-live (make-hash))
(define live-after-sets (make-hash))

(define (uncover-live-block label instrs initialSet)
    (define live-after-list (get-live-after instrs initialSet))
    (dict-set! live-after-sets label live-after-list)
    (car live-after-list)
)
;;; (define (uncover-live-block lbl block graph)
;;;     (match block
;;;         [(Block info instrs)
;;;             (define children (sequence->list (in-neighbors graph lbl)))
;;;             (define initialSet (set))
;;;             (for ([child children]) (set! initialSet (set-union initialSet (dict-ref label-live child))))
;;;             (define live-after-list (get-live-after instrs initialSet))
;;;             (dict-set! label-live lbl (car live-after-list))
;;;             (Block (dict-set info 'live-after live-after-list) instrs)
;;;         ]        
;;;     )
;;; )

(define (analyze_dataflow G transfer bottom join e)
    (define mapping (make-hash))
    (for ([v (in-vertices G)])
        (dict-set! mapping v bottom))
    (define worklist (make-queue))
    (for ([v (in-vertices G)]  #:when (not (eq? v 'conclusion))) 
        (enqueue! worklist v))
    (define trans-G (transpose G))
    (while (not (queue-empty? worklist))
        (define node (dequeue! worklist))
        (define input (for/fold ([state bottom])
                        ([pred (in-neighbors trans-G node)])
                      (join state (dict-ref mapping pred))))
        (define block (dict-ref e node))
        (define instrs '())
        (match block
            [(Block info instr) (set! instrs instr) instr]
        )
        (displayln instrs)
        (define output (transfer node instrs input))
        (cond [(not (equal? output (dict-ref mapping node)))
            (dict-set! mapping node output)
            (for ([v (in-neighbors G node)])
                (enqueue! worklist v))]))
    (displayln "Manish")
    (displayln mapping)
    mapping
)

(define (uncover-live p)
    (match p
        [(X86Program info e) 
            (set! label-live (make-hash))
            (define cfgEdges '())
            (dict-for-each e 
                (lambda (lbl instrs) (set! cfgEdges (append cfgEdges (makeCFG lbl (Block-instr* instrs)))))
            )

            (define graph (make-multigraph cfgEdges))
            (define graphTransp (transpose graph))
            (define topoOrder (tsort graphTransp))
            (dict-set! label-live 'conclusion (set (Reg 'rax) (Reg 'rsp)))
            (analyze_dataflow graphTransp uncover-live-block (set) set-union e)
            (displayln "manish")
            (displayln live-after-sets)
            (displayln e)
            (dict-for-each e 
                (lambda (lbl block) 
                    (dict-set! e lbl (Block (dict-set (Block-info block) 'live-after (dict-ref live-after-sets lbl)) (Block-instr* block)))
                )
            )
            (displayln e)
            (X86Program info e)
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
                [(Instr 'movzbq (list src dest)) (when (not (eq? src v)) (add-edge! interference-graph v d))]
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

(define (build-graph list-live-after listOfInstructions interference-graph) 
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
            (define graph (undirected-graph '()))
            (dict-for-each body
                (lambda (lbl instrs)
                    (match (dict-ref body lbl)
                        [(Block sinfo bbody) (set! graph (build-graph (dict-ref sinfo 'live-after) bbody graph))] 
                    )
                )
            )
        (X86Program (dict-set info 'conflicts graph) body)]
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
    [12 (Reg 'r15)]
  )
)

(define (register-to-color reg)
  (match reg
    [(Reg 'rcx) 0]
    [(Reg 'rdx) 1]
    [(Reg 'rsi) 2]
    [(Reg 'rdi) 3]
    [(Reg 'r8) 4]
    [(Reg 'r9) 5]
    [(Reg 'r10) 6]
    [(Reg 'r11) 7]
    [(Reg 'rbx) 8]
    [(Reg 'r12) 9]
    [(Reg 'r13) 10]
    [(Reg 'r14) 11]
    [(Reg 'r15) 12]
    [(Reg 'rax) -1]
    [(Reg 'rsp) -2]
    [(Reg 'rbp) -3]
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
                        [(< color 13) 
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
            (define graph (dict-ref info 'conflicts))
            (define varColors (allocate-registers-helper (sequence->list (in-vertices graph)) graph))
            (define numSpilledVariables (num-spilled-var varColors))
            (define usedCallee (used-callee varColors))

            (dict-for-each body
                (lambda (lbl instrs)
                    (match (dict-ref body lbl)
                        [(Block sinfo instrs) (dict-set! body lbl (Block sinfo (assign-homes instrs varColors (length (set-to-list usedCallee)))))] 
                    )
                )
            )

            (X86Program (dict-set (dict-set info 'stack-space numSpilledVariables) 'used_callee usedCallee) body)
        ]
    )
)

(define (patch-instructions-convert stm)
    (match stm
        [(Instr 'movzbq (list (ByteReg 'al) (Deref 'rbp offset))) 
                (list
                    (Instr 'movzbq (list (ByteReg 'al) (Reg 'rax)))
                    (Instr 'movq (list (Reg 'rax) (Deref 'rbp offset)))
                )
        ]
        [(Instr 'cmpq (list src (Imm n))) 
                (list
                    (Instr 'movq (list (Imm n) (Reg 'rax)))
                    (Instr 'cmpq (list src (Reg 'rax)))
                )
        ]
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
        [_ (list stm)]
    )
)

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
    (match p
        [(X86Program info body)
            (dict-for-each body
                (lambda (lbl instrs)
                    (match (dict-ref body lbl)
                        [(Block sinfo instrs) (dict-set! body lbl (Block sinfo (append-map patch-instructions-convert instrs)))] 
                    )
                )
            )
        (X86Program info body)]
    )
)

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
            (dict-set! es 'main 
                (Block info (append (list (Instr 'pushq (list (Reg 'rbp)))) 
                                                    (list (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))) 
                                                    (push-calle-saved (dict-ref info 'used_callee)) 
                                                    (list (Instr 'subq (list (Imm A) (Reg 'rsp))))
                                                    (list (Jmp 'start))
                            )
                )
            )
            (dict-set! es 'conclusion 
                            (Block info (append  (list (Instr 'addq (list (Imm A) (Reg 'rsp)))) 
                                                        (pop-calle-saved (dict-ref info 'used_callee))
                                                        (list (Instr 'popq (list (Reg 'rbp))))
                                                        (list (Retq))
                                                )
                                    )
            )

        (X86Program info es)]
    )  
)

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
    ;;;  ("pe lint", pe-Lint, interp-Lvar, type-check-Lvar)
     ("shrink", shrink, interp-Lwhile, type-check-Lwhile)
     ("uniquify", uniquify, interp-Lwhile, type-check-Lwhile)
     ("uncover get!", uncover-get!, interp-Lwhile)
     ("remove complex opera*", remove-complex-opera*, interp-Lwhile, type-check-Lwhile)
     ("explicate control", explicate_control, interp-Cwhile, type-check-Cwhile)
     ("instruction selection", select-instructions, interp-x86-0)
     ("uncover live", uncover-live, interp-x86-0)
     ("interference graph", build-interference, interp-x86-0)
     ("allocate registers", allocate-registers, interp-x86-0)
     ("patch instructions", patch-instructions, interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))