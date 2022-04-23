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
(require "interp-Cvec.rkt")
(require "interp-Lif.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Lvec.rkt")
(require "interp-Lfun.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Lvec.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Cwhile.rkt")
(require "type-check-Cvec.rkt")
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
        [(HasType exp type) (HasType (shrink-helper exp) type)]
        [(Apply fn es) (Apply (shrink-helper fn) (for/list ([exp es]) (shrink-helper exp)))]
        [_ e]
    )
)

(define (shrink p)
    (match p
        [(ProgramDefsExp info dfList e) 
            (set! dfList (append dfList (list (Def 'main '() 'Integer '() e))))
            (ProgramDefs info (for/list ([df dfList]) (Def (Def-name df) (Def-param* df) (Def-rty df) (Def-info df) (shrink-helper (Def-body df)))))
        ]
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
      [(HasType exp type) (HasType ((uniquify-exp env) exp) type)]
      [(Apply fn es) (Apply ((uniquify-exp env) fn) (for/list ([exp es]) ((uniquify-exp env) exp)))]
      [(Def name params rty info body) 
        (define new_params
            (for/list ([prm params]) 
                (match prm
                    [(cons var type) 
                        (define newVar (gensym var))
                        (dict-set! env var newVar)
                        (cons newVar type)
                    ]
                )
            )
        )
        (Def (dict-ref env name) new_params rty info ((uniquify-exp env) body))
      ]
)))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(ProgramDefs info dfList) 
        (define fnNameEnv (make-hash))
        (for/list ([df dfList])
            (define newFnName (gensym (Def-name df)))
            (if (eq? (Def-name df) 'main) (set! newFnName 'main) (set! newFnName newFnName))
            (dict-set! fnNameEnv (Def-name df) newFnName)
        )

        (ProgramDefs info
            (for/list ([df dfList]) 
                ((uniquify-exp fnNameEnv) df)
            )
        )
    ]
  )
)

(define (reveal-functions-helper e)
    (match e
        [(Let x e1 body) (Let (reveal-functions-helper x) (reveal-functions-helper e1) (reveal-functions-helper body))]
        [(If cond e1 e2) (If (reveal-functions-helper cond) (reveal-functions-helper e1) (reveal-functions-helper e2))]
        [(Prim op es) (Prim op (for/list ([e1 es]) (reveal-functions-helper e1)))]
        [(SetBang v exp) (SetBang v (reveal-functions-helper exp))]
        [(Begin es exp) (Begin (for/list ([e es]) (reveal-functions-helper e)) (reveal-functions-helper exp))]
        [(WhileLoop exp1 exp2) (WhileLoop (reveal-functions-helper exp1) (reveal-functions-helper exp2))]
        [(HasType exp type) (HasType (reveal-functions-helper exp) type)]
        [(Apply fn es) (Apply 
            (if (Var? fn) (FunRef (Var-name fn) (length es)) (reveal-functions-helper fn)) 
            (for/list ([exp es]) (reveal-functions-helper exp)))
        ]
        [_ e]
    )
)

(define (reveal-functions p)
    (match p
        [(ProgramDefs info dfList) 
            (ProgramDefs info
                (for/list ([df dfList])
                    (Def (Def-name df) (Def-param* df) (Def-rty df) (Def-info df) (reveal-functions-helper (Def-body df)))
                )
            )
        ]
    )
)

(define (limit-functions-map params vecName [paramMap '()] [ind 0])
    (match params
        ['() paramMap]
        [(cons a c) (match a
                [(cons var type)
                    (if (< ind 5) 
                        (limit-functions-map c vecName (dict-set paramMap var (Var var)) (+ ind 1)) 
                        (limit-functions-map c vecName (dict-set paramMap var `(Prim 'vector-ref (list ,vecName ,(- ind 5)))) (+ ind 1))
                    )
                ]
        )]
    )
)

(define (limit-functions-params params vecName [ind 0])
    (match params
        ['() '()]
        [(cons a c) 
            (cond
                [(< ind 5) (cons a (limit-functions-params c vecName (+ ind 1)))]
                [else
                    (define vc '(Vector))
                    (for/list ([prm params])
                        (match prm
                            [`(,x : ,t) (set! vc (append vc (list t)))]
                        )
                    )
                    (list `(,vecName : ,vc))
                ]
            )
        ]
    )
)

(define (limit-functions-fnCall params paramMap [ind 0])
    (match params
        ['() '()]
        [(cons a c) 
            (cond
                [(< ind 5) (cons a (limit-functions-fnCall c paramMap (+ ind 1)))]
                [else (list (Prim 'vector params))]
            )
        ]
    )
)

(define (limit-functions-body body paramMap)
    (match body
        [(Var x) (dict-ref paramMap x)]
        [(Let x e1 body) (Let (limit-functions-body x) (limit-functions-body e1) (limit-functions-body body))]
        [(If cond e1 e2) (If (limit-functions-body cond) (limit-functions-body e1) (limit-functions-body e2))]
        [(Prim op es) (Prim op (for/list ([e1 es]) (limit-functions-body e1)))]
        [(SetBang v exp) (SetBang v (limit-functions-body exp))]
        [(Begin es exp) (Begin (for/list ([body es]) (limit-functions-body body)) (limit-functions-body exp))]
        [(WhileLoop exp1 exp2) (WhileLoop (limit-functions-body exp1) (limit-functions-body exp2))]
        [(HasType exp type) (HasType (limit-functions-body exp) type)]
        [(Apply fn es) (Apply (limit-functions-body fn paramMap) 
                              (limit-functions-fnCall es paramMap)
                        )
        ]
        [(FunRef id n) (FunRef id n)]
        ;;; [_ body]
    )
)

(define (limit-functions-helper df)
    (define params (Def-param* df))
    (define vecName (gensym 'tup))
    (define paramMap (limit-functions-map params vecName))
    (define newParams (limit-functions-params params vecName))
    (define newBody (limit-functions-body (Def-body df) paramMap))
    (Def (Def-name df) newParams (Def-rty df) (Def-info df) newBody)
)

(define (limit-functions p)
    (match p 
        [(ProgramDefs info dfList) 
            (ProgramDefs info 
                (for/list ([df dfList]) (limit-functions-helper df))
            )
        ]
    )
)

(define (has-type-vectorSet-helper varList vectorName [ind 0])
    (match varList
        ['() (Var vectorName)]
        [(cons a c) (Let (gensym '_) (Prim 'vector-set! (list (Var vectorName) (Int ind) (Var a))) (has-type-vectorSet-helper c vectorName (+ ind 1)))]
    )
)

(define (has-type-helper es type [varList '()])
    (match es
        ['() 
            (define vectorName (gensym))
            (define len (length varList))
            (define bytes (* 8 (+ len 1)))
            (Let (gensym '_) (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int bytes))) (GlobalValue 'fromspace_end))) (Void) (Collect bytes)) 
                (Let vectorName (Allocate len type) (has-type-vectorSet-helper varList  vectorName))
            )
        ]
        [_ 
            (define curVarName (gensym))
            (define curValue (car es))
            (Let curVarName (expose_allocation_helper curValue) (has-type-helper (cdr es) type (append varList (list curVarName))))
        ]
    )
)

(define (expose_allocation_helper e)
    (match e
        [(Let x e body) (Let x (expose_allocation_helper e) (expose_allocation_helper body))]
        [(If cond exp1 exp2) (If (expose_allocation_helper cond) (expose_allocation_helper exp1) (expose_allocation_helper exp2))]
        [(Prim op es) (Prim op (for/list ([e es]) (expose_allocation_helper e)))]
        [(SetBang v exp) (SetBang v (expose_allocation_helper exp))]
        [(Begin es exp) (Begin (for/list ([e es]) (expose_allocation_helper e)) (expose_allocation_helper exp))]
        [(WhileLoop exp1 exp2) (WhileLoop (expose_allocation_helper exp1) (expose_allocation_helper exp2))]
        [(HasType exp type)
            (match exp
                [(Prim 'vector es) (has-type-helper es type)]
            )
        ]
        [(Def name params rty info body) (Def name params rty info (expose_allocation_helper body))]
        [(Apply fn es) (Apply (expose_allocation_helper fn) (for/list ([exp es]) (expose_allocation_helper exp)))]
        [_ e]
    )
)

(define (expose_allocation p) 
    (match p 
        [(ProgramDefs info dfList) 
            (ProgramDefs info 
                (for/list ([df dfList]) (expose_allocation_helper df))
            )
        ]
    )
)

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
        [_ (set)]
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
        [(Def name params rty info body) (Def name params rty info (uncover-get!-exp body))]
        [_ e]
    )
)

(define (uncover-get! p) 
    (match p 
        [(ProgramDefs info dfList) 
            (ProgramDefs info 
                (for/list ([df dfList]) (expose_allocation_helper df))
            )
        ]
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
        [(Prim op (list e1))
            (cond
                [(rco_atm e1) (Prim op (list e1))]
                [else
                    (define tmp-var (gensym))
                    (Let tmp-var (rco_exp e1) (Prim op (list (Var tmp-var))))
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
        [(Prim op (list e1 e2 e3))
            (cond
                [(not (rco_atm e1))
                    (define tmp-var (gensym))
                    (Let tmp-var (rco_exp e1) (rco_exp (Prim op (list (Var tmp-var) e2 e3))))
                ]
                [(not (rco_atm e2))
                    (define tmp-var (gensym))
                    (Let tmp-var (rco_exp e2) (rco_exp (Prim op (list e1 (Var tmp-var) e3))))
                ]
                [(not (rco_atm e3))
                    (define tmp-var (gensym))
                    (Let tmp-var (rco_exp e3) (rco_exp (Prim op (list e1 e2 (Var tmp-var)))))
                ]
                [else (Prim op (list e1 e2 e3))]
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
        [_ e]
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
        [(Prim 'vector-ref es) 
                  (define tmp (gensym 'tmp))
                  (Seq (Assign (Var tmp) cnd) 
                        (IfStmt (Prim 'eq? (list (Var tmp) (Bool #t))) (create_block thn)
                                           (create_block els)))]
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
        ;;; [(Begin es exp)
        ;;;     (define thnBlock (create_block thn))
        ;;;     (define elsBlock (create_block els)) 
        ;;;     (foldr explicate_effect (explicate_pred exp thnBlock elsBlock) es)]
        [(Begin es exp)
            (define thnBlock (create_block thn))
            (define elsBlock (create_block els)) 
            (explicate_effect (Begin es (Void)) (explicate_pred exp thnBlock elsBlock))]
        [_ (error "explicate_pred unhandled case" cnd)]
    )
)

(define (explicate_effect e cont) 
    (match e
        [(Prim 'read '()) (Seq e cont)]
        [(Prim 'vector-set! es) (Seq (Prim 'vector-set! es) cont)]
        [(WhileLoop cnd bdy) 
            (let ([loop (gensym 'loop)])
            (define body (explicate_pred cnd (explicate_effect bdy (Goto loop)) cont)) 
            (set! basic-blocks (cons (cons loop body) basic-blocks))
            (Goto loop))
        ]
        [(SetBang v exp) (explicate_assign exp v cont)]
        [(Begin es body)
            (match es
            [(list) (explicate_effect body cont)]
            [(cons e rest) (explicate_effect e (explicate_effect (Begin rest body) cont))])]
        ;;; [(Begin es exp) (explicate_effect exp (explicate_effect es cont))]
        [(If cond exp1 exp2) (explicate_pred cond (explicate_effect exp1 cont) (explicate_effect exp2 cont))]
        [(Let x rhs body) (explicate_assign rhs x (explicate_effect body cont))]
        [(Allocate len T) cont]
        [(GlobalValue var) cont]
        [(Collect bytes) (Seq (Collect bytes) cont)]
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
        [(WhileLoop cnd bdy) (explicate_effect e '())]
        [(Begin es exp) (foldr explicate_effect (explicate_tail exp) es)]
        [(Allocate len type) (Return (Allocate len type))]
        [(GlobalValue var) (Return (GlobalValue var))]
        [else (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e x cont)
    (match e
        [(Var xvar) (Seq (Assign (Var x) (Var xvar)) cont)]
        [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
        [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
        [(Void) (Seq (Assign (Var x) (Void)) cont)]
        [(GetBang var) (Seq (Assign (Var x) (Var var)) cont)]
        [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
        [(If cond exp1 exp2) (explicate_pred cond (explicate_assign exp1 x cont) (explicate_assign exp2 x cont))]
        [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
        [(SetBang v exp) (explicate_effect e (Seq (Assign (Var x) (Void)) cont))]
        [(WhileLoop cnd body) (explicate_effect e (Seq (Assign (Var x) (Void)) cont))]
        [(Begin es exp) (foldr explicate_effect (explicate_assign exp x cont) es)]
        [(Allocate len type) (Seq (Assign (Var x) e) cont)]
        [(GlobalValue var) (Seq (Assign (Var x) e) cont)]
        [(Collect bytes) (Seq (Collect bytes) cont)]
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
        [(Seq (Prim 'vector-set! (list vecName ind rhs)) t*)
                (define offset (* 8 (+ (Int-value ind) 1)))
                (append (list (Instr 'movq (list vecName (Reg 'r11)))
                              (Instr 'movq (list (select-instructions-atomic rhs) (Deref 'r11 offset)))
                        ) 
                        (select-instructions-statement t*)
                )
        ]
        [(Seq (Collect bytes) t*) 
            (append
                (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
                      (Instr 'movq (list (Imm bytes) (Reg 'rsi)))
                       ;;;   TODO: argument of collect
                      (Callq 'collect 2)
                )
                (select-instructions-statement t*)
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

;;; TODO
(define (ptr? type)
  (match type
    [`(Vector ,ts ...) 1]
    [_ 0]))

(define (ptr-bool? type)
  (match type
    [`(Vector ,ts ...) #t]
    [_ #f]))

(define (get-vector-metadata len T cur_tag cur_ind)
  (define initial_tag (bitwise-ior 1 (arithmetic-shift len 1)))
  (for/fold ([cur_tag initial_tag])
            ([type T]
             [cur_ind (range 7 (+ 7 len))])
    (bitwise-ior cur_tag (arithmetic-shift (ptr? type) cur_ind)))
)

(define (select-instructions-assignment e x)
    (match e
        [(Int i) (list (Instr 'movq (list (select-instructions-atomic e) x)))]
        [(Var v) (list (Instr 'movq (list e x)))]
        [(Bool b) (list (Instr 'movq (list (select-instructions-atomic e) x)))]
        [(Void) (list (Instr 'movq (list (select-instructions-atomic e) x)))]
        [(Prim 'vector-ref (list vecName ind))
            (define offset (* 8 (+ (Int-value ind) 1)))
            (list (Instr 'movq (list vecName (Reg 'r11)))
                  (Instr 'movq (list (Deref 'r11 offset) x))
            )
        ]
        [(Prim 'vector-set! (list vecName ind rhs))
            (define offset (* 8 (+ (Int-value ind) 1)))
            (list (Instr 'movq (list vecName (Reg 'r11)))
                  (Instr 'movq (list (select-instructions-atomic rhs) (Deref 'r11 offset)))
                  (Instr 'movq (list (Imm 0) x))
            )
        ]
        ;;; TODO: Check this
        [(Prim 'vector-length (list vecName))
            (list (Instr 'movq (list vecName (Reg 'r11)))
                  (Instr 'movq (list (Deref 'r11 0) (Reg 'r11)))
                  (Instr 'sarq (list (Imm 1) (Reg 'r11)))
                  (Instr 'andq (list (Imm 63) (Reg 'r11)))
                  (Instr 'movq (list (Reg 'r11) x))
            )
        ]
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
        [(GlobalValue var) (list (Instr 'movq (list (Global var) x)))]
        [(Allocate len `(Vector ,T ...))
            (define tag (get-vector-metadata len T 0 7))
            (define offset (* 8 (+ len 1)))
            (list (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
                  (Instr 'addq (list (Imm offset) (Global 'free_ptr)))
                  (Instr 'movq (list (Imm tag) (Deref 'r11 0)))
                  (Instr 'movq (list (Reg 'r11) x))
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

(define (check-cond e)
    (match e
        [(Imm e) #f]
        [(Global g) #f]
        [_ #t]
    )
)

(define (check-deref e)
    (match e
        [(Deref r i) (Reg r)]
        [_ e]
    )
)


(define (list-to-set lst)
    (list->set (for/list ([e lst] #:when (check-cond e)) (check-deref e)))  
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
        (define output (transfer node instrs input))
        (cond [(not (equal? output (dict-ref mapping node)))
            (dict-set! mapping node output)
            (for ([v (in-neighbors G node)])
                (enqueue! worklist v))]))
    mapping
)

(define (uncover-live p)
    (match p
        [(X86Program info e) 
            (set! label-live (make-hash))
            (set! live-after-sets (make-hash))
            (define cfgEdges '())
            (dict-for-each e 
                (lambda (lbl instrs) (set! cfgEdges (append cfgEdges (makeCFG lbl (Block-instr* instrs)))))
            )

            (define graph (make-multigraph cfgEdges))
            (define graphTransp (transpose graph))
            (define topoOrder (tsort graphTransp))
            (dict-set! label-live 'conclusion (set (Reg 'rax) (Reg 'rsp)))
            (analyze_dataflow graphTransp uncover-live-block (set) set-union e)
            (dict-for-each e 
                (lambda (lbl block) 
                    (dict-set! e lbl (Block (dict-set (Block-info block) 'live-after (dict-ref live-after-sets lbl)) (Block-instr* block)))
                )
            )
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
                [(Callq 'collect n) 
                    (cond 
                        [(and (not (set-member? (list->set allRegisters) v)) (ptr-bool? (dict-ref local-vars (Var-name v)))) 
                            (for ([reg allRegisters]) 
                                (add-edge! interference-graph reg v))
                        ]
                    )
                    (add-edge! interference-graph v d)
                ]
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

(define local-vars (make-hash))

(define (build-interference p)
    (match p
        [(X86Program info body)
            (set! local-vars (dict-ref info 'locals-types))
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
    [7 (Reg 'rbx)]
    [8 (Reg 'r12)]
    [9 (Reg 'r13)]
    [10 (Reg 'r14)]
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
    [(Reg 'rbx) 7]
    [(Reg 'r12) 8]
    [(Reg 'r13) 9]
    [(Reg 'r14) 10]
    [(Reg 'rax) -1]
    [(Reg 'rsp) -2]
    [(Reg 'rbp) -3]
    [(Reg 'r11) -4]
    [(Reg 'r15) -5]
  )
)

(define allRegisters 
    (list
        (Reg 'rcx)
        (Reg 'rdx)
        (Reg 'rsi)
        (Reg 'rdi)
        (Reg 'r8)
        (Reg 'r9)
        (Reg 'r10)
        (Reg 'rbx)
        (Reg 'r12)
        (Reg 'r13)
        (Reg 'r14)
        (Reg 'rax)
        (Reg 'rsp)
        (Reg 'rbp)
        (Reg 'r15)
        (Reg 'r11)
    )
)

(struct node (name [blockedColorsSet #:mutable]))

(define (assign-homes-convert e varmap usedCalleeNum)
    (match e
        [(Var e) 
            (define color (dict-ref varmap (Var e)))
            (cond   
                [(< color 11) (color-to-register color)]
                [(odd? color) (Deref 'rbp (- (* 8  (+ (/ (- color 9) 2) usedCalleeNum))) )]
                [else (Deref 'r15 (- (* 8  (/ (- color 10) 2))))]
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

(define cmp-<                 
  (lambda (node1 node2)         
    (< (length (set-to-list (node-blockedColorsSet node1))) (length (set-to-list (node-blockedColorsSet node2)))) )
)

(define (mex v s [i 0])
    (if (eq? i 11) 
        (if (ptr-bool? (dict-ref local-vars (Var-name v))) (set! i 12) (set! i 11)) 
        (set! i i)
    )

    (match (member i s)
        [#f i]
        [_ (if (< i 11) (mex v s (+ i 1)) (mex v s (+ i 2)))
        ]
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
                    (define curColor (mex (node-name curNode) (set-to-list (node-blockedColorsSet curNode))))
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
                [(> max 10) (/ (- max 9) 2) ]
                [else 0]
            ) 
        ]
        [_  
            (match (car (car varColors))
                [(Var _) (define color (cdr (car varColors)) )
                    (cond 
                        [(< color max) (num-spilled-var (cdr varColors) max)]
                        [(odd? color) (num-spilled-var (cdr varColors) color)]
                        [else (num-spilled-var (cdr varColors) max)]
                    )
                ]
                [_ (num-spilled-var (cdr varColors) max)]
            )
        ]
    )
)

(define (num-root-spilled-var varColors [max 0]) 
    (match varColors
        ['()
            (cond
                [(> max 10) (/ (- max 10) 2) ]
                [else 0]
            ) 
        ]
        [_  
            (match (car (car varColors))
                [(Var _) (define color (cdr (car varColors)) )
                    (cond 
                        [(< color max) (num-root-spilled-var (cdr varColors) max)]
                        [(even? color) (num-root-spilled-var (cdr varColors) color)]
                        [else (num-root-spilled-var (cdr varColors) max)]
                    )
                ]
                [_ (num-root-spilled-var (cdr varColors) max)]
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
                        [(< color 11) 
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
            (define numRootSpilledVariables (num-root-spilled-var varColors))
            (define usedCallee (used-callee varColors))

            (dict-for-each body
                (lambda (lbl instrs)
                    (match (dict-ref body lbl)
                        [(Block sinfo instrs) (dict-set! body lbl (Block sinfo (assign-homes instrs varColors (length (set-to-list usedCallee)))))] 
                    )
                )
            )

            (X86Program (dict-set (dict-set (dict-set info 'stack-space numSpilledVariables) 'num-root-spills numRootSpilledVariables) 'used_callee usedCallee) body)
        ]
    )
)

(define (patch-instructions-convert stm)
    (match stm
        [(Instr 'movzbq (list (ByteReg 'al) (Deref reg1 offset))) 
                (list
                    (Instr 'movzbq (list (ByteReg 'al) (Reg 'rax)))
                    (Instr 'movq (list (Reg 'rax) (Deref reg1 offset)))
                )
        ]
        [(Instr 'cmpq (list src (Imm n))) 
                (list
                    (Instr 'movq (list (Imm n) (Reg 'rax)))
                    (Instr 'cmpq (list src (Reg 'rax)))
                )
        ]
        [(Instr op (list (Deref reg1 offset_1) (Deref reg2 offset_2))) 
            ;;; (cond
                ;;; [(eq? offset_1 offset_2) '()]
                ;;; [else 
                    (list
                        (Instr 'movq (list (Deref reg1 offset_1) (Reg 'rax)))
                        (Instr op (list (Reg 'rax) (Deref reg2 offset_2)))
                    )
                ;;; ]
            ;;; )
        ]
        [(Instr op (list (Reg reg1) (Reg reg2)))
            ;;; (cond
                ;;; [(eq? reg1 reg2) '()]
                ;;; [else 
                    (list (Instr op (list (Reg reg1) (Reg reg2))))
                ;;; ]
            ;;; )
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

(define (zeroOutRootStack num [i 0])
    (cond 
        [(> i (- num 1)) '()]
        [else (append (list (Instr 'movq (list (Imm 0) (Deref 'r15 (* 8 i))))) (zeroOutRootStack num (+ i 1)))]
    )
)

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
    (match p
        [(X86Program info es) 
            (define S (dict-ref info 'stack-space))
            (define C (length (set-to-list (dict-ref info 'used_callee))))
            (define A (- (align (+ (* 8 S) (* 8 C)) 16) (* 8 C)))
            (define R (* 8 (dict-ref info 'num-root-spills)))
            (dict-set! es 'main 
                (Block info (append (list (Instr 'pushq (list (Reg 'rbp)))) 
                                                    (list (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))) 
                                                    (push-calle-saved (dict-ref info 'used_callee)) 
                                                    (list (Instr 'subq (list (Imm A) (Reg 'rsp))))
                                                    
                                                    (list (Instr 'movq (list (Imm 16384) (Reg 'rdi))))
                                                    (list (Instr 'movq (list (Imm 16384) (Reg 'rsi))))
                                                    (list (Callq 'initialize 2))
                                                    (list (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15))))

                                                    (zeroOutRootStack (dict-ref info 'num-root-spills))
                                                    (list (Instr 'addq (list (Imm R) (Reg 'r15))))
                                                    (list (Jmp 'start))
                            )
                )
            )
            (dict-set! es 'conclusion 
                            (Block info (append  (list  (Instr 'subq (list (Imm R) (Reg 'r15))))
                                                        (list (Instr 'addq (list (Imm A) (Reg 'rsp))))
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
     ("shrink", shrink, interp-Lfun, type-check-Lfun)
     ("uniquify", uniquify, interp-Lfun, type-check-Lfun)
     ("reveal functions", reveal-functions, interp-Lfun, type-check-Lfun)
     ("limit functions", limit-functions, interp-Lfun, type-check-Lfun)
     ("expose allocation", expose_allocation, interp-Lfun, type-check-Lfun)
     ("uncover get!", uncover-get!, interp-Lfun, type-check-Lfun)
    ;;;  ("remove complex opera*", remove-complex-opera*, interp-Lvec, type-check-Lvec)
    ;;;  ("explicate control", explicate_control, interp-Cvec, type-check-Cvec)
    ;;;  ("instruction selection", select-instructions, interp-x86-0)
    ;;;  ("uncover live", uncover-live, interp-x86-0)
    ;;;  ("interference graph", build-interference, interp-x86-0)
    ;;;  ("allocate registers", allocate-registers, interp-x86-0)
    ;;;  ("patch instructions", patch-instructions, interp-x86-0)
    ;;;  ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))