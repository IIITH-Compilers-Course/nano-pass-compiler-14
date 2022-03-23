#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "priority_queue.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
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

(define caller-saved-registers (list
                                (Reg 'rax)
                                (Reg 'rcx)
                                (Reg 'rdx)
                                (Reg 'rsi)
                                (Reg 'rdi)
                                (Reg 'r8)
                                (Reg 'r9)
                                (Reg 'r10)
                                (Reg 'r11)))

(define argument-registers (list
                            (Reg 'rdi)
                            (Reg 'rsi)
                            (Reg 'rdx)
                            (Reg 'rcx)
                            (Reg 'r8)
                            (Reg 'r9)))

(define registers-for-coloring (list
                                (Reg 'rcx)
                                (Reg 'rdx)
                                (Reg 'rsi)
                                (Reg 'rdi)
                                (Reg 'r8)
                                (Reg 'r9)
                                (Reg 'r10)
                                (Reg 'r11)
                                (Reg 'rbx)
                                (Reg 'r12)
                                (Reg 'r13)
                                (Reg 'r14)))


(define unavailable-registers-for-coloring (set
                                (Reg 'rax)
                                (Reg 'rsp)
                                (Reg 'rbp)
                                (Reg 'r15)))

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
    [(Reg 'r15) -4]))

(define (color-to-register color)
  (cond
    [(equal? color 0) (Reg 'rcx)]
    [(equal? color 1) (Reg 'rdx)]
    [(equal? color 2) (Reg 'rsi)]
    [(equal? color 3) (Reg 'rdi)]
    [(equal? color 4) (Reg 'r8)]
    [(equal? color 5) (Reg 'r9)]
    [(equal? color 6) (Reg 'r10)]
    [(equal? color 7) (Reg 'r11)]
    [(equal? color 8) (Reg 'rbx)]
    [(equal? color 9) (Reg 'r12)]
    [(equal? color 10) (Reg 'r13)]
    [(equal? color 11) (Reg 'r14)]))

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
    ;;modified partial evaluator
    [(Var x) (Var x)]
    [(Let var rhs body)
    (Let var (pe-exp rhs) (pe-exp body))]
    ;;modified partial evaluator ends
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
       ;;(error "TODO: code goes here (uniquify-exp, symbol?)")]
      [(Int n) (Int n)]
      [(Let x e body)
       (define new_e ((uniquify-exp env) e))
       (define new_x (gensym x))
       (define new_env (dict-set env x new_x))
       (define new_body ((uniquify-exp new_env) body))
       (Let new_x new_e new_body)]
       ;;(error "TODO: code goes here (uniquify-exp, let)")]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-operands env)
  (lambda (e)
    (displayln e)
    (match e
      [(Int n) (Int n)]
      [(Var x) (Var x)]
      [(Prim 'read '()) (Prim 'read '())]
      [(Let var e1 e2)
       (Let var ((remove-complex-operands env) e1) ((remove-complex-operands env) e2))]
      [(Prim '- (list e1))
       (displayln e1)
       (cond
         [(or (Int? e1) (Var? e1)) (Prim '- (list e1))]
         [else
          (define new_e1 (gensym "e1"))
          (Let new_e1 ((remove-complex-operands env) e1) (Prim '- (list (Var new_e1))))])]
       ;;(define var (gensym "var"))
       ;;(Let var e (Var var))]
      [(Prim op (list e1 e2))
       (cond
         [(or (Int? e1) (Var? e1))
          (cond
            [(or (Int? e2) (Var? e2)) (Prim op (list e1 e2))]
            [else
             (define new_e2 (gensym "e2"))
             (Let new_e2 ((remove-complex-operands env) e2) (Prim op (list e1 (Var new_e2))))])]
         [else
          (define new_e1 (gensym "e1"))
          (cond
            [(or (Int? e2) (Var? e2)) (Let new_e1 ((remove-complex-operands env) e1) (Prim op (list (Var new_e1) e2)))]
            [else
             (define new_e2 (gensym "e2"))
             (Let new_e1 ((remove-complex-operands env) e1) (Let new_e2 ((remove-complex-operands env) e2) (Prim op (list (Var new_e1) (Var new_e2)))))])])]
      [else
       (displayln e) e]
      )))

(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info ((remove-complex-operands '()) e))]))
  ;;(error "TODO: code goes here (remove-complex-opera*)"))


(define (explicate-tail e)
    (match e
      [(Var x) (Return (Var x))]
      [(Int n) (Return (Int n))]
      [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
      [(Prim op es) (Return (Prim op es))]
      [else (error "explicate_tail unhandled case" e)]))

(define (explicate-assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) e) cont)]
    [else (error "explicate_assign unhandled case" e)]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info e) (CProgram info `((start . ,(explicate-tail e))))]))
  ;;(error "TODO: code goes here (explicate-control)"))

;; select-instructions : C0 -> pseudo-x86
(define (sel-instr-atm e)
  (match e
    [(Var x) e]
    [(Int n) (Imm n)]))

(define (sel-instr-assign v e)
  (match e
    [(Int n)
     (list (Instr 'movq (list (sel-instr-atm e) v)))]
    [(Var x)
     (list (Instr 'movq (list (sel-instr-atm e) v)))]
    [(Prim 'read '())
     (list (Callq 'read_int 0)
           (Instr 'movq (list (Reg 'rax) v)))]
    [(Prim '- (list a))
     (list (Instr 'movq (list (sel-instr-atm a) v))
           (Instr 'negq (list v)))]
    [(Prim op (list a1 a2))
     (list (Instr 'movq (list (sel-instr-atm a1) v))
           (Instr 'addq (list (sel-instr-atm a2) v)))]))

(define (sel-instr-stmt stmt)
  (match stmt
    [(Assign (Var v) (Prim op (list (Var v1) e))) #:when (equal? v v1)
     (list (Instr 'addq (list (sel-instr-atm e) (Var v))))]
    [(Assign (Var v) (Prim op (list e (Var v2)))) #:when (equal? v v2)
     (list (Instr 'addq (list (sel-instr-atm e) (Var v))))]
    [(Assign v e) (sel-instr-assign v e)]))

(define (sel-instr-tail e)
  (match e
    [(Seq stmt rest_e)
     (append (sel-instr-stmt stmt) (sel-instr-tail rest_e))]
    [(Return (Prim 'read '()))
     (list (Callq 'read_int)
           (Jmp 'conclusion))]
    [(Return e)
     (append
      (sel-instr-assign (Reg 'rax) e)
      (list (Jmp 'conclusion)))]))

(define (select-instructions p)
  (match p
    [(CProgram info e)
     (X86Program info `((start . ,(Block '() (sel-instr-tail (dict-ref e 'start))))))]))
;;(define (select-instructions p)
  ;;(error "TODO: code goes here (select-instructions)"))

;; liveness-analysis : pseudo-x86 -> pseudo-x86
(define (get-write-set instr)
  (match instr
    [(Instr 'movq (list e1 e2))
     (set e2)]
    [(Instr 'addq (list e1 e2))
     (set e2)]
    [(Instr 'negq (list e1))
     (set e1)]
    [(Callq func-name n) (list->set caller-saved-registers)]
    [else (set)]))

(define (get-read-set instr)
  (match instr
    [(Instr 'movq (list e1 e2))
     (match e1
       [(Imm n) (set)]
       [else (set e1)])]
    [(Instr 'addq (list e1 e2))
     (match e1
       [(Imm n) (set e2)]
       [else (set e1 e2)])]
    [(Instr 'negq (list e1))
     (set e1)]
    [(Callq func-name n)
     (cond
       [(<= n 6) (list->set (take argument-registers n))]
       [else (list->set (take argument-registers 6))])]
    [else (set)]))

(define (create-live-after instrs)
  (define rev-instrs (reverse instrs))
  (define lafter (set))
  (define live-after-sets (for/list ([instr rev-instrs])
    (match instr
      [(Jmp 'conclusion)
       (set! lafter (set (Reg 'rax)))
       (set (Reg 'rax))]
      [else
       (define write-set (get-write-set instr))
       (define read-set (get-read-set instr))
       (define las (set-union (set-subtract lafter write-set) read-set))
       (set! lafter las)
       las])))
  (append (reverse live-after-sets) (list (set))))

(define (uncover-live p)
  (match p
    [(X86Program info e)
     (match e
      [`((start . ,(Block sinfo instrs)))
       (X86Program (dict-set info 'live-after-sets (create-live-after instrs)) `((start . ,(Block sinfo instrs))))])]))

;; interference-graph : pseudo-x86 -> pseudo-x86
(define (print-graph graph)
  (for ([u (in-vertices graph)])
    (for ([v (in-neighbors graph u)])
      (display (format "~a -> ~a;\n" u v))
      )))

(define (create-ig live-after-sets instrs locals)
  ;;(displayln live-after-sets)
  (define cnt 0)
  ;;(define edges '())
  (define IG (undirected-graph '()))
  (for ([instr instrs])
    (set! cnt (+ 1 cnt))
    (match instr
      [(Instr 'movq (list e1 e2))
       (for ([e (list-ref live-after-sets cnt)])
         (when (and (not (equal? e e1)) (not (equal? e e2))) (add-edge! IG e e2)))]
      [(Instr 'addq (list e1 e2))
       (for ([e (list-ref live-after-sets cnt)])
         (when (not (equal? e e2)) (add-edge! IG e e2)))]
      [(Instr 'negq (list e1))
       (for ([e (list-ref live-after-sets cnt)])
         (when (not (equal? e e1)) (add-edge! IG e e1)))]
      [(Callq func-name n)
       (for ([e (list-ref live-after-sets cnt)])
         (for ([reg caller-saved-registers])
           (when (not (equal? e reg)) (add-edge! IG e reg))))]
      [else (displayln "hello")]))
  ;;(displayln edges)
  ;;(define ig (undirected-graph edges))
  (define vertices (list->set (get-vertices IG)))
  (for ([x locals])
    (when (not (set-member? vertices (car x)))
      (add-vertex! IG (Var (car x)))))
  (print-graph IG)
  IG)

(define (build-interference p)
  (match p
    [(X86Program info e)
     (match e
       [`((start . ,(Block sinfo instrs)))
        (X86Program (dict-set info 'conflicts (create-ig (dict-ref info 'live-after-sets) instrs (dict-ref info 'locals-types))) `((start . ,(Block sinfo instrs))))])]))

;;allocate-registers : pseudo-x86 -> pseudo-x86
(define (choose-color unavailable)
  (for/first ([c (in-naturals)]
              #:when (not (set-member? unavailable c)))
    c))

(define (color-graph info)
  (define locals (dict-ref info 'locals-types))
  (define IG (dict-ref info 'conflicts))
  (define unavail-colors (make-hash)) ;;pencil marks
  (define colors (make-hash)) ;;final colors
  (define pq-node (make-hash)) ;;priority queue nodes hashmap
  (define (comparator u v)
    (>= (set-count (hash-ref unavail-colors u))
        (set-count (hash-ref unavail-colors v))))
  (define pq (make-pqueue comparator))
  
  ;;initialising DSATUR
  (for ([x locals])
    (define t (Var (car x)))
    (define adjacent-regs
      (filter (lambda (u) (set-member? unavailable-registers-for-coloring u)) (get-neighbors IG t)))
    (define adjacent-colors (list->set (map register-to-color adjacent-regs)))
    (hash-set! unavail-colors t adjacent-colors)
    (hash-set! pq-node t (pqueue-push! pq t)))
  (displayln unavail-colors)
  (displayln "pq count")
  (displayln (pqueue-count pq))
  ;;graph coloring
  (while (> (pqueue-count pq) 0)
         (define node (pqueue-pop! pq))
         ;;(displayln node)
         (define node-color (choose-color (hash-ref unavail-colors node)))
         (hash-set! colors node node-color)
         ;;(if (has-vertex? IG node) (displayln "yes") (displayln "no"))
         ;;(print-graph IG)
         ;;(displayln (format "neighbors of ~a are ~a\n" node (get-neighbors IG node)))
         ;;(define node2 (car (get-vertices IG)))
         ;;(displayln node2)
         ;;displayln "-----------")
         ;;(for ([u (in-neighbors IG node2)])
           ;;(display (format "~a -> ~a;\n" u node2)))
         (for ([u (in-neighbors IG node)])
           ;;(displayln (format "~a -> ~a;\n" node u))
           (when (not (set-member? unavailable-registers-for-coloring u))
             (hash-set! unavail-colors u
                        (set-add (hash-ref unavail-colors u) node-color))
             (pqueue-decrease-key! pq (hash-ref pq-node u)))))
  colors)
  
(define (allocate-registers p)
  (match p
    [(X86Program info e)
     (match e
       [`((start . ,(Block sinfo instrs)))
        (define colors (color-graph info))
        (X86Program (dict-set info 'colors colors) `((start . ,(Block sinfo instrs))))])]))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (calc-stack-space ls) (* 8 (length ls)))

(define (assign-homes-instr instrs locals-home)
  (match instrs
    [(cons (Instr instr args) rest)
     (cons (Instr instr (for/list ([arg args])
                          (if (Var? arg) (dict-ref locals-home (Var-name arg)) arg))) (assign-homes-instr rest locals-home))]
    [(cons instr ss) (cons instr (assign-homes-instr ss locals-home))]
    [else instrs]))
 
(define (assign-home-to-locals locals-types n locals-home colors)
  (cond
    [(empty? locals-types) locals-home]
    [else 
     (define item (car locals-types))
     (define arg (car item))
     (cond
       [(hash-has-key? colors (Var arg))
        (define new-locals-home (dict-set locals-home arg (color-to-register (hash-ref colors (Var arg)))))
        (assign-home-to-locals (cdr locals-types) n new-locals-home colors)]
       [else
         (define new-locals-home (dict-set locals-home arg (Deref 'rbp (* -8 n))))
         (assign-home-to-locals (cdr locals-types) (add1 n) new-locals-home colors)])]))
  
  
(define (assign-homes p)
  (match p
    [(X86Program info e)
     (match e
      [`((start . ,(Block sinfo instrs)))
        (define locals-home (assign-home-to-locals (dict-ref info 'locals-types) 1 '() (dict-ref info 'colors)))
        (define stack-space (calc-stack-space (dict-ref info 'locals-types)))
        (X86Program (dict-set info 'stack-space stack-space) `((start . ,(Block sinfo (assign-homes-instr instrs locals-home)))))])]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instr instr)
  (match instr
    [(Instr op (list (Deref reg1 off1) (Deref reg2 off2)))
     (list (Instr 'movq (list (Deref reg1 off1) (Reg 'rax)))
                 (Instr op (list (Reg 'rax) (Deref reg2 off2))))]
    ;;[(cons instr ss) (cons (list instr) (patch-instr ss))]
    [else (list instr)]))

(define (patch-instructions p)
  (match p
    [(X86Program info e)
     (match e
       [`((start . ,(Block sinfo instrs)))
        (X86Program info `((start . ,(Block sinfo (append-map patch-instr instrs)))))])]))
  ;;(error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86 -> x86

(define (get-main-block n mainl)
  (set! mainl (list (Instr 'pushq (list (Reg 'rbp)))))
  (set! mainl (append mainl (list (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))))
  (cond
    [(equal? (modulo n 16) 0) (set! mainl (append mainl (list (Instr 'subq (list (Imm n) (Reg 'rsp))))))]
    [else (set! mainl (append mainl (list (Instr 'subq (list (Imm (+ 8 n)) (Reg 'rsp))))))])
  (set! mainl (append mainl  (list (Jmp 'start))))
  mainl)
(define (get-conclusion-block n concl)
  (cond
    [(equal? (modulo n 16) 0) (set! concl (append concl (list (Instr 'addq (list (Imm n) (Reg 'rsp))))))]
    [else (set! concl (append concl (list (Instr 'addq (list (Imm (+ 8 n)) (Reg 'rsp))))))])
  (set! concl (append concl (list (Instr 'popq (list (Reg 'rbp))))))
  (set! concl (append concl  (list (Retq))))
  concl)


(define (prelude-and-conclusion p)
  (match p
    [(X86Program info e)
     (match e
       [`((start . ,(Block sinfo instrs)))
        (X86Program info `((start . ,(Block sinfo instrs))
                           (main . , (Block `() (get-main-block (dict-ref info 'stack-space) '() )) )
                           (conclusion . , (Block `() (get-conclusion-block (dict-ref info 'stack-space) '() )) )))])]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("partial_pass", pe-Lint, interp-Lvar) 
     ("uniquify" ,uniquify ,interp-Lvar, type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar, type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar, type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ("liveness analysis", uncover-live, interp-x86-0)
     ("interference graph", build-interference, interp-x86-0)
     ("register allocation", allocate-registers, interp-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))