#lang racket

(require test-engine/racket-tests)

(struct bin (op fst snd) #:transparent) ; op is a symbol; fst, snd are ASTs.

(struct fun (param body) #:transparent) ; param is a symbol; body is an AST.

(struct app (fn arg) #:transparent) ; fn and arg are ASTs.

;; An AST is a (union bin fun app).

(struct sub (name val) #:mutable #:transparent)

;; A substitution is a (sub n v), where n is a symbol and v is a number.
;; An environment (env) is a list of substitutions.

(struct closure (var body envt) #:transparent)

(struct seq (fst snd) #:transparent)

(struct set (var newval) #:transparent)

(struct result (val newstore) #:transparent)

;; A closure is a (closure v bdy env), where
;; v is a symbol, bdy is an AST, and env is a environment.

;; parse: sexp -> AST

(define (parse sx)
  (match sx
    [`(with ((,nm ,nmd)) ,bdy) (app (fun nm (parse bdy)) (parse nmd))]
    [`(+ ,x ,y) (bin '+ (parse x) (parse y))]
    [`(* ,x ,y) (bin '* (parse x) (parse y))]
    [`(- ,x ,y) (bin '- (parse x) (parse y))]
    [`(/ ,x ,y) (bin '/ (parse x) (parse y))]
    [`(fun (,x) ,bdy) (fun x (parse bdy))]
    [`(,f ,x) (app (parse f) (parse x))]
    [`(seq ,x ,y) (seq (parse x) (parse y))]
    [`(set ,x ,y) (set x (parse y))]
    [x x]))

; op-trans: symbol -> (number number -> number)
; converts symbolic representation of arithmetic function to actual Racket function
(define (op-trans op)
  (match op
    ['+ +]
    ['* *]
    ['- -]
    ['/ /]))

;; lookup: symbol env -> (union number fun)
;; looks up a substitution in an environment (topmost one)

(define (lookup var env str)
  (looking (looking var env) str))

(define (looking var lst)
  (cond
    [(empty? lst) (error 'interp "unbound variable ~a" var)]
    [(equal? var (sub-name (first lst))) (sub-val (first lst))]
    [else (looking var (rest lst))]))


;; interp: AST env -> (union number closure)

(define (interp ast env str)
  (match ast
    [(fun v bdy) (result (closure v bdy env) str)]
    [(app fun-exp arg-exp)
       (match (interp fun-exp env str)
         [(result (closure v bdy cl-env) str)
          (let ((len (length str)))
            (let ((newstr (cons (sub len (result-val (interp arg-exp env str))) str)))
              (interp bdy (cons (sub v len) cl-env) newstr)))])]
    [(bin op x y)
     (let ((r (interp x env str)))
       (let ((w (interp y env (result-newstore r))))
         (let ((q ((op-trans op) (result-val r) (result-val w))))
           (result q (result-newstore w)))))]
    [(set x y)
     (let ((strloc (looking x env)))
       (let ((newstr (cons (sub strloc (result-val (interp y env str))) str)))
         (result void newstr)))]
    [(seq x y)
     (let ((r (interp x env str)))
       (interp y env (result-newstore r)))]
    [x (if (number? x)
           (result x str)
           (result (lookup x env str) str))]))
             
; completely inadequate tests
;;(check-expect (parse '(* 2 3)) (bin '* 2 3))

;;(check-expect (interp (parse '(set x 3)) empty empty) 6)

;;(test)
