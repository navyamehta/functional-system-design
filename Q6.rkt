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

(struct newbox (exp) #:transparent)

(struct openbox (exp) #:transparent)

(struct setbox (bexp vexp) #:transparent)

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
    [`(box ,x) (newbox (parse x))]
    [`(unbox ,x) (openbox (parse x))]
    [`(fun (,x) ,bdy) (fun x (parse bdy))]
    [`(,f ,x) (app (parse f) (parse x))]
    [`(seq ,x ,y) (seq (parse x) (parse y))]
    [`(setbox ,x ,y) (setbox (parse x) (parse y))]
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
          (let ((argeval (interp arg-exp env str)))
          (let ((len (length (result-newstore argeval))))
            (let ((newstr (cons (sub len (result-val argeval)) (result-newstore argeval))))
              (interp bdy (cons (sub v len) cl-env) newstr))))])]
    [(bin op x y)
     (let ((r (interp x env str)))
       (let ((w (interp y env (result-newstore r))))
         (let ((q ((op-trans op) (result-val r) (result-val w))))
           (result q (result-newstore w)))))]
    [(newbox x)
       (let ((temp (interp x env str)))
         (let ((len (length (result-newstore temp))))
           (result len (cons (sub len (result-val temp)) (result-newstore temp)))))]
    [(openbox x)
     (let ((intem (interp x env str)))
       (result (looking (result-val intem) (result-newstore intem)) (result-newstore intem)))]
    [(setbox x y)
     (let ((temp (interp x env str)))
       (let ((temp2 (interp y env (result-newstore temp))))
       (result void (updatestr (result-val temp) (result-val temp2) (result-newstore temp2)))))]
    [(seq x y)
     (let ((r (interp x env str)))
       (interp y env (result-newstore r)))]
    [x (if (number? x)
           (result x str)
           (result (lookup x env str) str))]))

(define (updatestr addr y str)
  (cond
    [(equal? (sub-name (first str)) addr) (cons (sub addr y) (rest str))]
    [else (updatestr addr y (append (rest str) (list (first str))))]))
             
; completely inadequate tests
;;(check-expect (parse '(* 2 3)) (bin '* 2 3))

;;(check-expect (interp (parse '(set x 3)) empty empty) 6)

;;(test)