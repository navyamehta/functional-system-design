#lang racket

;; Navya Mehta and Sherman Grewal

(define-struct returner (cd vr ctr))

(define (compile-simp prog)
  (cond
    [(empty? prog) empty]
    [(not (equal? (first prog) 'vars)) (let ((eval (comp prog empty empty 0)))
                                         (append (returner-cd eval) (list (list 'halt)) (list (list 'data 'printer 0)) (returner-vr eval)))]
    [(or (equal? (length prog) 2) (empty? (third prog))) (varhandle (second prog))]
    [else (let ((eval (comp (rest (rest prog)) empty (varhandle (second prog)) 0)))
            (append (returner-cd eval) (list (list 'halt)) (list (list 'data 'printer 0)) (returner-vr eval)))]))

(define (varhandle vars)
  (cond
    [(empty? vars) empty]
    [else (cons (cons 'data (first vars)) (varhandle (rest vars)))]))

(define (comp code acc vars ctr)
  (cond
    [(empty? code) (make-returner (reverse acc) vars ctr)]
    [else (let ((instr (first code)))
            (cond
              [(equal? (first instr) 'skip) (comp (rest code) acc vars ctr)]
              [(equal? (first instr) 'while)
               (let ((lp (comp (rest (rest instr)) empty vars (add1 ctr))))
                 (let ((bexper (bexp (second instr) (string->symbol (string-append "temp" (number->string ctr))) ctr)))
                 (comp (rest code) (append (reverse (append (list (list 'label (string->symbol (string-append "whiler" (number->string ctr))))) (returner-cd bexper)
                                                            (list (list 'branch (string->symbol (string-append "temp" (number->string ctr))) (string->symbol (string-append "LP" (number->string ctr))))
                                                                  (list 'jump (string->symbol (string-append "END" (number->string ctr))))
                                                                  (list 'label (string->symbol (string-append "LP" (number->string ctr))))) (returner-cd lp)
                                                            (list  (list 'jump (string->symbol (string-append "whiler" (number->string ctr)))) (list 'label (string->symbol (string-append "END" (number->string ctr))))))) acc)
                       (append (returner-vr lp) (varhandle (returner-vr bexper)) (varhandle (list (list (string->symbol (string-append "temp" (number->string ctr))) 0)))) (add1 (returner-ctr lp)))))]
              [(equal? (first instr) 'print) (cond
                                               [(string? (second instr)) (comp (rest code) (append (list (list 'print-string (second instr))) acc) vars ctr)]
                                               [(numsym? (second instr)) (comp (rest code) (append (list (list 'print-val (second instr))) acc) vars ctr)]
                                               [else (let ((r (aexp (second instr) empty empty ctr)))
                                                       (let ((eval (sethandle (returner-cd r))))
                                                         (comp (rest code) (append (list (list 'print-val 'printer)) (list (list 'move 'printer (first (first (returner-vr r))))) (reverse eval) acc)
                                                             (append vars (varhandle (returner-vr r))) (add1 ctr))))])]
              [(equal? (first instr) 'seq) (comp (append (rest instr) (rest code)) acc vars ctr)]
              [(equal? (first instr) 'set) (let ((r (aexp (third instr) empty empty ctr)))
                                             (let ((eval (sethandle (returner-cd r))))
                                               (cond
                                                 [(numsym? eval) (comp (rest code) (append (list (list 'move (second instr) eval)) acc) vars ctr)]
                                                 [else (comp (rest code) (append (list (list 'move (second instr) (first (first (returner-vr r))))) (reverse eval) acc) (append vars (varhandle (returner-vr r))) (+ ctr 2))])))]
              [(equal? (first instr) 'iif)
               (let ((truer (comp (list (third instr)) empty vars (add1 ctr))))
                 (let ((falser (comp (list (fourth instr)) empty vars (add1 (returner-ctr truer)))))
                   (let ((b (bexp (second instr) (string->symbol (string-append "iffer" (number->string ctr))) ctr)))
                   (comp (rest code) (append (reverse (append (returner-cd b) (list (list 'branch (string->symbol (string-append "iffer" (number->string ctr)))
                                                                            (string->symbol (string-append "TRUE" (number->string ctr))))) (returner-cd falser)
                                                                              (list (list 'jump (string->symbol (string-append "OTHER" (number->string ctr))))
                                                                                    (list 'label (string->symbol (string-append "TRUE" (number->string ctr)))))
                                                              (returner-cd truer) (list (list 'label (string->symbol (string-append "OTHER" (number->string ctr))))))) acc)
                         (append (returner-vr truer) (getnewval vars (returner-vr falser) empty) (varhandle (returner-vr b)) (list (list 'data (string->symbol (string-append "iffer" (number->string ctr))) 0))) (add1 (returner-ctr falser))))))] 
              ))]))

(define (sethandle lst)
  (cond
    [(empty? lst) empty]
    [(numsym? lst) lst]
    [(equal? (first (first lst)) '+) (cons (list 'add (second (first lst)) (third (first lst)) (fourth (first lst))) (sethandle (rest lst)))]
    [(equal? (first (first lst)) '-) (cons (list 'sub (second (first lst)) (third (first lst)) (fourth (first lst))) (sethandle (rest lst)))]
    [(equal? (first (first lst)) '*) (cons (list 'mul (second (first lst)) (third (first lst)) (fourth (first lst))) (sethandle (rest lst)))]
    [(equal? (first (first lst)) 'div) (cons (list 'div (second (first lst)) (third (first lst)) (fourth (first lst))) (sethandle (rest lst)))]
    [(equal? (first (first lst)) 'mod) (cons (list 'mod (second (first lst)) (third (first lst)) (fourth (first lst))) (sethandle (rest lst)))]
    [else (error "not aexp")]))

(define (aexp expr acc varlst ctr)
  (cond
    [(numsym? expr) (make-returner expr empty ctr)]
    [(and (not (list? (second expr))) (not (list? (third expr)))) (make-returner (reverse (cons (list (first expr) (string->symbol (string-append "setter" (number->string ctr)))
                                                                                                      (second expr) (third expr)) acc)) 
                                                                                 (cons (list (string->symbol (string-append "setter" (number->string ctr))) 0) varlst) (add1 ctr))]
    [(list? (second expr))
     (let ((inner (aexp (second expr) empty varlst ctr)))
       (aexp (list (first expr) (first (first (returner-vr inner))) (third expr)) (append (reverse (returner-cd inner)) acc) (returner-vr inner) (add1 ctr)))]
    [(list? (third expr))
     (let ((inner (aexp (third expr) empty varlst ctr)))
       (aexp (list (first expr) (second expr) (first (first (returner-vr inner)))) (append (reverse (returner-cd inner)) acc) (returner-vr inner) (add1 ctr)))]))

(define (bexp expr var ctr)
  (cond
    [(equal? expr #false) (make-returner (list (list 'gt var 1 5)) empty ctr)]
    [(equal? expr #true) (make-returner (list (list 'lt var 1 5)) empty ctr)]
    [else (let ((symb (convertsym (first expr))))
            (cond
              [(or (equal? symb 'land)(equal? symb 'lor))
               (cond
                 [(and (= (length expr) 2) (equal? symb 'land)) (bexp (append expr (list #true)) var ctr)]
                 [(and (= (length expr) 2) (equal? symb 'lor)) (bexp (append expr (list #false)) var ctr)]
                 [else
                  (let ((qt (andor (rest expr) empty symb)))
                    (let ((val1 (bexp (second qt) (string->symbol (string-append "whatever" (number->string ctr))) (add1 ctr))))
                      (let ((val2 (bexp (third qt) (string->symbol (string-append "however" (number->string ctr))) (+ (returner-ctr val1) 100))))
                        (make-returner (append (returner-cd val1) (returner-cd val2) (list (list symb var (string->symbol (string-append "whatever" (number->string ctr)))
                                                                                    (string->symbol (string-append "however" (number->string ctr))))))
                          (append (returner-vr val1)(returner-vr val2) (list (list (string->symbol (string-append "whatever" (number->string ctr))) 0))
                                  (list (list (string->symbol (string-append "however" (number->string ctr))) 0))) (+ ctr 2)))))])]
              [(equal? symb 'lnot)
               (let ((val1 (bexp (second expr) (string->symbol (string-append "whatever" (number->string ctr))) (add1 ctr))))
                 (make-returner (append (returner-cd val1) (list (list symb var (string->symbol (string-append "whatever" (number->string ctr))))))
                                (append (returner-vr val1)(list (list (string->symbol (string-append "whatever" (number->string ctr))) 0))) (+ ctr 2)))] 
              [else
               (let ((r1 (aexp (second expr) empty empty ctr)))
                 (let ((r2 (aexp (third expr) empty empty ctr)))
                   (let ((val1 (sethandle (returner-cd r1))))
                     (let ((val2 (sethandle (returner-cd r2))))
                       (cond
                         [(and (numsym? val1)(numsym? val2)) (make-returner (list (list symb var val1 val2)) empty ctr)]
                         [(numsym? val1) (make-returner (append val2 (list (list symb var val1 (first (first (returner-vr r2)))))) (returner-vr r2) ctr)]
                         [(numsym? val2) (make-returner (append val1 (list (list symb var (first (first (returner-vr r1))) val2))) (returner-vr r1) ctr)])))))]))]))

(define (convertsym sym)
  (cond
    [(equal? sym '<) 'lt]
    [(equal? sym '<=) 'le]
    [(equal? sym '>) 'gt]
    [(equal? sym '>=) 'ge]
    [(equal? sym '=) 'equal]
    [(equal? sym '!=) 'not-equal]
    [(equal? sym 'and) 'land]
    [(equal? sym 'or) 'lor]
    [(equal? sym 'not) 'lnot]
    [else sym]))

(define (numsym? r)
  (or (number? r)(symbol? r)))

(define (getnewval vars lst acc)
  (cond
    [(empty? vars) (append (reverse acc) lst)]
    [(equal? (first vars) (first lst)) (getnewval (rest vars) (rest lst) acc)]
    [else (getnewval vars (rest lst) (cons (first lst) acc))]))

(define (andor lst acc symb)
  (cond
    [(empty? lst) (andor (reverse acc) empty symb)]
    [(and (< (length lst) 2)(empty? acc)) (first lst)]
    [(>= (length lst) 2)
     (cond
       [(and (list? (first lst))(> (length (first lst)) 2))
        (let ((temp (andor (rest (first lst)) empty (first (first lst)))))
          (cond
            [(and (list? (second lst))(> (length (second lst)) 2))
             (let ((temp2 (andor (rest (second lst)) empty (first (second lst)))))
               (andor (rest (rest lst)) (cons (list symb temp temp2) acc) symb))]
            [else (andor (rest (rest lst)) (cons (list symb temp (second lst)) acc) symb)]))]
       [else (cond
               [(and (list? (second lst))(> (length (second lst)) 2))
                (let ((temp2 (andor (rest (second lst)) empty (first (second lst)))))
                  (andor (rest (rest lst)) (cons (list symb (first lst) temp2) acc) symb))]
               [else (andor (rest (rest lst)) (cons (list symb (first lst) (second lst)) acc) symb)])])]
    [else (cond
            [(and (list? (first lst))(> (length (first lst)) 2))
             (let ((temp (andor (rest (first lst)) empty (first (first lst)))))
               (andor (rest lst) (cons temp acc) symb))]
            [else (andor (rest lst) (cons (first lst) acc) symb)])]))
  


              