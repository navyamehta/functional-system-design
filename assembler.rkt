#lang racket

;; Navya Mehta and Sherman Grewal

(define-struct returner (target constantassoc memassoc))

(define (primp-assemble lst)
  (let ((r (hashmapper lst empty empty empty)))
    (let ((consres (resolver (returner-constantassoc r) (returner-memassoc r) empty #false)))
      (let ((memres (resolver (returner-memassoc r) consres empty #false)))
        (symbolresolve (returner-target r) empty consres memres)))))

(define (hashmapper source target constantassoc memassoc)
  (cond
    [(empty? source) (make-returner (reverse target) constantassoc memassoc)]
    [else (let ((instr (first source)))
            (cond
              [(equal? (first instr) 'const) (let ((dup1 (checker (second instr) constantassoc)))
                                               (cond
                                                 [(equal? dup1 false) (hashmapper (rest source) target (cons (list (second instr) (third instr)) constantassoc) memassoc)]
                                                 [else (error "duplicate")]))]
              [(equal? (first instr) 'data) (let ((dup2 (checker (second instr) memassoc)))
                                              (cond
                                                [(equal? dup2 false) (cond
                                                                       [(list? (third instr)) (hashmapper (rest source) (dataadder (build-list (first (third instr)) (lambda (x) (second (third instr)))) target) constantassoc (cons (list (second instr) (length target)) memassoc))]
                                                                       [else (hashmapper (rest source) (dataadder (rest (rest instr)) target) constantassoc (cons (list (second instr) (length target)) memassoc))])]
                                                [else (error "duplicate")]))]
              [(equal? (first instr) 'label) (let ((dup3 (checker (second instr) constantassoc)))
                                               (cond
                                                 [(equal? dup3 false) (hashmapper (rest source) target  (cons (list (second instr) (length target)) constantassoc) memassoc)]
                                                 [else (error "duplicate")]))]
              [else (hashmapper (rest source) (cons instr target) constantassoc memassoc)]))]))

(define (resolver toberes otherdata acc bool)
  (cond
    [(empty? toberes) (cond
                        [(equal? bool #false) (reverse acc)]
                        [else (resolver (reverse acc) otherdata empty #false)])]
    [else (let ((f (first toberes)))
            (cond
              [(or (number? (second f)) (equal? (second f) #true) (equal? (second f) #false)) (resolver (rest toberes) otherdata (cons f acc) bool)]
              [else (let ((incheck (checker (second f) toberes)))
                      (let ((outcheck (checker (second f) otherdata)))
                        (let ((oldcheck (checker (second f) acc)))
                          (cond
                            [(and (equal? incheck false)(equal? outcheck false)(equal? oldcheck false)) (error "undefined")]
                            [(and (equal? incheck false) (equal? oldcheck false)) (cond
                                                      [(and (symbol? (second outcheck)) (symbol=? (second outcheck) (first f))) (error "circular")]
                                                      [(symbol? (second outcheck)) (resolver (rest toberes) otherdata (cons (list (first f) (second outcheck)) acc) #true)]
                                                      [else (resolver (rest toberes) otherdata (cons (list (first f) (second outcheck)) acc) bool)])]
                            [(and (equal? incheck false) (equal? outcheck false)) (cond
                                                      [(and (symbol? (second oldcheck)) (symbol=? (second oldcheck) (first f))) (error "circular")]
                                                      [(symbol? (second oldcheck)) (resolver (rest toberes) otherdata (cons (list (first f) (second oldcheck)) acc) #true)]
                                                      [else (resolver (rest toberes) otherdata (cons (list (first f) (second oldcheck)) acc) bool)])]
                            [(and (equal? outcheck false) (equal? oldcheck false)) (cond
                                                       [(and (symbol? (second incheck)) (symbol=? (second incheck) (first f))) (error "circular")]
                                                       [(symbol? (second incheck)) (resolver (rest toberes) otherdata (cons (list (first f) (second incheck)) acc) #true)]
                                                       [else (resolver (rest toberes) otherdata (cons (list (first f) (second incheck)) acc) bool)])]))))]))]))

(define (symbolresolve source target constantassoc memassoc)
  (cond
    [(empty? source) (reverse target)]
    [else (let ((instr (first source)))
            (display instr)
            (display newline)
       (cond
         [(symbol? instr)
          (let ((const (checker instr constantassoc)))
            (let ((mem (checker instr memassoc)))
              (cond
                [(and (equal? const false)(equal? mem false)) (error "undefined")]
                [(equal? const false) (symbolresolve (rest source) (cons (second mem) target) constantassoc memassoc)]
                [(equal? mem false) (symbolresolve (rest source) (cons (second const) target) constantassoc memassoc)])))]
         [(number? instr) (symbolresolve (rest source) (cons instr target) constantassoc memassoc)]
         [(equal? (first instr) 'print-string) (symbolresolve (rest source) (cons instr target) constantassoc memassoc)]
         [(equal? (first instr) 'halt) (symbolresolve (rest source) (cons 0 target) constantassoc  memassoc)]
         [(equal? (first instr) 'lit) (cond
                                        [(number? (second instr)) (symbolresolve (rest source) (cons (second instr) target) constantassoc memassoc)]
                                        [else (let ((const (checker (second instr) constantassoc)))
                                                (let ((mem (checker (second instr) memassoc)))
                                                  (cond
                                                    [(and (equal? const false)(equal? mem false)) (display instr) (error "undefined")]
                                                    [(equal? const false) (symbolresolve (rest source) (cons (second mem) target) constantassoc memassoc)]
                                                    [(equal? mem false) (symbolresolve (rest source) (cons (second const) target) constantassoc memassoc)])))])] 
         [(symbolin? (rest instr))
          (let ((eval (inhandling instr constantassoc memassoc)))
            (symbolresolve (rest source) (cons eval target) constantassoc memassoc))]
         [else (symbolresolve (rest source) (cons instr target) constantassoc memassoc)]))]))

(define (symbolin? instr)
  (cond
    [(empty? instr) false]
    [(not (or (number? (first instr)) (string? (first instr)))) true]
    [else (symbolin? (rest instr))]))

(define (dataadder vals target)
  (cond
    [(empty? vals) target]
    [else (dataadder (rest vals) (cons (first vals) target))]))

(define (inhandling instr constantassoc memassoc)
  (unless (inccheck instr constantassoc) (instructhandle (rest instr) constantassoc memassoc (list (first instr)))))

(define (instructhandle instr constantassoc memassoc acc)
    (cond
      [(empty? instr) (reverse acc)]
      [(number? (first instr)) (instructhandle (rest instr) constantassoc memassoc (cons (first instr) acc))]
      [(list? (first instr)) (cond
                               [(equal? (length (first instr)) 1) (instructhandle (rest instr) constantassoc memassoc (cons (first instr) acc))]
                               [else (instructhandle (rest instr) constantassoc memassoc (cons (listhandle (first instr) constantassoc memassoc) acc))])]
      [else (let ((const (checker (first instr) constantassoc)))
              (let ((mem (checker (first instr) memassoc)))
                (cond
                  [(and (equal? const false)(equal? mem false)) (error "undefined")]
                  [(equal? const false) (instructhandle (rest instr) constantassoc memassoc (cons (list (second mem)) acc))]
                  [(equal? mem false) (instructhandle (rest instr) constantassoc memassoc (cons (second const) acc))])))]))

(define (listhandle lst constantassoc memassoc)
  (cond
    [(empty? lst) empty]
    [(number? (first lst)) (cond
                             [(number? (second lst)) lst]
                             [(list? (second lst)) lst]
                             [else (let ((mem (checker (second lst) memassoc)))
                                     (cond
                                       [(equal? mem false) (error "incorrect")]
                                       [else (list (first lst)(list (second mem)))]))])]
    [(symbol? (first lst)) (let ((mem (checker (first lst) memassoc)))
                             (let ((const (checker (first lst) constantassoc)))
                             (cond
                               [(and (equal? mem false) (equal? const false)) (error "incorrect")]
                               [(equal? mem false)
                                (cond
                                  [(or (number? (second lst))(list? (second lst))) (list (second const)(second lst))]
                                  [else (let ((mem2 (checker (second lst) memassoc)))
                                          (cond
                                            [(equal? mem2 false) (error "incorrect")]
                                            [else (list (second const)(list (second mem2)))]))])]
                               [(equal? const false)
                                (cond
                                  [(or (number? (second lst))(list? (second lst))) (list (second mem)(second lst))]
                                  [else (let ((mem2 (checker (second lst) memassoc)))
                                          (cond
                                            [(equal? mem2 false) (error "incorrect")]
                                            [else (list (second mem)(list (second mem2)))]))])])))]))
  
(define (inccheck instr constantassoc)
  (cond
    [(and (not (equal? (checker (second instr) constantassoc) false)) (not (or (equal? (first instr) 'jump)(equal? (first instr) 'branch)(equal? (first instr) 'print-val)(equal? (first instr) 'print-string)))) (error "incorrect")]
    [else false]))
                
    

;; symbolin? returns a boolean whether there exists symbol in the normal primp expression. If there are symbols that have been defined, replace them. else add them
;; as is to be resolved in a recursive call

;; compbool is a boolean telling us whether all symbols have been resolved
;; constantassoc is an assoc list of all constants
;; memassoc is an assoc list of all memory locations
;; source is  the input  and  target is the PRIMP output


(define (adder symbol val assoclst)
  (cons (list symbol val) assoclst))

(define (checker symbol assoclst)
  (assoc symbol assoclst))

