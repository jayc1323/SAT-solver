;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Homework 5 : Continuations 

;;;Problem 2
;;;
;;; (list-of? A? v) takes two arguments - A? ,which is a predicate that can be
;;                  applied to any value and v, which is an arbitrary uScheme 
;;                  value. Returns true if v is a list of values where each
;;                  value satisfies the predicate A? , else returns false.
;; laws:
;; (list-of? A? '()) == #t 
;; (list-of? A? (cons x xs)) ==  (and (A? x) (list-of? A? xs))
;; (list-of? A? v) == #f ,where (not (pair? v)) and (not (= v '()))

(define list-of?(A? v)
    (if (equal? v '())
        #t
        (if (pair? v)
            (and (A? (car v)) (list-of? A? (cdr v)))
            #f)))

        ;;Tests
        (check-assert (list-of? symbol? '(a b c d e))) 
        (check-assert (not (list-of? symbol? '(a 3 c d e))))  
        (check-assert (not (list-of? symbol? '(a (1 2 3) c d e))))     
        (check-assert (list-of? symbol? '())) 
        (check-assert (list-of? function? (list3 symbol? atom? pair?))) 
        (check-assert (not (list-of? function? (list3 symbol? 23 pair?)))) 
        (check-assert (list-of? atom? '(a 23 #t d e))) 
        (check-assert (not(list-of? atom? '(a (1 2 4) #t d e)))) 
        ;; Input is a pair but not a list
        (check-assert (not (list-of? symbol? (cons 'not (cons 'a 'list))))) 
        ;;Predicate returns true for every value
        (check-assert (list-of? (lambda(x)#t) '(a 23 #t (1 2) e))) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Problem 3

(record not [arg])
(record or  [args])
(record and [args])

;;;(formula? f), which when given an arbitrary μScheme value, returns #t if 
;;;             the value represents a Boolean formula and #f otherwise. 
;;;laws:
;;;(formula? x) == #t , where (symbol? x)
;;;(formula? (make-not arg)) == (formula? arg)
;;;(formula? (make-or args)) == (list-of? formula? args)
;;;(formula? (make-and args)) == (list-of? formula? args)
;;;(formula? v) == #f,where (and (and (not(not? v)) (not (or? v))) 
;;;                                     (not(and? v)))

(define formula?(f)
        (if (symbol? f)
             #t
             (if (not? f)
                  (formula? (not-arg f))
                  (if (or? f)
                       (list-of? formula? (or-args f))
                       (if (and? f)
                            (list-of? formula? (and-args f))
                             #f)))))

;;Tests
        ;;test valid symbol input
        (check-assert (formula? 'sat)) 
        ;;test invalid input, should be a symbol
        (check-assert (not (formula? '(1 2 3))))
        ;;test valid make-not record
        (check-assert (formula? (make-not 'abc)))
        ;;test invalid make-not record , arg not a formula
        (check-assert (not (formula? (make-not '(1 2)))))
        ;;test invalid make-or , args not a list
        (check-assert (not (formula? (make-or 'abc))))
        ;;test valid make-or ,args is a list containing a valid make-not
        (check-assert (formula? (make-or (list2 'bool (make-not 'asd)))))
        ;;test valid make-and record, containing a list of valid formulas
        (check-assert (formula? (make-and 
                                 (list2 'b (make-or (list2 'bool 
                                                     (make-not 'asd)))))))

                                                   
    (check-assert (not (formula? (make-and 
                                  (cons 'b (make-or (list2 'bool 
                                                     (make-not 'asd))))))))  
    ;;test invalid make-and record,args is a list but one of its elements is 
    ;; an invalid make-or record
    (check-assert (not (formula? (make-and 
                                  (list2 'b 
                                   (make-or (list2 'bool 
                                             (make-not '()))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Problem 4

;;(eval-formula f env) takes a formula f and an environment env which is
;; an association list of key-value pairs of symbols to booleans. Returns
;; true if the formula is satisfied in the given env,else returns false.
;; (eval-formula f env) may be called only when every
;; Boolean variable in formula f is bound in env.

;;laws:
;;(eval-formula f env) == (find f env),where (symbol? f)
;;(eval-formula (make-not f1) env) == (not (eval-formula f1 env))
;;(eval-formula (make-or '()) env) == #f
;;(eval-formula (make-or (cons f fs)) env) == (or (eval-formula f env)  
;;                                (eval-formula (make-or fs) env))
;;(eval-formula (make-and '()) env) == #t
;;(eval-formula (make-and (cons y ys)) env) == (and (eval-formula y env)  
;;                                (eval-formula (make-or ys) env))
         
(define eval-formula(f env)
        (if (symbol? f)
            (find f env)
            (if (not? f)
                (not (eval-formula (not-arg f) env))
                 (if (or? f)
                     (if (null? (or-args f))
                         #f
                         (or (eval-formula  (car (or-args f)) env)
                             (eval-formula (make-or (cdr (or-args f))) env)))
                     (if (null? (and-args f))
                         #t
                         (and (eval-formula (car (and-args f)) env)
                             (eval-formula 
                              (make-and (cdr (and-args f))) env)))))))  

 ;; Tests
 ;; 1 - Formula is a symbol 
 (check-assert (eval-formula 'a '((a #t) (b #f))))
 ;; 2 - Formula is a record of type not
 (check-assert (eval-formula (make-not 'b) '((a #t) (b #f))))
 ;; 3 - Formula is a record of type or
 (check-assert (not (eval-formula (make-or '()) '((a #t) (b #f)))))
 ;; 4 - Formula is a record of type or
 (check-assert (eval-formula (make-or '(a b)) '((a #t) (b #f))))
  ;; 5 - Formula is a record of type or
 (check-assert (not (eval-formula (make-or '(a b)) '((a #f) (b #f)))))
  ;; 6 - Formula is a record of type and
 (check-assert (eval-formula (make-and '()) '((a #t) (b #f))))
 ;; 7 - Formula is a record of type and
 (check-assert (not (eval-formula (make-and '(a b)) '((a #t) (b #f)))))
  ;; 8 - Formula is a record of type and
 (check-assert (eval-formula (make-and '(a b)) '((a #t) (b #t))))

 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 ;;Problem 5

  
;; (solve-sat f fail succ) takes three parameters: a formula f, 
;;  a failure continuation fail, and a success continuation succ. It searches
;;  for an assignment that satisfies formula f. If it finds a satisfying 
;;  assignment env (an association list),it calls (succ env resume) 
;;  with a satisfying assignment env and a resume continuation 
;;  resume (which does not take any arguments). 
;;  Otherwise, it calls (fail) with no arguments. 

;; laws for sat-solve
;; (solve-sat f fail succ) == (solve-formula f #t '() fail succ)

(define solve-sat(f fail succ)
  (letrec
   (

;;(solve-formula f bool cur fail succeed) extends assignment cur to find an 
;;                        assignment that makes the single f equal to bool.
;;laws:
;;(solve-formula x bool cur fail succeed) == 
;;           (solve-symbol x bool cur fail succeed) , where x is a symbol

;;(solve-formula (make-not f)  bool cur fail succeed) == 
;;                      (solve-formula  f  (not bool) cur fail succeed)     

;;(solve-formula (make-or  fs) #t   cur fail succeed) == 
;;                           (solve-any fs #t cur fail succeed)

;;(solve-formula (make-or  fs) #f   cur fail succeed) == 
;;                           (solve-all fs #f cur fail succeed)   

;;(solve-formula (make-and fs) #t   cur fail succeed) == 
;;                        (solve-all fs #t cur fail succeed) 

;;(solve-formula (make-and fs) #f   cur fail succeed) == 
;;                           (solve-any fs #f cur fail succeed)   


    [solve-formula 
     (lambda(f bool cur fail succeed)
      (if (symbol? f)
          (solve-symbol f bool cur fail succeed)
          (if (not? f)
              (solve-formula  (not-arg f)  (not bool) cur fail succeed)
              (if (or? f)
                  (if (= bool #t)
                      (solve-any (or-args f) #t cur fail succeed)
                      (solve-all (or-args f) #f cur fail succeed))
                  (if (= bool #t)
                      (solve-all (and-args f) #t cur fail succeed)
                      (solve-any (and-args f) #f cur fail succeed))))))]

;-------------------------------------------------------------------------
;;(solve-any fs bool cur fail succeed) extends cur to find an assignment that
;;                                      makes any one of the fs equal to bool
;;laws:
;;(solve-any '() bool cur fail succeed) == (fail)

;;(solve-any (cons f fs) bool cur fail succeed) == 
;;  (solve-formula f bool cur 
;;     (lambda()(solve-any fs bool cur fail succeed)) succeed)

     [solve-any 
      (lambda(fs bool cur fail succeed)
        
            (if (null? fs)
                (fail)
                (solve-formula (car fs) bool cur 
                 (lambda()(solve-any (cdr fs) bool cur fail succeed)) 
                   succeed)))]

;--------------------------------------------------------------------------
;;(solve-all fs bool cur fail succeed) extends cur to find an assignment that
;;                           makes every formula in the list fs equal to bool
;;laws:
;;(solve-all '() bool cur fail succeed) == (succeed cur fail)

;;(solve-all (cons f fs) bool cur fail succeed) == 
;;  (solve-formula f bool cur fail 
;;     (lambda(cur' fail)(solve-all fs bool cur' fail succeed)))

     [solve-all 
      (lambda(fs bool cur fail succeed)
        
            (if (null? fs)
                (succeed cur fail)
                (solve-formula (car fs) bool cur fail 
                 (lambda(cur' resume)
                  (solve-all (cdr fs) bool cur' resume succeed)))))]

;------------------------------------------------------------------------
;;solve-symbol x bool cur fail succeed), where x is a symbol, 
;;                                  does one of three things:

;;1) If x is bound to bool in cur, succeeds with environment 
;;                       cur and resume continuation fail

;;2) If x is bound to (not bool) in cur, fails

;;3) If x is not bound in cur, extends cur with a binding of x to bool, 
;;then succeeds with the extended environment and continuation fail

;;laws:
;;(solve-symbol x bool cur fail succeed) == (succeed cur{x->bool} fail)
;;                                         , where x is not bound in cur

;;(solve-symbol x bool cur fail succeed) == (succeed cur fail),
;;                                           where x is bool in cur

;;(solve-symbol x bool cur fail succeed) == (fail), 
;;                                          where x is (not bool) in cur

     [solve-symbol 
      (lambda(x bool cur fail succeed)
                   (let([value (find x cur)])
       
                      (if (equal? value '())
                          (succeed (bind x bool cur) fail)
                          (if (= value bool)
                              (succeed cur fail)
                              (fail)))))])

;;---------------------------------------------------------------------- 
;; letrec body

    (solve-formula f #t '() fail succ)))

;;---------------------------------------------------------------------

;;tests -PROVIDED
    (check-assert (function? solve-sat))    ; correct name
    (check-error (solve-sat))                ; not 0 arguments
    (check-error (solve-sat 'x))             ; not 1 argument
    (check-error (solve-sat 'x (lambda () 'fail)))   ; not 2 args
    (check-error
     (solve-sat 'x (lambda () 'fail) (lambda (c r) 'succeed) 'z));not 4 args

    (check-error (solve-sat 'x (lambda () 'fail) (lambda () 'succeed)))
        ; success continuation expects 2 arguments, not 0
    (check-error (solve-sat 'x (lambda () 'fail) (lambda (_) 'succeed)))
        ; success continuation expects 2 arguments, not 1
    (check-error (solve-sat
                       (make-and (list2 'x (make-not 'x)))
                       (lambda (_) 'fail)
                       (lambda (_) 'succeed)))
        ; failure continuation expects 0 arguments, not 1


    (check-expect   ; x can be solved
       (solve-sat 'x
                  (lambda () 'fail)
                  (lambda (cur resume) 'succeed))
       'succeed)

    (check-expect   ; x is solved by '((x #t))
       (solve-sat 'x
                  (lambda () 'fail)
                  (lambda (cur resume) (find 'x cur)))
       #t)

    (check-expect   ; (make-not 'x) can be solved
       (solve-sat (make-not 'x)
                  (lambda () 'fail)
                  (lambda (cur resume) 'succeed))
       'succeed)

    (check-expect   ; (make-not 'x) is solved by '((x #f))
       (solve-sat (make-not 'x)
                  (lambda () 'fail)
                  (lambda (cur resume) (find 'x cur)))
       #f)

    (check-expect   ; (make-and (list2 'x (make-not 'x))) cannot be solved
       (solve-sat (make-and (list2 'x (make-not 'x)))
                  (lambda () 'fail)
                  (lambda (cur resume) 'succeed))
       'fail)
    ;;---------------------------------------------------------------------
    ;;TEST CASES sat-solver
    ;; using eval-formula 
   
    ;;TEST 1    
    ;;(A or B)- Solvable , so eval-formula should be satisfied in
    ;; the environment produced by solve-sat 
    (val f1 (make-or '(a b)))
    (check-assert(eval-formula f1 
                  (solve-sat f1 (lambda()'No_solution) 
                     (lambda(cur resume)cur))))


    ;;;---------------------------------------------------------
     ;;TEST 2
    ;;(A or B) and (not A or C )-Solvable
    (val f2 
       (make-and (list2 (make-or '(a b)) 
                  (make-or (list2 (make-not 'a) 'c)))))
    (check-assert (eval-formula f2 
                    (solve-sat f2 (lambda()'No_solution) 
                        (lambda(cur resume)cur))))
    
    ;;---------------------------------------------------------
     ;;TEST 3
    ;; (A and not A) - not solvable
    (val f3 (make-and (list2 'a (make-not 'a))))
    (check-expect (solve-sat f3 (lambda()'No_solution) 
                        (lambda(cur resume)cur)) 'No_solution)

    ;;---------------------------------------------------------
     ;;TEST 4  
    ;;( A and B and C)- solvable
    (val f4 (make-and (list3 'a 'b 'c)))
    (check-assert (eval-formula f4 
                    (solve-sat f4 (lambda()'No_solution) 
                        (lambda(cur resume)cur))))
    
    ;;---------------------------------------------------------
     ;;TEST 5
    ;;(A ∨ B) ∧ (¬A) ∧ (¬B) -> Unsolvable
     (val f5 (make-and (list3 (make-or (list2 'a 'b)) 
                                (make-not 'a) 
                                (make-not 'b))))
    (check-expect (solve-sat f5 (lambda()'No_solution) 
                        (lambda(cur resume)cur)) 'No_solution)
    

    ;;---------------------------------------------------------
     ;;TEST 6  
    ;;(A OR B)
    ;;(B OR C OR D)
    ;;(NOT A OR NOT D)
    ;;(C OR D)  -> Solvable 
    (val f6 
     (make-and 
      (list4 
       (make-or (list2 'a 'b))
       (make-or (list3 'b 'c 'd))
       (make-or (list2 (make-not 'a) (make-not 'd)))
       (make-or (list2 'c 'd)))))
    (check-assert (eval-formula f6 (solve-sat f6 (lambda()'No_solution) 
                                                    (lambda(cur resume)cur))))
    

    ;;---------------------------------------------------------------
     ;;TEST 7
    ;; (A or B )
    ;; and (C and notA ) solvable
     (val f7 
      (make-and 
       (list2 
         (make-or (list2 'a 'b) )
         (make-and (list2 'c (make-not 'a))))))
    (check-assert (eval-formula f7 (solve-sat f7 (lambda()'No_solution) 
                                                    (lambda(cur resume)cur))))
   


    ;;;;;;;;;;;;;;;;;;;;;;;;end;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;