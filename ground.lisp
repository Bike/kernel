;;;; Definitions of Kernel primitives for the ground environment.
;;;; Also includes convenience functions and macros for writing primitives.
(in-package #:kernel)

(defun k-every (predicate list)
  "1-ary EVERY for Kernel lists.  Used primarily in the type checkers."
  (do ((list (decycle list) (k-cdr list)))
      ((not (typep list 'k-cons)) t)
    (unless (funcall predicate (k-car list))
      (return nil))))

(defun check-args (structure args)
  "Signal an error if args is not an acyclic Kernel list, with given args."
  (labels ((aux (args length)
	     (if (zerop length)
		 (unless (eq args %nil) (error 'kernel-too-many-arguments-passed))
		 (if (k-cons-p args)
		     (aux (k-cdr args) (1- length))
		     (error 'kernel-not-enough-arguments-passed)))))
    (handler-case (aux args (length structure))
      (kernel-too-many-arguments-passed () (error 'kernel-too-many-arguments-passed :ptree structure :otree args))
      (kernel-not-enough-arguments-passed () (error 'kernel-not-enough-arguments-passed :ptree structure :otree args)))))

(defpackage kernel-primitives
  (:nicknames :kp)
  (:use :kernel)
  (:import-from :cl :nil)
  (:shadow :cons :eval)
  (:export :boolean? :eq? :equal? :symbol? :$if :pair? :null? :cons
	   :set-car! :set-cdr! :copy-es-immutable :environment?
	   :inert? :make-environment :$define! :operative? :$vau
	   :applicative? :wrap :unwrap :call/cc :extend-continuation
	   :continuation->applicative :eval))

(define-kernel-primitive kp:boolean? nil (args environment continuation)
  "Returns #t if all of its arguments are booleans, and #f otherwise."
  (funcall continuation (k-every #'(lambda (x) (typep x 'boolean)) args)))

(define-kernel-primitive kp:eq? nil ((obj1 obj2) environment continuation)
  "Returns #t if its two arguments are eq as specified in 4.2.1, and #f otherwise."
  (let ((seen (list)))
    ;; A set of pairs of objects that have been seen together and which are thus considered eq?.
    ;; (lol cyclic structures amirite)
    (labels ((aux (obj1 obj2)
	       (if (and
		    (k-cons-p obj1)
		    (k-cons-immutable-p obj1)
		    (k-cons-p obj2)
		    (k-cons-immutable-p obj2))
		   (if (or (member (cons obj1 obj2) seen :test #'equal)
			   (member (cons obj2 obj1) seen :test #'equal))
		       t
		       (progn (push (cons obj1 obj2) seen)
			      (and (aux (k-car obj1) (k-car obj2))
				   (aux (k-cdr obj1) (k-cdr obj2)))))
		   (eq obj1 obj2))))
     (funcall continuation (aux obj1 obj2)))))

(define-kernel-primitive kp:equal? nil ((obj1 obj2) env cont)
  "Returns #t if just go read 4.3.1."
  ;; Probably going to have to fix this to deal with other types.
  ;; This works more or less the same as eq? up there.
  (let ((seen (list)))
    (labels ((aux (obj1 obj2)
	       (if (and (k-cons-p obj1) (k-cons-p obj2))
		   (if (or (member (cons obj1 obj2) seen :test #'equal)
			   (member (cons obj2 obj1) seen :test #'equal))
		       t
		       (progn (push (cons obj1 obj2) seen)
			      (and (aux (k-car obj1) (k-car obj2))
				   (aux (k-cdr obj1) (k-cdr obj2)))))
		   ;; Here's where fancier tests for other types whould go.
		   (eq obj1 obj2))))
      (funcall cont (aux obj1 obj2)))))

(define-kernel-primitive kp:symbol? nil (args env cont)
  "Returns #t if all of its arguments are Kernel symbols."
  (funcall cont (k-every #'(lambda (x) (typep x 'k-symbol)) args)))

(define-kernel-primitive kp:$if t ((antecedent consequent alternative) env cont)
  "Returns the evaluation of its second argument if its first evaluates to #t, its third if it's #f, and error otherwise."
  (interpret antecedent env
	     (lambda (result)
	       (case result
		 ((t) (interpret consequent env cont))
		 ((nil) (interpret alternative env cont))
		 (error "Antecedent of $if not a boolean: ~s" result)))))

(define-kernel-primitive kp:pair? nil (args env cont)
  "Returns #t if all of its arguments are Kernel pairs, #f otherwise."
  (funcall cont (k-every #'k-cons-p args)))

(define-kernel-primitive kp:null? nil (args env cont)
  "Returns #t if all of its arguments are Kernel (), #f otherwise."
  (funcall cont (k-every #'(lambda (x) (eq x %nil)) args)))

(define-kernel-primitive kp:cons nil ((obj1 obj2) env cont)
  ;; In case like I you thought "can't we just return the arglist"
  ;; the answer is "no", because
  ;; ($define! x (list 1 2))
  ;; ($define! oh-shi- (eval (cons cons x) (get-current-environment)))
  ;; (set-car! x 3)
  ;; oh-shi- must be a cons of 1 and 2 at this point.
  (funcall cont (k-cons obj1 obj2)))

(define-kernel-primitive kp:set-car! nil ((pair object) env cont)
  "Set the car of a Kernel pair, erring if it's not actually a mutable pair."
  (if (and (k-cons-p pair)
	   (not (k-cons-immutable-p pair)))
      (setf (k-car pair) object)
      (error "Tried to mutate non-mutable-pair ~a" pair))
  (funcall cont %inert))

(define-kernel-primitive kp:set-cdr! nil ((pair object) env cont)
  "Set the cdr of a Kernel pair, erring if it's not actually a mutable pair."
  (if (and (k-cons-p pair)
	   (not (k-cons-immutable-p pair)))
      (setf (k-cdr pair) object)
      (error "Tried to mutate non-mutable-pair ~a" pair))
  (funcall cont %inert))

(define-kernel-primitive kp:copy-es-immutable nil ((object) env cont)
  "If object isn't a pair, return it; otherwise, return an immutable pair equal? to it."
  (funcall cont (k-copy-immutable object)))

(define-kernel-primitive kp:environment? nil (args env cont)
  "Returns #t if all its arguments are Kernel pairs, and #f otherwise."
  (funcall cont (k-every #'k-environment-p args)))

(define-kernel-primitive kp:inert? nil (args env cont)
  "Returns #t if all its arguments are #inert, and #f otherwise."
  (funcall cont (k-every #'(lambda (x) (eq x %inert)) args)))

(define-kernel-primitive kp:eval nil ((expression environment) env cont)
  (interpret expression environment cont))

;;; This converts the possibly cyclic argument list to an acyclic CL list
;;; so that lookup can be slightly faster, not to mention easier to write.
;;; SIDENOTE: 4.8.4 specifies that if an environment's list of parents is cyclic,
;;; it will "still" check them all "at most once" - wouldn't "exactly once"
;;; or "at least once" (not that there's any reason to check more than once) make more sense?
(define-kernel-primitive kp:make-environment nil (args env cont)
  "Construct and return a new, empty environment, with the specified parent environments."
  (flet ((convert-arglist (k-list)
	   ;; Quick helper function to make a CL list out of an already decycled Kernel list.
	   ;; 3.2 says we have to preserve the order of the parents, keep in mind.
	   (do* ((cur k-list (k-cdr cur))
		 (ret (list))
		 (ret-end ret (cdr ret-end)))
		((eq cur %nil) ret)
	     (unless (k-cons-p cur) (error "Improper list passed to make-environment."))
	     (unless (k-environment-p (k-car cur)) (error "Non-environment in list passed to make-environment!"))
	     (setf (car ret-end) (k-car cur))
	     (setf (cdr ret-end) (list)))))
    ;; Seriously, indentation ech
    ;; Note that decycle will error if args isn't a Kernel list, but we'd do that anyway, so meh.
    (funcall cont (make-k-environment :parents (convert-arglist (decycle args)) :bindings nil))))

(define-kernel-primitive kp:$define! t ((definiend expression) env cont)
  "Bind definiend to (eval expression [the dynamic environment]) in the dynamic environment, then return #inert."
  ;; We're gonna pass off the (necessary) job of verifying that definiend is valid parameter tree
  ;; to some other function, in probably types.lisp.  Yay
  (vet-ptree definiend)
  (interpret expression
	     env
	     #'(lambda (expression)
		 (augment-environment definiend expression env)
		 (funcall cont %inert))))

(define-kernel-primitive kp:operative? nil (args env cont)
  "Return #t if all arguments are operatives, else #f."
  (funcall cont (k-every #'(lambda (x) (typep x 'k-operative)) args)))

(define-kernel-primitive kp:applicative? nil (args env cont)
  "Return #t if all arguments are applicatives, or otherwise #f."
  (funcall cont (k-every #'(lambda (x) (typep x 'k-applicative)) args)))

(define-kernel-primitive kp:$vau t ((formals (eformal (or k-symbol k-ignore)) expr) env cont)
  "Construct and return a new operative, in accordance with 4.10.3."
  (vet-ptree formals)
  (funcall cont
	   (make-instance 'k-operative-compound
			  :code (k-copy-immutable expr)
			  ;; "A stored copy of the formal parameter tree
			  ;; formals is matched in the local environment" - 4.10.3.2
			  ;; a bit ambiguous, but altering parameter trees is agh why.
			  :args (k-copy-immutable formals)
			  :envparam eformal
			  :env env)))

(define-kernel-primitive kp:wrap nil (((combiner k-combiner)) env cont)
  "Construct and return a new applicative around the provided operative."
  (funcall cont
	   (make-instance 'k-applicative-compound
			  :code combiner)))

(define-kernel-primitive kp:unwrap nil (((combiner k-applicative)) env cont)
  "Return the underlying combiner of combiner."
  ;; If said underlying combiner is a CL function, we have to fake it by making an operative.
  (funcall cont (if (functionp (combiner-code combiner))
		    (make-instance 'k-operative-primitive :code (combiner-code combiner))
		    (combiner-code combiner))))

;;; WARNING: HACKY AND BAD.  This is just so I can play around.
;;; Partly to unconfuse myself: Kernel continuations are NOT combiners.
(define-kernel-primitive kp:call/cc nil (((combiner k-combiner)) env cont)
  "Call the one argument with an object representing the current continuation of computation."
  (interpret (k-cons combiner (k-cons cont %nil))
	     env
	     cont))

(define-kernel-primitive kp:extend-continuation nil (args env cont)
  "Return a continuation that applies (unwrap applicative) to its argument, then passes that result to continuation."
  ;; I'm not 100% sure on what this thing does.
  (check-type args k-cons)
  (check-type (k-car args) function) ; should be continuation type (more specifically, a 3-ary function.)
  (check-type (k-cdr args) k-cons) ; this is stupid, but SAFETY!! (ololol.)
  (let ((continuation (k-car args)) (applicative (k-car (k-cdr args))) environment)
    (check-type applicative k-applicative)
    (etypecase (k-cdr (k-cdr args))
      (k-cons
       (setf environment (k-car (k-cdr (k-cdr args))))
       (check-type environment k-environment)
       (check-type (k-cdr (k-cdr (k-cdr args))) k-null))
      (k-null
       (setf environment (make-k-environment :bindings nil :parents nil))))
    ;; That was probably unnecessary.  Meh.
    (funcall cont #'(lambda (args env cont)
		      ;; I suppose you could call this on an applicative-fied continuation.
		      ;; *headsplode!*
		      (declare (ignore env cont))
		      (interpret (k-cons (combiner-code applicative) args)
				 environment
				 continuation)))))

(define-kernel-primitive kp:continuation->applicative nil (((continuation function)) env cont)
  "Return an applicative whose underlying operative abnormally passes its operand tree to continuation."
  (funcall cont
	   (make-instance 'k-applicative-compound
			  :code (make-instance 'k-operative-primitive
					       :code #'(lambda (a env cont)
							 (declare (ignore env cont))
							 (funcall continuation a))))))

;;;; Derived library begins here
#||
(define-kernel-primitive $sequence t (args env cont)
  (if (eq args %nil)
      ;; ($sequence) => #inert
      ;; Really, I should put the below in an auxiliary function to avoid pointless reevaluation of this,
      ;; but lazy
      (funcall cont %inert)
      (if (eq (k-cdr args) %nil)
	  ;; This is a $sequence of one statement, so we're done.
	  (interpret (k-car args) env cont)
	  ;; Otherwise, continuation mumbo-jumbo.
	  (interpret (k-car args) env
		     #'(lambda (res environ continuation)
			 (declare (ignore res environ continuation))
			 ($sequence (k-cdr args) env cont))))))

(push (cons 'list (make-instance 'k-applicative-primitive
				 :code #'(lambda (args env cont)
					   (declare (ignore env))
					   (funcall cont args)))))

(push (cons 'list* (make-instance 'k-applicative-primitive
				  :code #'(lambda (args env cont)
					    (declare (ignore env))
					    (labels ((aux (k-list)
						       (check-type k-list k-cons)
						       (if (eq (k-cdr k-list) %nil)
							   (k-car k-list)
							   (k-cons (k-car k-list) (aux (k-cdr k-list))))))
					      (funcall cont (aux args)))))))
||#