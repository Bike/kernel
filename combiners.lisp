;;;; Data types for combiners and environments for Kernel,
;;;; and some functions to operate on them.
(in-package #:kernel)

;;; Abstract parent class of all combiners.
(defclass k-combiner ()
  ;; code should be either a Kernel expression or a CL function of two args (see below)
  ((code :initarg :code :accessor combiner-code)))

;;; Abstract parent class of operatives.
(defclass k-operative (k-combiner) ())
;;; Abstract parent class of applicatives.
(defclass k-applicative (k-combiner) ())

;;; Class of compound, e.g. defined-in-Kernel operatives.
(defclass k-operative-compound (k-operative)
  ;; Argument list, a Kernel cons structure.  See $vau for detailed restrictions.
  ((arglist :initarg :args :accessor operative-arglist)
   ;; Environment arg, a Kernel symbol that is bound to the dynamic environment during execution.
   (envparam :initarg :envparam :accessor operative-envparam)
   ;; The static environment in which the operative was defined.
   (env :initarg :env :accessor operative-static-env)))

;;; Class of compound applicatives; dummy to be unwrapped.
(defclass k-applicative-compound (k-applicative) ())

;;; Now primitives.  Primitives should be CL functions of three arguments.
;;; The first argument is the entire operand tree, the second is the dynamic environment,
;;; and the third is the continuation to pass control to.
;;; Applicatives are passed the environment also.  They're free to ignore it.
;;; Ex. Kernel (cons 4 5) -> CL (funcall [fn] #k(4 5) env cont)
;;;     Kernel (apply boolean? 23) -> CL (funcall [fn] #k23 env cont)
;;;     Kernel ($let ((x (list 1 2 3))) (append! x x) (eval (cons + x) (get-current-environment)))
;;;     -> CL (funcall [fn] #1=#k(1 2 3 . #1#) env cont)
;;; etc.  (note that #k is a convenience of this note, and does not actually exist)
;;; Primitives are expected to do their own error/cycle/whatever the fuck handling.
(defclass k-applicative-primitive (k-applicative) ())
(defclass k-operative-primitive (k-operative) ())

;;; Environments are represented as a struct with two slots.
;;; "parents" is a Kernel list of environments (or Kernel nil)
;;; "bindings" is a CL alist of pairs (kernel_symbol . kernel_object)
;;; parents is a CL list of environments.  make-environment takes a
;;; possibly cyclic Kernel list, but installs in the environment
;;; an acyclic CL list; as far as I can tell, this is legal.
;;; (Note that 4.8.4 specifically says that the list of parents
;;;  is independent of the list passed to make-environment.)
(defstruct (k-environment (:print-function print-environment))
  parents
  bindings)

(defun print-environment (object stream depth)
  (declare (ignore depth))
  (print-unreadable-object (object stream :type t :identity t)))

;;; Parent of all Kernel conditions.
(define-condition kernel-condition (condition) ())

;;; Errors
(define-condition kernel-error (kernel-condition) ())

;;; This condition is signalled when an unbound variable is referenced in Kernel.
;;; TODO: Add report function.
(define-condition kernel-unbound-symbol (unbound-variable kernel-error) ((env :initarg :env :reader env)))

;;; This condition is signalled when an applicative is called with too many arguments.
;;; TODO: Add report function.
(define-condition kernel-too-many-arguments-passed (error kernel-error)
  ;; The parameter tree.
  ((ptree :initarg :ptree :reader ptree)
   ;; The Kernel list of arguments passed.
   (otree :initarg :otree :reader otree))
  (:report (lambda (condition stream)
	     (format stream "Too many arguments in ~s to match parameter list ~s" (otree condition) (ptree condition)))))

;;; This condition is signalled when an applicative isn't called with enough arguments.
;;; TODO: Blablabla, nobody likes writing error reporting code.
;;; And make this a subclass of something that too-many-args is?  meh
(define-condition kernel-not-enough-arguments-passed (error kernel-error)
  ((ptree :initarg :ptree :reader ptree)
   (otree :initarg :otree :reader otree))
  (:report (lambda (condition stream)
	     (format stream "Not enough arguments in ~s to match parameter list ~s" (otree condition) (ptree condition)))))

(defun lookup (ksym env)
  "Look up a Kernel symbol in a Kernel environment, returning its value, or signalling an error if it isn't bound."
  ;; As specified in the R-1SK, do a depth-first search of the parents.
  (let ((binding (assoc ksym (k-environment-bindings env))))
    (if binding
	(cdr binding)
	;; Not bound in this environment, so check the parents.
	(restart-case
	    (dolist (parent (k-environment-parents env) (error 'kernel-unbound-symbol :name ksym :env env))
	      (handler-case (lookup ksym parent)
		(kernel-unbound-symbol ())
		(:no-error (v) (return-from lookup v))))
	  (use-value (value)
	    :report "Specify a value to use this time."
	    value)
	  (store-value (value)
	    :report "Specify a value to store and use in the future."
	    (augment-environment ksym value env)
	    value)))))

(defun vet-ptree (parameter-tree)
  "Signal an error if parameter-tree is invalid.  See 4.9.1."
  (let ((seen nil))
    (labels ((aux (ptree)
	       (etypecase ptree
		 (k-symbol
		  (if (member ptree seen)
		      (error "~a is not a valid parameter tree: ~a is listed multiply." parameter-tree ptree)
		      (push ptree seen)))
		 (k-ignore)
		 (k-null)
		 (k-cons (aux (k-car ptree)) (aux (k-cdr ptree))))))
      (aux parameter-tree))))

(defun augment-environment (parameter-tree args env)
  "Mutate the provided environment so that the symbols in parameter-tree are bound to args."
  ;; The ptree is assumed to have been vetted as valid, probably by $vau (actually via vet-ptree, above).
  ;; If this is false, there will probably be weird errors.
  (progn
    ;; This function just dispatches on the argument type pretty much exactly as 4.9.1 says to.
    (etypecase parameter-tree
      ;; If it's a symbol, bind it.
      (k-symbol (push (cons parameter-tree args) (k-environment-bindings env)))
      ;; If it's %ignore, then ignore.
      (k-ignore)
      ;; If it's the end of the list, make sure it's supposed to be, then ignore.
      (k-null (unless (eq args %nil)
		;; Obvious problem: This does not report the offending function, etc.
		;; TODO: Make functions higher in the chain notice and report problem?
		(error 'kernel-too-many-arguments-passed :ptree parameter-tree :otree args)))
      ;; If it's a list, recurse.
      (k-cons
       ;; After making sure it's possible to, and erroring otherwise.
       (if (typep args 'k-cons)
	   (progn
	     (augment-environment (k-car parameter-tree) (k-car args) env)
	     (augment-environment (k-cdr parameter-tree) (k-cdr args) env))
	   (error 'kernel-not-enough-arguments-passed :ptree parameter-tree :otree args))))
    env))

(defvar *ground-environment* (make-k-environment :parents nil :bindings nil)
  "Ground environment for the Kernel interpreter, filled with R-1SK's functions.")

(defmacro k-destructuring-bind (list expression &body body)
  (let ((wholesym (gensym "WHOLE"))
	(checks nil)
	(bindings nil))
    (labels ((cons-aux (list path-so-far)
	       ;; doesn't work on circular lists, but this is in the CL bit, come on
	       (do ((n 0 (1+ n))
		    (path path-so-far `(k-cdr ,path))
		    (ptr list (cdr ptr)))
		   ((not (consp ptr))
		    (etypecase ptr
		      (null (push `(proper-k-list-of-length-or-error ',list ,path-so-far ,n) checks))
		      (symbol (push `(k-list-of-length-at-least-or-error ',list ,path-so-far ,n) checks)
			      (push (list ptr path) bindings))))
		 (etypecase (car ptr)
		   (symbol (push (list (car ptr) `(k-car ,path)) bindings))
		   (list (aux (car ptr) `(k-car ,path))))))
	     (aux (list path-so-far)
	       (etypecase list
		 (null)
		 (symbol (push (list list path-so-far) bindings))
		 (cons (cons-aux list path-so-far)))))
      (aux list wholesym)
      `(let ((,wholesym ,expression))
	 ,@checks
	 (let (,@bindings)
	   ,@body)))))

(defun proper-k-list-of-length-or-error (match k-list length)
  (multiple-value-bind (ignore acyclic cyclic) (decycle k-list)
    (declare (ignore ignore)) ; should use a nonconsing version instead
    (cond ((not (zerop cyclic))
	   (error 'kernel-too-many-arguments-passed :otree k-list :ptree match))
	  ((> acyclic length)
	   (error 'kernel-too-many-arguments-passed :otree k-list :ptree match))
	  ((< acyclic length)
	   (error 'kernel-not-enough-arguments-passed :otree k-list :ptree match)))))

(defun k-list-of-length-at-least-or-error (match k-list length)
  (do ((n 0 (1+ n))
       (ptr k-list (k-cdr ptr)))
      ((= length n))
    (when (not (k-cons-p ptr))
      (error 'kernel-not-enough-arguments-passed :otree k-list :ptree match))))

(defmacro define-kernel-primitive (name operative-p (args env cont) &body body)
  "Define a CL function as a Kernel primitive.  See comments on kernel-operative-primitive for calling convention."
  `(progn ,(if (symbolp args)
	       `(defun ,name (,args ,env ,cont)
		  (declare (ignorable ,env))
		  ,@body)
	       (let ((wholesym (gensym "WHOLE"))
		     (argtypes (mapcar (lambda (thing) (if (symbolp thing) t (second thing))) args))
		     (argnames (mapcar (lambda (thing) (if (symbolp thing) thing (first thing))) args)))
		 `(defun ,name (,wholesym ,env ,cont)
		    (declare (ignorable ,env)) ;; aw yeah
		    (k-destructuring-bind ,argnames ,wholesym
		      ,@(mapcar (lambda (name type) `(check-type ,name ,type)) argnames argtypes)
		      ,@body))))
	  (push (cons ',name
		      (make-instance ',(if operative-p 'k-operative-primitive 'k-applicative-primitive)
				     :code (function ,name)))
		(k-environment-bindings *ground-environment*))))

#||
(defmacro define-kernel-primitive (name operative-p (args env cont) &body body)
  "Define a CL function as a Kernel primitive.  See comments on kernel-operative-primitive for calling convention."
  ;; Do some shit with symbols here?  I do not understand packaging...
  `(progn (defun ,name (,args ,env ,cont) ,@body)
	  (push (cons ',name
		      (make-instance ',(if operative-p 'k-operative-primitive 'k-applicative-primitive)
				     :code (function ,name)))
		(k-environment-bindings *ground-environment*))))
||#