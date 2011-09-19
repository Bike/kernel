;;;; Functions for converting Kernel expressions into pseudo-assembly, hopefully.

(in-package #:kernel)

;;; Compiler is "data driven", in SICP terms, since none of the symbols in Kernel
;;; are guaranteed to have the same value in different contexts.

(defvar *compiler-ground*
  '(($if compile-if)
    ($define! compile-define)
    ($vau compile-vau))
  "Alist mapping Kernel symbols in the base library to functions to compile them.")

;;; Hacky function, should be elsewhere, and have more error handling bullshit.

(defun k-nth (n kl) (if (= n 0) (k-car kl) (k-nth (1- n) (k-cdr kl))))

(defun compile-sequence (k-list)
  (let ((listing nil) (comp-env (copy-list *compiler-ground*)))
    ;; listing is the end assembly.  comp-env is the compiler's "dynamic environment",
    ;; and is a copy because Kernel code may redefine symbols.
    (do* ((pair k-list (k-cdr pair))
	  (expr (k-car pair) (k-car pair)))
	 ((eq k-list %nil) listing)
      (setf listing (append listing (compile-expression expr comp-env))))))

(defun compile-expression (k-list comp-env)
  (typecase (k-car k-list)
    (k-symbol
     (let ((compiler (assoc (k-car k-list) comp-env)))
       (if compiler
	   (funcall (cdr compiler) (k-cdr k-list))
	   ;; shit error handling, for this hack
	   (error "In ~a, could not locate binding for ~a." k-list (k-car k-list)))))
    (k-cons
     ;; 3.3.3: The combiner is evaluated before its arguments.
     (let ((combiner (gensym)))
       (append (compile-combiner (k-car k-list) comp-env combiner)
	       ;; for future reference, arguments are: the defining expression,
	       ;; the compilation environment, and the name of the function
	       ;; (anonymous here, obviously).  Picked up the idea from Lisp 1.5.
	       ;;  In general, we can't know whether the combiner
	       ;;  is an applicative or operative, so we have to assume operative
	       ;;  and call eval a whole fucking lot (barring extensive analysis).
	       ;;  Sucks.
	       (let ((args nil))
		 (do ((pair k-list (k-cdr pair))
		      (expr (k-car pair) (k-car pair)))
		     ((eq %nil expr) args)
		   (setf args (append args (compile-expression expr comp-env) (list (list :push 
       ;; tired, not sure how to do stack whatever