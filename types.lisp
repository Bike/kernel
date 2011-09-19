;;;; Basic stuff needed for Kernel, such as types and constants.
;;;; Also has k-list-handling functions.

(in-package #:kernel)

(defstruct (k-cons (:print-function print-k-cons)) immutable-p car cdr)
(defstruct (k-null (:print-function print-null)))
(defstruct (k-inert (:print-function print-inert)))
(defstruct (k-ignore (:print-function print-ignore)))

(defun print-null (obj stream depth)
  (declare (ignore obj depth))
  (format stream "~a" "()"))
(defun print-inert (obj stream depth)
  (declare (ignore obj depth))
  (format stream "~a" "#inert"))
(defun print-ignore (obj stream depth)
  (declare (ignore obj depth))
  (format stream "~a" "#ignore"))

(defvar %nil (make-k-null))
(defvar %inert (make-k-inert))
(defvar %ignore (make-k-ignore))

(deftype k-symbol () 'symbol)
(deftype k-boolean () 'boolean)

(defun k-cons (x y)
  (make-k-cons :immutable-p nil :car x :cdr y))

(defun k-car (obj)
  (if (k-cons-p obj) (k-cons-car obj) (error "Called k-car on a non k-cons object ~a." obj)))
(defun k-cdr (obj)
  (if (k-cons-p obj) (k-cons-cdr obj) (error "Called k-cdr on a non k-cons object ~a." obj)))

;;; Quick wrapper functions for Kernel conses to handle immutability.
(defun (setf k-car) (x pair)
  (if (k-cons-p pair)
      (if (k-cons-immutable-p pair)
	  (error "Called (setf k-car) on an immutable k-cons ~a." pair)
	  (setf (k-cons-car pair) x))
      (error "Called (setf k-car) on a non k-cons ~a." pair)))
(defun (setf k-cdr) (y pair)
  (if (k-cons-p pair)
      (if (k-cons-immutable-p pair)
	  (error "Called (setf k-cdr) on an immutable k-cons ~a." pair)
	  (setf (k-cons-cdr pair) y))
      (error "Called (setf k-cdr) on a non k-cons ~a." pair)))

(defun get-kernel-revisits (obj)
  "Return a list of all pairs in a Kernel list that are multiply reachable."
  (labels ((aux (revisits all &rest trees)
	     (if (null trees)
		 revisits
		 (let ((tree (first trees))
		       (trees (rest trees)))
		   (cond ((or (not (k-cons-p tree))
			      (member tree revisits :test #'eq))
			  (apply #'aux revisits all trees))
			 ((member tree all :test #'eq)
			  (apply #'aux (cons tree revisits) all trees))
			 (t
			  (apply #'aux revisits (cons tree all)
				 (k-car tree) (k-cdr tree) trees)))))))
    (aux nil nil obj)))

;;; TODO: Fix this up to work properly with printer dynamic variables, or don't, because who cares?
;;; Well actually, right now it fucks up if *print-circle* is non-nil.  So uh.
(defun print-k-cons (obj stream depth)
  "Print a Kernel list structure according to convention, along with a prepended #K to distinguish from CL lists."
  (declare (ignore depth))
  (let ((table (mapcar (let ((n 0)) #'(lambda (revisit) (list revisit (incf n) nil))) (get-kernel-revisits obj))))
    (labels ((write-visit (obj revisit)
	       ;; Write a "visit", e.g. a cycle marker of some form
	       (format stream "~a" "#")
	       (format stream "~d" (second revisit))
	       (if (third revisit)
		   ;; not our first time printing this object, so
		   (format stream "~a" "#")
		   ;; It is our first time, so do that #n=(bla bla bla) shit.
		   (progn
		     (setf (third revisit) t)
		     (format stream "~a" "=(")
		     ;; Now write the actual whatever it is.
		     (write-car (k-car obj))
		     (write-cdr (k-cdr obj))
		     ;; And then finish it up.
		     (format stream "~a" ")"))))
	     (write-cdr (obj)
	       ;; Write the cdr of an object.
	       (typecase obj
		 (k-null)
		 (k-cons
		  (let ((revisit (assoc obj table :test #'eq)))
		    (if revisit
			;; Whoop, self reference
			(progn
			  (format stream "~a" " . ")
			  (write-visit obj revisit))
			;; nope, just more list.
			(progn
			  (format stream "~c" #\Space)
			  (write-car (k-car obj))
			  (write-cdr (k-cdr obj))))))
		 (otherwise
		  (format stream "~a" " . ")
		  (write obj :stream stream))))
	     (write-car (obj)
	       (if (k-cons-p obj)
		   (let ((revisit (assoc obj table :test #'eq)))
		     (if revisit
			 (write-visit obj revisit)
			 (progn
			   (format stream "~a" "(")
			   (write-car (k-car obj))
			   (write-cdr (k-cdr obj))
			   (format stream "~a" ")"))))
		   (write obj :stream stream))))
      (write-car obj))))

(defun decycle (k-list)
  "Return a copy of its Kernel list argument from which any primary (e.g. not following cars) cycle is removed.
  Also returns, in secondary and tertiary values respectively, the acyclic prefix length, and cycle length."
  (when (k-null-p k-list) (return-from decycle (values %nil 0 0)))
  (check-type k-list k-cons)
  (let* ((result (k-cons (k-car k-list) %nil)) (result-end result))
    (labels ((aux (kth k nth n)
	       ;; Copied and modified from 5.7.1's library derivation of get-list-metrics.
	       ;; k loops from 0 to n then resets to 0, while n either increments or stays the same.
	       ;; kth is the kth pair, nth is the nth.
	       (if (>= k n)
		   ;; if > k n, it's time to reset k to 0 - unless nth's hit the end,
		   ;; in which case we're done.
		   (if (k-cons-p (k-cdr nth))
		       (progn
			 ;; We've got more, so just add to the result list and recurse.
			 (setf (k-cdr result-end) (k-cons (k-car (k-cdr nth)) %nil))
			 (setf result-end (k-cdr result-end))
			 (aux k-list 0 (k-cdr nth) (1+ n)))
		       (progn
			 ;; We're out of conses, so we're done, and the list is acyclic
			 ;; with length n + 1.
			 (setf (k-cdr result-end) (k-cdr nth))
			 (values result (1+ n) 0)))
		   (if (eq kth nth)
		       ;; Hey, a cycle.  Acycle = k, cycle = n-k.
		       ;; The result list is already nil-capped, so just return the values.
		       (values result k (- n k))
		       ;; k isn't > n, and there's no cycle, so just continue.
		       (aux (k-cdr kth) (1+ k) nth n)))))
      ;; Seriously, indentation of these things is so bothersome.
      (aux k-list 0 k-list 0))))

(defun k-copy-immutable (obj)
  "If object isn't a pair, return it; otherwise, return an immutable pair Kernel-equal? to it."
  (let ((seen nil))
    ;; Bla bla bla standard operating procedure for cycleshit.
    (labels ((aux (obj)
	       (if (or (not (k-cons-p obj)) (k-cons-immutable-p obj))
		   ;; Immutable pairs can't point to mutable pairs, so anything immutable
		   ;; pointed to by mutable pairs should be "self-contained" and thus safe to not copy.
		   obj
		   (let ((previous (assoc obj seen)))
		     (if previous
			 ;; We've seen this pair before, so just return whatever we constructed then.
			 (cdr previous)
			 ;; Otherwise, we have to construct a new immutable pair, and put it in seen.
			 (let ((new (make-k-cons :immutable-p t :car nil :cdr nil)))
			   (push (cons obj new) seen)
			   ;; Now we can recurse safe from cycles.  I think.
			   ;; Note that the usual (setf k-cXr) is not used, since it's immutable.
			   (setf (k-cons-car new) (aux (k-car obj)))
			   (setf (k-cons-cdr new) (aux (k-cdr obj)))
			   new))))))
      ;; There's the helper function; call it.
      (aux obj))))