(in-package #:kernel)

;;;; Interpreter for a bootstrap implementation of the Kernel language.

(deftype k-object () '(or k-symbol k-cons k-ignore k-inert k-null k-environment k-combiner function))

(defun interpreter ()
  "Interface to the Kernel interpreter."
  (let ((working-environment (make-k-environment :parents (list *ground-environment*)))
	(*package* (find-package 'kernel)))
    (loop
       (format t "~&kernel> ")
       (let ((sexp (cl->kernel (read))))
	 (fresh-line)
	 (interpret sexp working-environment #'princ)))))

(defun cl->kernel (obj)
  "Convert a CL structure to a Kernel list.  Signals an error on unknown types.  Does not halt on cyclic lists."
  (etypecase obj
    (cons (k-cons (cl->kernel (car obj)) (cl->kernel (cdr obj))))
    (null %nil)
    (symbol
     (case obj
       ;; Some constant symbols.
       ;; At least for now, %t is CL:t, %f is CL:nil,
       ;; and the others are unforgeable constants, namely, instances of unique structs
       ;; (see types.lisp)
       (%t t)
       (%f nil)
       (%inert %inert)
       (%ignore %ignore)
       ;; And the most important step...
       (otherwise obj)))))

(defun interpret (expression environment continuation)
  "Interpret a Kernel list in a Kernel environment and pass the result to cont, a CL function."
  (etypecase expression
    (k-boolean (funcall continuation expression))
    (k-symbol (funcall continuation (lookup expression environment)))
    (k-cons (interp-call expression environment continuation))
    (k-object (funcall continuation expression))))

(defun interp-call (call env cont)
  "Interpret a Kernel call in env, passing its result to cont."
  ;; This function is somewhat confusing in CPS, so hang on.
  ;; First we evaluate the car (e.g. the function position) in env, and pass that
  ;; to a continuation.
  (interpret (k-car call) env
	     #'(lambda (combiner)
		 ;; This continuation works out what to do based on the combiner's type.
		 (etypecase combiner
		   (k-operative-compound
		    ;; If it's a compound operative (e.g., it was ($vau ...) at some point)
		    ;; then we're "done"; evaluate its code in an environment augmented
		    ;; with the arguments, passing the result to the continuation.
		    (interpret (combiner-code combiner)
			       (augment-environment
				(k-cons (operative-envparam combiner) (operative-arglist combiner))
				(k-cons env (k-cdr call))
				(make-k-environment :parents (list (operative-static-env combiner)) :bindings nil))
			       cont))
		   (k-operative-primitive
		    ;; If it's a primitive operative, call it on the operand tree with the environment and continuation.
		    (funcall (combiner-code combiner) (k-cdr call) env cont))
		   (k-applicative
		    ;; Sanity check that it's an applicative; if it's not, etypecase signals
		    ;; an error.  Hm, why am I going through the effort of error signalling?
		    ;; This is just supposed to make a self-hosting implementation possible...
		    ;; </muse>
		    ;; So anyway, it's an applicative of some sort, so evaluate the arguments
		    ;; and pass them to a specifically constructed continuation.
		    ;; We have to go deeper and all.
		    (map-interp (k-cdr call)
				env
				(if (typep combiner 'k-applicative-compound)
				    ;; If it's a compound applicative, the receiving continuation
				    ;; simply evaluates (in Kernel terms)
				    ;; (cons (unwrap combiner) args)
				    ;; in the given environment, with the continuation of the whole call.
				    #'(lambda (args)
					(interpret (k-cons (combiner-code combiner) args)
						   env
						   cont))
				    ;; If it's primitive, call the continuation on its result on
				    ;; the args and the environment.
				    ;; Primitive applicatives get a copy of the environment too.
				    ;; Perhaps I'm too generous.  But they can just (declare ignore env).
				    #'(lambda (args)
					(funcall (combiner-code combiner) args env cont)))))))))

(defun map-interp (exps env cont)
  "Evaluate exps as Kernel expressions from left to right in env and pass the Kernel list of them to cont."
  ;; exps may be cyclic, so we have to be a bit tricky.
  (multiple-value-bind (exps mu lambda) (decycle exps)
    ;; decycle returns the length of the acyclic prefix (mu)
    ;; and cycle (lambda) so that we can return a cyclic
    ;; structure if one was passed.
    (labels ((helper (expressions cont)
	       ;; Helper to actually do the evaluating,
	       ;; so we can avoid doing (comparatively expensive)
	       ;; cycle-handling BS more than once.
	       ;; It's still continuation-passing, though.  Hi confusion!
	       (if (eq expressions %nil)
		   ;; If we're out of expressions, we're done; "return" Kernel nil.
		   (funcall cont %nil)
		   ;; If not, interpret the first expression...
		   (interpret (k-car expressions) env
			      ;; ...passing the result to a continuation, which...
			      #'(lambda (x)
				  ;; ...recursively calls helper, continuating to...
				  (helper (k-cdr expressions)
					  #'(lambda (y)
					      ;; ...a regular goddamn cons.
					      (funcall cont (k-cons x y)))))))))
      ;; Well, that was a mouthful.
      ;; Now just call the helper function with a continuation that returns
      ;; a structure of the same shape.  And by "return" I mean "more CPS bullshit";
      ;; there has got to be a better way to write in this style.
      (helper exps
	      (if (zerop lambda)
		  ;; If there's no cycle, fuck this shit.
		  cont
		  ;; Welp.
		  #'(lambda (list)
		      ;; Traverse to the (mu)th cons of the return value,
		      ;; remember what it is, then keep going to the
		      ;; (mu + lambda - 1)th, and set its cdr to that.
		      (do ((pos 0 (1+ pos))
			   (cur list (k-cdr cur))
			   (cycle-start nil))
			  ((= pos (+ mu lambda -1))
			   (setf (k-cdr cur) cycle-start)
			   (funcall cont list))
			(when (= pos mu) (setf cycle-start cur)))))))))