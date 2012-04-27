;;;; System definition for Kernel.

(asdf:defsystem :kernel
  :serial t
  :depends-on (#:string-case)
  :version "0.1"
  :components ((:file "package")
	       (:file "types")
	       (:file "combiners")
	       (:file "interpreter")
	       (:file "ground")))