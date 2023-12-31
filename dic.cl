;;; -*- Mode: Lisp; Syntax: Common-Lisp;  -*-
;;; Code from Paradigms of Artificial Intelligence Programming
;;; Copyright (c) 1991 Peter Norvig

;;; krep1.lisp: Knowledge representation code; first version.

;;; This file is copied from http://www.norvig.com/ by Seiji Koide
;;; and modified for IPADIC dictionary loopup
;;; Copyright (c) 2007 Seiji Koide

(eval-when (:execute :load-toplevel :compile-toplevel)
(defpackage :ipadic 
  )
) ; end of eval-when

(in-package :ipadic)

;;;
;;; Followings are copied from Allegro Prolog origianal version.
;;;

(defun reuse-cons (x y x-y)
  "Return (cons x y), or reuse x-y if it is equal to (cons x y)"
  (if (and (eql x (car x-y)) (eql y (cdr x-y)))
      x-y
    (cons x y)))

(defun variable-p (x)
  "Is x a variable (a symbol beginning with `?')?"
  (and (symbolp x) (equal (char (symbol-name x) 0) #\?)))

(defconstant no-bindings '((t . t))
  "Indicates pat-match success, with no variables.")

(defconstant fail nil "Indicates pat-match failure")

(defparameter *occurs-check* t "Should we do the occurs check?")

(defmacro make-binding (var val) `(cons ,var ,val))

(defmacro extend-bindings (var val bindings)
  "Add a (var . value) pair to a binding list."
  (let ((b (gensym)))
    `(cons (make-binding ,var ,val)
	   ;; Once we add a "real" binding,
	   ;; we can get rid of the dummy no-bindings
	   (let ((,b ,bindings))
	     (if (and (eq ,b no-bindings))
		 nil
        ,b)))))

(defun subst-bindings (bindings x)
  "Substitute the value of variables in bindings into x,
  taking recursively bound variables into account."
  (cond ((eq bindings fail) fail)
        ((eq bindings no-bindings) x)
        ((and (variable-p x) (get-binding x bindings))
         (subst-bindings bindings (lookup x bindings)))
        ((atom x) x)
        (t (reuse-cons (subst-bindings bindings (car x))
                       (subst-bindings bindings (cdr x))
                       x))))

(defun unify (x y &optional (bindings no-bindings))
  "See if x and y match with given bindings."
  (cond ((eq bindings fail) fail)
        ((eql x y) bindings)
        ((variable-p x) (unify-variable x y bindings))
        ((variable-p y) (unify-variable y x bindings))
        ((and (consp x) (consp y))
         (unify (rest x) (rest y)
                (unify (first x) (first y) bindings)))
        (t fail)))

(defun lookup (var bindings)
  "Get the value part (for var) from a binding list."
  (binding-val (get-binding var bindings)))

(defun predicate (relation) (first relation))

(defun binding-val (binding)
  "Get the value part of a single binding."
  (cdr binding))

(defun unify-variable (var x bindings)
  "Unify var with x, using (and maybe extending) bindings."
  (cond ((get-binding var bindings)
         (unify (lookup var bindings) x bindings))
        ((and (variable-p x) (get-binding x bindings))
         (unify var (lookup x bindings) bindings))
        ((and *occurs-check* (occurs-check var x bindings))
         fail)
        (t (extend-bindings var x bindings))))

(defun get-binding (var bindings)
  "Find a (variable . value) pair in a binding list."
  (assoc var bindings))

(defun occurs-check (var x bindings)
  "Does var occur anywhere inside x?"
  (cond ((eq var x) t)
        ((and (variable-p x) (get-binding x bindings))
         (occurs-check var (lookup x bindings) bindings))
        ((consp x) (or (occurs-check var (first x) bindings)
                       (occurs-check var (rest x) bindings)))
        (t nil)))

(defun variables-in (exp)
  "Return a list of all the variables in EXP."
  (unique-find-anywhere-if #'non-anon-variable-p exp))

(defun non-anon-variable-p (x)
  (and (variable-p x) (not (eq x '?))))

(defun rename-variables (x)
  "replace all variables in x with new ones."
  (sublis (mapcar (lambda (var) (cons var (gensym (string var))))
                  (variables-in x))
          x))

(defun unique-find-anywhere-if (predicate tree
                                &optional found-so-far)
  "return a list of leaves of tree satisfying predicate, with duplicates removed."
  ;;(declare (notinline unique-find-anywhere-if))
  (if (atom tree)
      (if (funcall predicate tree)
          (adjoin tree found-so-far)
	found-so-far)
    ;; This special-case hack is to prevent this walker frmo seeing inside lisp forms
    ;; inside the lisp functor.
    (if (eq (car tree) 'prolog-symbol-macrolet)
	(loop for (nil binding) in (cadr tree)
	    do (setq found-so-far (unique-find-anywhere-if predicate binding found-so-far))
	    finally (return found-so-far))
      (if (eq (car tree) 'prolog-progn)
	  found-so-far
	(unique-find-anywhere-if
	 predicate
	 (first tree)
	 (unique-find-anywhere-if predicate (rest tree) found-so-far))))))

(defun find-anywhere-if (predicate tree)
  "does predicate apply to any atom in the tree?"
  (if (atom tree)
      (funcall predicate tree)
    (or (find-anywhere-if predicate (first tree))
	(find-anywhere-if predicate (rest tree)))))

(defmacro ?- (&rest goals) `(top-level-prove ',(replace-?-vars goals)))

;;; ==============================

;; An nlist is implemented as a (count . elements) pair:
(defun make-empty-nlist () 
  "Create a new, empty nlist."
  (cons 0 nil))

(defun nlist-n (x) "The number of elements in an nlist." (car x))
(defun nlist-list (x) "The elements in an nlist." (cdr x))

(defun nlist-push (item nlist)
  "Add a new element to an nlist."
  (incf (car nlist))
  (push item (cdr nlist))
  nlist)

;;; ==============================

(defstruct (dtree (:type vector))
  (first nil) (rest nil) (atoms nil) (var (make-empty-nlist)))

;;; ==============================

;; Not all Lisps handle the closure properly, so change the local PREDICATES
;; to a global *predicates* - norvig Jun 11 1996
(defvar *predicates* nil)

(defun get-dtree (predicate)
  "Fetch (or make) the dtree for this predicate."
  (cond ((get predicate 'dtree))
	(t (push predicate *predicates*)
	   (setf (get predicate 'dtree) (make-dtree)))))

(defun clear-dtrees ()
  "Remove all the dtrees for all the predicates."
  (dolist (predicate *predicates*)
    (setf (get predicate 'dtree) nil))
  (setf *predicates* nil))

;;; ==============================

(defun index (key)
  "Store key in a dtree node.  Key must be (predicate . args);
  it is stored in the predicate's dtree."
  (dtree-index key key (get-dtree (predicate key))))

(defun dtree-index (key value dtree)
  "Index value under all atoms of key in dtree."
  (format t "~%DTREE-INDEX ~S ~S ~S" key value dtree)
  (cond
    ((consp key)               ; index on both first and rest
     (dtree-index (first key) value
                  (or (dtree-first dtree)
                      (setf (dtree-first dtree) (make-dtree))))
     (dtree-index (rest key) value
                  (or (dtree-rest dtree)
                      (setf (dtree-rest dtree) (make-dtree)))))
    ((null key))               ; don't index on nil
    ((variable-p key)          ; index a variable
     (nlist-push value (dtree-var dtree)))
   (t ;; Make sure there is an nlist for this atom, and add to it
    (format t "~%NLIST-PUSH(~S ~S) ->" value (lookup-atom key dtree))
     (prin1 (nlist-push value (lookup-atom key dtree))))))

(defun lookup-atom (atom dtree)
  "Return (or create) the nlist for this atom in dtree."
  (or (lookup atom (dtree-atoms dtree))
      (let ((new (make-empty-nlist)))
        (push (cons atom new) (dtree-atoms dtree))
        new)))

;;; ==============================

(defun test-index ()
  (let ((props '((p a b) (p a c) (p a ?x) (p b c)
                 (p b (f c)) (p a (f . ?x)))))
    (clear-dtrees)
    (mapc #'index props)
    (write (list props (get-dtree 'p))
           :circle t :array t :pretty t)
    (values)))

;;; ==============================

(defun fetch (query)
  "Return a list of buckets potentially matching the query,
  which must be a relation of form (predicate . args)."
  (dtree-fetch query (get-dtree (predicate query))
               nil 0 nil most-positive-fixnum))

;;; ==============================

(defun dtree-fetch (pat dtree var-list-in var-n-in best-list best-n)
  "Return two values: a list-of-lists of possible matches to pat,
  and the number of elements in the list-of-lists."
  (if (or (null dtree) (null pat) (variable-p pat))
      (values best-list best-n)
      (let* ((var-nlist (dtree-var dtree))
             (var-n (+ var-n-in (nlist-n var-nlist)))
             (var-list (if (null (nlist-list var-nlist))
                           var-list-in
                           (cons (nlist-list var-nlist)
                                 var-list-in))))
        (cond
          ((>= var-n best-n) (values best-list best-n))
          ((atom pat) (dtree-atom-fetch pat dtree var-list var-n
                                        best-list best-n))
          (t (multiple-value-bind (list1 n1)
                 (dtree-fetch (first pat) (dtree-first dtree)
                              var-list var-n best-list best-n)
               (dtree-fetch (rest pat) (dtree-rest dtree)
                            var-list var-n list1 n1)))))))

(defun dtree-atom-fetch (atom dtree var-list var-n best-list best-n)
  "Return the answers indexed at this atom (along with the vars),
  or return the previous best answer, if it is better."
  (let ((atom-nlist (lookup atom (dtree-atoms dtree))))
    (cond
      ((or (null atom-nlist) (null (nlist-list atom-nlist)))
       (values var-list var-n))
      ((and atom-nlist (< (incf var-n (nlist-n atom-nlist)) best-n))
       (values (cons (nlist-list atom-nlist) var-list) var-n))
      (t (values best-list best-n)))))

;;; ==============================
(eval-when (:execute :load-toplevel :compile-toplevel)
(proclaim '(inline mapc-retrieve))
)
(defun mapc-retrieve (fn query)
  "For every fact that matches the query,
  apply the function to the binding list."
  (dolist (bucket (fetch query))
    (dolist (answer bucket)
      (let ((bindings (unify query answer)))
        (unless (eq bindings fail)
          (funcall fn bindings))))))

;;; ==============================

(defun retrieve (query)
  "Find all facts that match query.  Return a list of bindings."
  (let ((answers nil))
    (mapc-retrieve #'(lambda (bindings) (push bindings answers))
                   query)
    answers))

(defun retrieve-matches (query)
  "Find all facts that match query.
  Return a list of expressions that match the query."
  (mapcar #'(lambda (bindings) (subst-bindings bindings query))
          (retrieve query)))

;;; ==============================

(defmacro query-bind (variables query &body body)
  "Execute the body for each match to the query.
  Within the body, bind each variable."
  (let* ((bindings (gensym "BINDINGS"))
         (vars-and-vals
           (mapcar
             #'(lambda (var)
                 (list var `(subst-bindings ,bindings ',var)))
             variables)))
    `(mapc-retrieve
       #'(lambda (,bindings)
           (let ,vars-and-vals
             ,@body))
       ,query)))

;;; -*- Mode: Lisp; Syntax: Common-Lisp;  -*-
;;; Code from Paradigms of Artificial Intelligence Programming
;;; Copyright (c) 1991 Peter Norvig

;;; krep1.lisp: Knowledge representation code; second version.
;;; Fixes problem with renaming variables; adds conjunctions.

(defun index (key)
  "Store key in a dtree node.  Key must be (predicate . args);
  it is stored in the predicate's dtree."
  (dtree-index key (rename-variables key)    ; store unique vars
               (get-dtree (predicate key))))

