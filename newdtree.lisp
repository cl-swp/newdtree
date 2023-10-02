;;;-*- Mode: common-lisp; syntax: common-lisp; package: ndtree; base: 10 -*-
;;; ==================================================================================
;;;; New Dtree
;;;
;;; This module is extended version of original dtree, which is published at PAIP.
;;; This code is modified by Seiji Koide starting with the original one in 
;;; http://www.norvig.com/ for the usage of Semantic Web and LOD Linguistics
;;; Copyright (c) 2017 Seiji Koide
;;; ==================================================================================

;;; krep1.lisp: Knowledge representation code; second version.
;;; Fixes problem with renaming variables; adds conjunctions.

(cl:provide :ndtree)

(setq *features* (pushnew :ndtree *features*))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (require :utils)
  (require :iri)
  )
(defpackage :ndtree 
  (:nicknames :ndt)
  (:use :common-lisp :utils)
  (:export #:mklist #:arg-rest #:length=1 #:op #:make-exp
           #:+no-bindings+ #:+fail+ #:unify #:lookup #:args
           #:dtree-atoms #:dtree-atoms #:dtree-var #:variable?
           #:make-dtree #:dtree-first #:dtree-rest #:dtree-index #:get-dtree #:predicate
           #:index #:fetch #:subst-bindings #:retrieve #:add-fact #:retrieve-fact #:retrieve-setof
           #:extend-bindings #:get-binding #:new-variable #:rename-variables
           #:delete-index #:dtree-fetch #:clear-dtrees #:index-delete
           #:*predicates*))
(in-package :ndt)

;;;
;;; Followings are copied from the origianal version of Allegro Prolog.
;;;

(#+:allegro defconstant #+:sbcl defparameter +no-bindings+ '((t . t))
  "Indicates pat-match success, with no variables.")

(#+:allegro defconstant #+:sbcl defparameter  +fail+ nil "Indicates pat-match failure")

(defparameter *occurs-check* t "Should we do the occurs check?")

(defvar *new-variable-counter* 0)

(defun subst-bindings (bindings x)
  "Substitute the value of variables in bindings into x,
  taking recursively bound variables into account."
  (cond ((eq bindings +fail+) +fail+)
        ((eq bindings +no-bindings+) x)
        ((and (variable? x) (get-binding x bindings))
         (subst-bindings bindings (lookup x bindings)))
        ((atom x) x)
        (t (reuse-cons (subst-bindings bindings (car x))
                       (subst-bindings bindings (cdr x))
                       x))))

(defun lookup (var bindings)
  "Get the value part (for var) from a binding list.
   Note that this code is effective for interned iri."
  (binding-val (get-binding var bindings)))

(defun binding-val (binding)
  "Get the value part of a single binding."
  (cdr binding))

(eval-when (:execute :load-toplevel :compile-toplevel)
(defmacro make-binding (var val) `(cons ,var ,val))

(defmacro extend-bindings (var val bindings)
  "Add a (var . value) pair to a binding list."
  (let ((b (gensym)))
    `(cons (make-binding ,var ,val)
           ;; Once we add a "real" binding,
           ;; we can get rid of the dummy +no-bindings+
           (let ((,b ,bindings))
             (if (and (eq ,b +no-bindings+))
                 nil
               ,b)))))
)  ; end of eval-when

(defmethod compound= (x y)
  (equal x y))
(defmethod compound= ((x iri:iri) (y iri:iri))
  (iri:iri= x y))
#|
(ndtree::compound= "test" "test")
|#

(defun unify (x y &optional (bindings +no-bindings+))
  "See if x and y match with given bindings."
;;;  (format t "~%UNIFY(~S ~S ~S)" x y bindings)
  (cond ((eq bindings +fail+) +fail+)
        ((compound= x y) bindings)     ; for any kind of data types, structures, and class-instances
        ((variable? x) (unify-variable x y bindings))
        ((variable? y) (unify-variable y x bindings))
        ((and (consp x) (consp y))
         (unify (rest x) (rest y)
                (unify (first x) (first y) bindings)))
        (t +fail+)))

(defun unify-variable (var x bindings)
  "Unify var with x, using (and maybe extending) bindings."
  (cond ((get-binding var bindings)
         (unify (lookup var bindings) x bindings))
        ((and (variable? x) (get-binding x bindings))
         (unify var (lookup x bindings) bindings))
        ((and *occurs-check* (occurs-check var x bindings))
         +fail+)
        (t (extend-bindings var x bindings))))

(defun get-binding (var bindings)
  "Find a (variable . value) pair in a binding list."
  (assoc var bindings :test #'compound=))     ; var should be a symbol that starts with character '?'.

(defun delete-binding (var bindings)
  (delete (assoc var bindings) bindings))

(defun variable? (x)
  "Is x a variable (a symbol starting with `?')?"
  (and (symbolp x) (eql (char (symbol-name x) 0) #\?)))

(defun occurs-check (var x bindings)
  "Does var occur anywhere inside x?"
  (cond ((eq var x) t)
        ((and (variable? x) (get-binding x bindings))
         (occurs-check var (lookup x bindings) bindings))
        ((consp x) (or (occurs-check var (first x) bindings)
                       (occurs-check var (rest x) bindings)))
        (t nil)))

(defun new-variable (var)
  "Create a new variable.  Assumes user never types variables of form ?<var>.<n>"
  (concat-symbol (if (variable? var) "" "?")
                 var "." (incf *new-variable-counter*)))

#|
(in-package :ndtree)
(unify '(Love John Jane) '(Love John Jane))
(unify '(Love John ?x) '(Love John Jane))
(unify '(Love John ?x) '(Love ?y Jane))
(unify '(Married (FatherOf Mary) (MotherOf ?x))
       '(Married (FatherOf ?y)   (MotherOf Mary)))
(unify '(Married ?x (MotherOf Mary))
       '(Married (FatherOf ?y) (MotherOf Mary)))
(unify '(Married ?x            (MotherOf Mary))
       '(Married (FatherOf ?x) (MotherOf Mary)))
(unify '(rdf:type rdf:Property rdfs:Resource)
       '(rdf:type rdf:Property rdfs:Resource))
(unify `(rdf:type
         ,(iri:iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property")
         ,(iri:iri "http://www.w3.org/2000/01/rdf-schema#Resource"))
       `(rdf:type
         ,(iri:iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property")
         ,(iri:iri "http://www.w3.org/2000/01/rdf-schema#Resource")))
(unify `(rdf:type
         ,(iri:iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property")
         ,(iri:iri "http://www.w3.org/2000/01/rdf-schema#Resource"))
       `(rdf:type rdf:Property rdfs:Resource))
(unify `(rdf:type
         ,(iri:iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property")
         ,(iri:iri "http://www.w3.org/2000/01/rdf-schema#Resource"))
       `(rdf:type ?x ?y))
|#
;;;
;;;; Following is copied from prolog.lisp by Norvig
;;;

;; clauses are represented as (head . body) cons cells
(defun clause-head (clause) (first clause))
(defun clause-body (clause) (rest clause))
#|
;; clauses are stored on the predicate's plist
(defmethod get-clauses (pred) (get pred 'clauses))
(defmethod get-clauses ((pred iri:iri)) (getf (iri:iri-plist pred) 'clauses))
|#
(defun rename-variables (x)
  "replace all variables in x with new ones."
  (sublis (mapcar #'(lambda (var) (cons var (gensym (string var))))
                  (variables-in x))
          x))

(defun continue-p ()
  "Ask user if we should continue looking for solutions."
  (case (read-char)
    (#\; t)
    (#\. nil)
    (#\newline (continue-p))
    (otherwise 
      (format t " Type ; to see more or . to stop")
     (continue-p))))

(defun variables-in (exp)
  "Return a list of all the variables in <exp>."
  (unique-find-anywhere-if #'non-anon-variable? exp))

(defun non-anon-variable? (x)
  (and (variable? x) (not (eq x '?))))

(defun predicate (relation) (and (consp relation) (first relation)))
(defun arg-rest (relation) (and (consp relation) (cddr relation)))

(defun unique-find-anywhere-if (pred-fun tree &optional found-so-far)
  "return a list of leaves of tree satisfying pred-fun,
   with duplicates removed."
  (if (atom tree)
      (if (funcall pred-fun tree)
          (adjoin tree found-so-far)
        found-so-far)
    (unique-find-anywhere-if
     pred-fun
     (first tree)
     (unique-find-anywhere-if pred-fun (rest tree)
                              found-so-far))))

;;; ==============================

;; An nlist is implemented as a (count . elements) pair:
(defun make-empty-nlist () 
  "Create a new, empty nlist."
  (cons 0 nil))

(defun empty-nlist-p (nlist)
  (or (<= (car nlist) 0)
      (null (cdr nlist))))

(defun nlist-n (x) "The number of elements in an nlist." (car x))
(defun nlist-list (x) "The elements in an nlist." (cdr x))
;;; ==============================
;; An nlist is implemented as a (count . elements) pair:

(defun nlist-push (item nlist)
  "Add a new element to an nlist."
  (incf (car nlist))
  (push item (cdr nlist))
  nlist)
#+:never
(defun nlist-push (item nlist)
  "add a new element to an nlist. In this version, 
   the equality of new elements is tested by using <compound=>."
  (cond ((member item (cdr nlist) :test #'compound=)  ; eq/eql/equal/compound=
         nlist)
        (t (incf (car nlist))
           (push item (cdr nlist))
           nlist)))

(defun nlist-delete (item nlist)
  "deletes item from an nlist. In this version, 
   the equality of new elements is tested by using <equal>."
  (cond ((member item (cdr nlist) :test #'compound=)
         (decf (car nlist))
         (setq nlist (cons (car nlist) (delete item (cdr nlist))))
         nlist)
        (t nil)))

;;; ==============================

(defstruct (dtree (:type vector))
  (first nil) (rest nil) (atoms nil) (var (make-empty-nlist)))

;;; ==============================

;; Not all Lisps handle the closure properly, so change the local PREDICATES
;; to a global *predicates* - norvig Jun 11 1996
(defvar *predicates* nil)

;; The original function of <get-dtree> is translated into a set of methods that allows 
;; to handle an instance of <symbol>, <iri>  - seiji Dec 10 2014
(defgeneric get-dtree (predicate)
  (:documentation "fetch (or make) the dtree for this predicate."))
(defmethod get-dtree ((predicate symbol))
  (cond ((get predicate :dtree))
        (t (pushnew predicate *predicates*)
           (setf (get predicate :dtree) (make-dtree)))))

(defmethod get-dtree ((predicate iri:iri))
  (cond ((iri:iri-dtree predicate))
        (t (pushnew predicate *predicates* :test #'equal)
           (setf (iri:iri-dtree predicate) (make-dtree)))))

(defun clear-dtrees ()
  "Remove all the dtrees for all the predicates."
  (dolist (predicate *predicates*)
    (etypecase predicate
      (symbol (setf (get predicate :dtree) nil))
      (iri:iri (setf (iri:iri-dtree predicate) nil))
      ))
  (setf *predicates* nil)
  t)

(defun delete-index (key value dtree)
  "deletes value under all atoms of key in dtree."
  ;(format t "~%key: ~S" key)
  (cond ((consp key)               ; index on both first and rest
         (delete-index (first key) value
                       (dtree-first dtree))
         (delete-index (rest key) value
                       (dtree-rest dtree)))
        ((null key))              ; don't index on nil
        ((variable? key)          ; index a variable
         (nlist-delete value (dtree-var dtree)))
        ((atom key)
         (let ((atom-nlist (lookup key (dtree-atoms dtree))))
           (when (member value (cdr atom-nlist) :test #'compound=)
             ;(format t "~%Deleting ~S at key ~S" value key)
             (decf (car atom-nlist))
             (setf (cdr atom-nlist) (delete value (cdr atom-nlist) :test #'compound=)))))
        (t ;; Make sure there is an nlist for this atom, and delete from it
         (error "Not Yet!")
         (let ((nlist (nlist-delete value (lookup key (dtree-atoms dtree)))))
           (when (empty-nlist-p nlist)
             (error "Not Yet!"))))))

;;; ==============================

(defun dtree-index (key value dtree)
  "Index value under all atoms of key in dtree."
  (cond ((consp key)               ; index on both first and rest
         (dtree-index (first key) value
                      (or (dtree-first dtree)
                          (setf (dtree-first dtree) (make-dtree))))
         (dtree-index (rest key) value
                      (or (dtree-rest dtree)
                          (setf (dtree-rest dtree) (make-dtree)))))
        ((null key))              ; don't index on nil
        ((variable? key)          ; index a variable
         (nlist-push value (dtree-var dtree)))
        (t ;; Make sure there is an nlist for this atom, and add to it
         (nlist-push value (lookup-atom key dtree)))))

(defun lookup-atom (atom dtree)
  "Return (or create) the nlist for this atom in dtree."
  (or (lookup atom (dtree-atoms dtree))
      (let ((new (make-empty-nlist)))
        (push (cons atom new) (dtree-atoms dtree))
        new)))

;;; ==============================

(defun test-index ()
  (let ((props `((p a b) (p a c) (p a ?x) (p b c)
                 (p b (f c)) (p a (f . ?x))
                 (p
                  ,(iri:iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property")
                  ,(iri:iri "http://www.w3.org/2000/01/rdf-schema#Resource")))))
    (clear-dtrees)
    (mapc #'index props)
    (write (list props (get-dtree 'p))
           :circle t :array t :pretty t)
    (values)))

#|
(in-package :ndtree)
(test-index)
(fetch '(p a b))
(fetch '(p a xx))
(fetch '(p ?x ?y))
(fetch '(p ?x c))
(fetch '(p a ?y))
(fetch `(p ,(iri:iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property") ,(iri:iri "http://www.w3.org/2000/01/rdf-schema#Resource")))
(fetch `(p ?x ,(iri:iri "http://www.w3.org/2000/01/rdf-schema#Resource")))
(fetch `(p ,(iri:iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property") ?y))
|#
#|
(ndtree:clear-dtrees)
(ndtree:index '(pd3:output logA:cRedBhidVjLa7Tl5MwXh-1 logA:cRedBhidVjLa7Tl5MwXh-7 logA:cRedBhidVjLa7Tl5MwXh-8))
(ndtree:fetch '(pd3:output logA:cRedBhidVjLa7Tl5MwXh-1 . ?o))
|#
(defun fetch (query)
  "Return a list of buckets potentially matching the query,
   which must be a relation of form (predicate . args)."
  (loop for pat in (flatten (dtree-fetch query (get-dtree (predicate query))
                                         nil 0 nil most-positive-fixnum))
      when (ndtree:unify pat query)
      collect pat))

#|
(ndt:dtree-fetch '(rdfs:comment rdf:direction . ?o) (ndt:get-dtree 'rdfs:comment)
                 nil 0 nil most-positive-fixnum)
|#

(defun dtree-fetch (pat dtree var-list-in var-n-in best-list best-n)
  "Return two values: a list-of-lists of possible matches to pat,
  and the number of elements in the list-of-lists."
  (if (or (null dtree) (null pat) (variable? pat))
      (values best-list best-n)
    (let* ((var-nlist (dtree-var dtree))
           (var-n (+ var-n-in (nlist-n var-nlist)))
           (var-list (if (null (nlist-list var-nlist))
                         var-list-in
                       (cons (nlist-list var-nlist)
                             var-list-in))))
      (cond
       ((>= var-n best-n) (values best-list best-n))   ; >= 
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
    (cond ((or (null atom-nlist) (null (nlist-list atom-nlist)))
           (values var-list var-n))
          ((and atom-nlist (< (incf var-n (nlist-n atom-nlist)) best-n))  ; (< 2 1)
           (values (cons (nlist-list atom-nlist) var-list) var-n))
          (t (values best-list best-n)))))

;;; ==============================
(eval-when (:execute :load-toplevel :compile-toplevel)
(proclaim '(inline mapc-retrieve))
)

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

;;;
;;;; Krep2
;;;
;;; Hereafter, copied from krep2.lisp by norvig.

(defun index (key)
  "Store key in a dtree node.  Key must be (predicate . args);
  it is stored in the predicate's dtree."
  (dtree-index key (rename-variables key)    ; store unique vars
               (get-dtree (or (predicate key) key))))

(defun index-delete (key)
  (delete-index key key (get-dtree (or (predicate key) key))))

;;; ==============================

;;; The following iterated-deepening code is not used, but is
;;; included for those who want to incorporate it into prolog.
#|
(defvar *search-cut-off* nil "Has the search been stopped?")

(defun prove-all (goals bindings depth)
  "Find a solution to the conjunction of goals."
  ;; This version just passes the depth on to PROVE.
  (cond ((eq bindings +fail+) +fail+)
        ((null goals) bindings)
        (t (prove (first goals) bindings (rest goals) depth))))

(defun prove (goal bindings other-goals depth)
  "Return a list of possible solutions to goal."
  ;; Check if the depth bound has been exceeded
  (if (= depth 0)                            ;***
      (progn (setf *search-cut-off* t)       ;***
             +fail+)                           ;***
      (let ((clauses (get-clauses (predicate goal))))
        (if (listp clauses)
            (some
              #'(lambda (clause)
                  (let ((new-clause (rename-variables clause)))
                    (prove-all
                      (append (clause-body new-clause) other-goals)
                      (unify goal (clause-head new-clause) bindings)
                      (- depth 1))))          ;***
              clauses)
            ;; The predicate's "clauses" can be an atom:
            ;; a primitive function to call
            (funcall clauses (rest goal) bindings
                     other-goals depth)))))   ;***
|#
;;; ==============================

(defparameter *depth-start* 5
  "The depth of the first round of iterative search.")
(defparameter *depth-incr* 5 
  "Increase each iteration of the search by this amount.")
(defparameter *depth-max* most-positive-fixnum
  "The deepest we will ever search.")

;;; ==============================
#|
(defun top-level-prove (goals)
  (let ((all-goals
          `(,@goals (show-prolog-vars ,@(variables-in goals)))))
    (loop for depth from *depth-start* to *depth-max* by *depth-incr*
          while (let ((*search-cut-off* nil))
                  (prove-all all-goals +no-bindings+ depth)
                  *search-cut-off*)))
  (format t "~&No.")
  (values))
|#
;;; ==============================
#|
(defun show-prolog-vars (vars bindings other-goals depth)
  "Print each variable with its binding.
  Then ask the user if more solutions are desired."
  (if (> depth *depth-incr*)
      +fail+
      (progn
        (if (null vars)
            (format t "~&Yes")
            (dolist (var vars)
              (format t "~&~a = ~a" var
                      (subst-bindings bindings var))))
        (if (continue-p)
            +fail+
            (prove-all other-goals bindings depth)))))
|#
;;; ==============================

;;;; Adding support for conjunctions:

(defun add-fact (fact)
  "Add the fact to the data base."
  (if (eq (predicate fact) 'and)
      (mapc #'add-fact (args fact))
    (index fact)))

;;; ==============================

(defun retrieve-fact (query &optional (bindings +no-bindings+))
  "Find all facts that match query.  Return a list of bindings."
  (if (eq (predicate query) 'and)
      (retrieve-conjunction (args query) (list bindings))
      (retrieve query bindings)))

(defun retrieve-conjunction (conjuncts bindings-lists)
  "Return a list of binding lists satisfying the conjuncts."
  (mapcan
    #'(lambda (bindings)
        (cond ((eq bindings +fail+) nil)
              ((null conjuncts) (list bindings))
              (t (retrieve-conjunction
                   (rest conjuncts)
                   (retrieve-fact
                     (subst-bindings bindings (first conjuncts))
                     bindings)))))
    bindings-lists))

;;; ==============================

(defun mapc-retrieve (fn query &optional (bindings +no-bindings+))
  "For every fact that matches the query,
  apply the function to the binding list."
  (dolist (bucket (fetch query))
    (dolist (answer bucket)
      (let ((new-bindings (unify query answer bindings)))
        (unless (eq new-bindings +fail+)
          (funcall fn new-bindings))))))

(defun retrieve (query &optional (bindings +no-bindings+))
  "Find all facts that match query.  Return a list of bindings."
  (let ((answers nil))
    (mapc-retrieve #'(lambda (bindings) (push bindings answers))
                   query bindings)
    answers))


;;; ==============================

(defun retrieve-bagof (query)
  "Find all facts that match query.
  Return a list of queries with bindings filled in."
  (mapcar #'(lambda (bindings) (subst-bindings bindings query))
          (retrieve-fact query)))

(defun retrieve-setof (query)
  "Find all facts that match query.
  Return a list of unique queries with bindings filled in."
  (remove-duplicates (retrieve-bagof query) :test #'equal))

;;; ==============================

;;;; Get ready for attached functions in the next version:

(defmacro def-attached-fn (pred args &body body)
  "Define the attached function for a primitive."
  `(setf (get ',pred 'attached-fn)
         #'(lambda ,args .,body)))
