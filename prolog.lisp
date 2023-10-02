;;;-*- Mode: Lisp; Syntax: Common-Lisp -*-
;;; ==================================================================================
;;;; Prolog for DTREE
;;;
;;; This module is copied from http://www.norvig.com/ and modified by Seiji Koide.
;;; Copyright (c) 2009 Seiji Koide
;;; ==================================================================================

(eval-when (:execute :load-toplevel :compile-toplevel)
  
) ; end of eval-when

(defpackage :dtree 
  (:export ))
(in-package :dtree)

;;;; Code from Paradigms of AI Programming
;;;; Copyright (c) 1991 Peter Norvig

;;;; File prolog.lisp: prolog from (11.3), with interactive backtracking.

;;;; does not include destructive unification (11.6); see prologc.lisp

(defmacro <- (&rest clause)
  "add a clause to the data base."
  `(add-clause ',(replace-?-vars clause)))

(defun add-clause (clause)
  "add a clause to the data base, indexed by head's predicate."
  ;; the predicate must be a non-variable symbol.
  (let ((pred (predicate (clause-head clause))))
    (assert (and (symbolp pred) (not (variable? pred))))
    (pushnew pred *predicates*)
    (setf (get pred 'clauses)
          (nconc (get-clauses pred) (list clause)))
    pred))

(defun clear-predicate (predicate)
  "remove the clauses for a single predicate."
  (setf (get predicate 'clauses) nil))

(defmacro ?- (&rest goals) `(top-level-prove ',(replace-?-vars goals)))

;; (setf (get 'show-prolog-vars 'clauses) 'show-prolog-vars)

(defun replace-?-vars (exp)
    "Replace any ? within exp with a var of the form ?123."
    (cond ((eq exp '?) (gensym "?"))
          ((atom exp) exp)
          (t (reuse-cons (replace-?-vars (first exp))
                         (replace-?-vars (rest exp))
                         exp))))
