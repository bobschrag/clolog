(ns clolog.core
  (:require [clojure.pprint :refer [cl-format]]
            [clojure.string :as str]
            [clojure.set :refer [difference]]
            [clojure.walk :refer [postwalk]]
            ))

(def ^:dynamic *assertions*
  "The repository of assertions (AKA knowledge base) defined by the user
  or using application.  Bind this (and possibly
  `*predicate-transforms*`) to manage separate knowledge bases
  simultaneously, or to checkpoint a knowledge base."
  (atom {}))

(def ^:dynamic *predicate-transforms*
  "The repository of predicate transforms defined by the user or using
  application.  Bind this to manage alternative transform
  definitions."
  (atom {}))

(defn assert<- [assertion]
  "Add `assertion` to the knowledge base.  If the assertion's head
  clause has a constant predicate and fixed arity, place `assertion's`
  last for consideration in search."
  ;; ...
  )

(defmacro <- [& assertion]
  "The macro version of function `assert<--`."
  `(assert<- (quote ~assertion)))

(defn assert<-- [assertion]
  "Add `assertion` to the knowledge base---after clearing its
  required-constant head clause predicate at its required-fixed
  arity."
  ;; ...
  )

(defmacro <-- [& assertion]
  "The macro version of function `assert<--`."
  `(assert<-- (quote ~assertion)))

(defn assert<--- [assertion]
  "Add `assertion` to the knowledge base---after clearing the entire
  knowledge base."
  ;; ...
  )

(defmacro <--- [& assertion]
  "The macro version of function `assert<---`."
  `(assert<--- (quote ~assertion)))

(defn assert<-0 [assertion]
  "Add `assertion` to the knowledge base---after clearing its
  required-constant head clause predicate at its required-fixed
  arity."
  ;; ...
  )

(defmacro <-0 [& assertion]
  "The macro version of function `assert<-0`."
  `(assert<-0 (quote ~assertion)))

;;; Predicate transform (AKA logic macro) facility:

(defn create-predicate-transform [transform]
  "Create one of the production rules used in transforming a clause
  with given predicate."
  ;; ...
  )

(defn create-predicate-transforms
  "Define the predicate transforms included here."
  ([]
   (create-predicate-transforms false))
  ([debugging?]
   (reset! *predicate-transforms* {})
   (let [create-predicate-transform (if debugging?
                                      assert<-
                                      create-predicate-transform)]
     ;; Designing to unique assertion head arity can be appropriate.
     ;;
     ;; `if*` (as in Allegro Prolog)
     (create-predicate-transform '((if* ?if ?then ?else) (if ?if ?then ?else)))
     ;; `if%` (Allegro Prolog `if`)
     (create-predicate-transform '((if% ?if ?then ?else) (if (first ?if) ?then ?else)))
     ;; `cond*`
     (create-predicate-transform '((cond*) (or))) ; Handled so in Clojure.
     (create-predicate-transform '((cond* ?if ?then :else ?else) (if* ?if ?then ?else)))
     (create-predicate-transform '((cond* ?if1 ?then1 ?if2 ?then2 & ?rest) ; `& ?rest` in input form.
                                   (if* ?if1 ?then1 (cond* ?if2 ?then2 & ?rest))))
     ;; `cond%`
     (create-predicate-transform '((cond%) (or)))
     (create-predicate-transform '((cond% ?if ?then :else ?else) (if% ?if ?then ?else)))
     (create-predicate-transform '((cond% ?if1 ?then1 ?if2 ?then2 & ?rest)
                                   (if% ?if1 ?then1 (cond% ?if2 ?then2 & ?rest))))
     ;; Consider `when`, `when-not`, `when%`, `when%-not`.
     ;; `optional` (as in SPARQL)
     (create-predicate-transform '((optional ?goal) (if ?goal (true) (true))))
     ;; `different`
     (create-predicate-transform '((different ?a ?b) (not (same ?a ?b))))
     ;; `is`
     (create-predicate-transform '((is ?a ?b) (same ?a ?b)))
     ;; Norvig `lisp`, `lispp`
     (create-predicate-transform '((lisp ?form) (do ?form)))
     (create-predicate-transform '((lisp ?logic ?form) (evals-from? ?logic ?form)))
     (create-predicate-transform '((lispp ?form) (truthy? ?form)))
     )))

;;; Make sure a using namespace gets public symbols (those not in
;;; `clojure.core`) we have introduced for built-in predicates.
(def truthy?)
(def evals-from?)
(def ground)
(def same)

(defn get-matching-assertions [clause-pattern]
  "Return a vector of the assertions matching `clause-pattern`."
  ;; ...
  )

(declare subsumes?)

(defn get-subsumed-assertions [clause-pattern]
  "Return a vector of the assertions subsumed by `clause-pattern`."
  ;; ...
  )

(defn get-subsuming-assertions [clause-pattern]
  "Return a vector of the assertions subsuming `clause-pattern`."
  ;; ...
  )

(defn retract-subsumed-assertions [clause-pattern]
  "Retract the assertions subsumed by `clause-pattern`."
  ;; ...
  )

(defmacro --- [clause-pattern]
  "The macro version of function `retract-subsumed-assertions`."
  `(retract-subsumed-assertions (quote ~clause-pattern)))

(defn retract-specific-assertion [assertion]
  "Retract `assertion`, using `=` (so, respecting ?var symbols)."
  ;; ...
  )

(defmacro -- [& clauses]
  "The macro version of function `retract-specific-assertion`."
  `(retract-specific-assertion (quote ~clauses)))

(defn unprint-i?vars [expr]
  "Convert i?vars' print representations in `expr` to actual
   i?vars---making it easier to execute expressions copied from
   Clojure execution traces."
  ;; ...
  )

(def ^:dynamic *answer-count-limit*
  "When truthy, terminate query execution upon having recorded (positive
  integer) `*answer-count-limit*` answers."
  nil)

(def ^:dynamic *discard-subsumed-answers*
  "When truthy, during query execution discard answers subsumed by other
  answers."
  true)

(def ^:dynamic *leash*
  "When truthy, during query execution, write informative reports to
  standard output."
  false)

(defn query [answer-template goals
             & {:keys [limit
                       discard-subsumed
                       ;; For negation as failure (private):
                       stack-index
                       special-form-stack
                       special-form-depth]
                :or {limit *answer-count-limit*
                     discard-subsumed *discard-subsumed-answers*
                     ;; Private:
                     stack-index 0
                     special-form-stack ()
                     special-form-depth 0}}]
  "Perform (depth-first, pre-order) logic programming search over
  goals, instantiating `answer-template` upon each success, and return
  a vector of such answers.  Discard (and/or do not record) subsumed
  answers, per `discard-subsumed`.  Terminate search upon having
  recorded `limit` answers."
  ;; ...
  )

(defmacro ? [answer-template & goals] ; Does not support keyword args.
  "The macro version of function `query`."
  `(query (quote ~answer-template) (quote ~goals)))

