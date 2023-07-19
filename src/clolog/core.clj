(ns clolog.core
  (:require [clojure.pprint :refer [pprint cl-format]]
            [clojure.string :as str]
            [clojure.set :refer [difference]]
            [clojure.walk :refer [postwalk]]
            ))

;;; We provide a richly featured Prolog interpreter that can be called
;;; by and call Clojure.

;;;;; ----------------------------------------------------------------
;;;;; Knowledge base:

;;; We repersent an assertion---i,e., a Prolog rule or fact, as a
;;; list of clauses (<head> <goal>*), where each clause is a list
;;; (<predicate> <term>*).

;;; A term can be just about any Clojure object possessing
;;; identity/supporting equality (so, not a regex).

;;; In matching (e.g.) goals and assertion heads, we look inside only
;;; seqs and lists.

;;; A predicate can be anything you like---not necessarily a
;;; symbol (so if you like go wild with RDF).  (And you can use
;;; multi-word strings.)

;;; And (apart from Prolog-reserved symbols) there is nothing
;;; semantically special about the "predicate" position in a "clause"
;;; tuple.  We do index it more aggressively (so far, exclusively)
;;; than the other positions, but a ?var in the predicate position
;;; also is completely acceptable.

;;; The variable below is dynamic---so that using applications
;;; can stash a value when done compiling a model, then bind the
;;; value afresh when they'd like to augment it.
;;;
;;; Keys are predicates.
;;; Within a predicate, keys are arities.
;;; Within an arity, assertions are ordered (even under any indexing).
;;; For separate models, bind these and any other globals.
(def ^:dynamic *assertions*
  "The repository of assertions (AKA knowledge base) defined by the user
  or using application.  Bind this (and possibly
  `*predicate-transforms*`) to manage separate knowledge bases
  simultaneously, or to checkpoint a knowledge base."
  (atom {}))

;;; The assertions defining predicate transforms.
(def ^:dynamic *predicate-transforms*
  "The repository of predicate transforms defined by the user or using
  application.  Bind this to manage alternative transform
  definitions."
  (atom {}))

(declare ?var?)
(declare indexify)
(declare built-in-special-head?)

(defn- check-assertion [assertion]
  (assert (not (?var? (first assertion)))
          "Head clauses may not productively match all goals.")
  (let [goal (first assertion)
        head (first goal)]
    (assert (not (= head '&))
            "Head clauses may not productively match all goals.")
    (assert (not (built-in-special-head? head))
            "No assertions may be added to built-in special forms.")))

;;; Find out some things to store assertions appropriately.
(defn- complex? [head]
  (or (seq? head) (vector? head)))

(declare ground?)

(defn- non-ground-complex? [head]
  (and (complex? head)
       (not (ground? head))))

(declare unindexify)
(declare i?var?)

(defn- get-predicate
  ([head unindexed?]
   (unindexify (get-predicate (indexify head 0))
               0))
  ([head]
   (if (i?var? (first head))
     'variable
     (if (non-ground-complex? (first head))
       ;; For now, a single bucket.  FUTURE: A trie.
       'non-ground-complex
       (first head)))))

;;; Not checking for duplicate/subsumed assertions---which we really don't want.
;;; But, if submitted, should we...
;;; - [Warn and] keep the original, in order?
;;; - [Warn and] keep the latest?
;;; - Just barf?
;;; Consider for FUTURE.
(defn assert<- [assertion]
  "Add `assertion` to the knowledge base.  If the assertion's head
  clause has a constant predicate and fixed arity, place `assertion's`
  last for consideration in search."
  (check-assertion assertion)
  (let [head (first assertion)
        predicate (get-predicate head :unindexed)
        arity (if (some #{'&} head)
                'variadic
                (count (rest head)))
        predicate-assertions (or (get @*assertions* predicate)
                                 ;; Initialize with the empty map of arities.
                                 {})
        arity-assertions (or (get predicate-assertions arity)
                             ;; Initialize with this assertion.
                             [])
        arity-assertions (conj arity-assertions assertion)
        predicate-assertions (assoc predicate-assertions arity arity-assertions)]
    (swap! *assertions* assoc predicate predicate-assertions)))

(defmacro <- [& assertion]
  "The macro version of function `assert<--`."
  `(assert<- (quote ~assertion)))

(defn assert<-- [assertion]
  "Add `assertion` to the knowledge base---after clearing its
  required-constant head clause predicate at its required-fixed
  arity."
  (check-assertion assertion)
  (let [head (first assertion)
        predicate (get-predicate head :unindexed)
        arity (if (some #{'&} head)
                'variadic
                (count (rest head)))]
    (assert (not= predicate 'variable)
            "Retract variable-predicate assertions more particularly.")
    (assert (not= predicate 'non-ground-complex)
            "Retract assertions with non-ground-complex head clause predicates more particularly.")
    (assert (not= arity 'variadic)
            "Retract variadic assertions more particularly.")
    (swap! *assertions* update-in [predicate] assoc arity [assertion])))

(defmacro <-- [& assertion]
  "The macro version of function `assert<--`."
  `(assert<-- (quote ~assertion)))

(defn assert<--- [assertion]
  "Add `assertion` to the knowledge base---after clearing the entire
  knowledge base."
  (check-assertion assertion)
  (reset! *assertions* {})
  (assert<- assertion))

(defmacro <--- [& assertion]
  "The macro version of function `assert<---`."
  `(assert<--- (quote ~assertion)))

(declare predicate-arity-assertions)

(defn assert<-0 [assertion]
  "Add `assertion` to the knowledge base---after clearing its
  required-constant head clause predicate at its required-fixed
  arity."
  (check-assertion assertion)
  (let [head (first assertion)
        predicate (get-predicate head :unindexed)
        arity (if (some #{'&} head)
                'variadic
                (count (rest head)))]
    (assert (not= predicate 'non-ground-complex)
            "Non-ground-complex-predicate assertion order control not supported.")
    (assert (not= predicate 'variable)
            "Variable-predicate assertion order control not supported.")
    (assert (not= arity 'variadic)
            "Variadic assertion order control not supported.")
    (let [assertions (apply list (predicate-arity-assertions predicate arity))
        assertions (vec (cons assertion assertions))]
      (swap! *assertions* update-in [predicate] assoc arity assertions))))

(defmacro <-0 [& assertion]
  "The macro version of function `assert<-0`."
  `(assert<-0 (quote ~assertion)))

;;; Predicate transform (AKA logic macro) facility:

(defn create-predicate-transform [transform]
  "Create one of the production rules used in transforming a clause
  with given predicate."
  (let [goal (first transform)
        head (first goal)
        head-transforms (or (get @*predicate-transforms* head)
                                 [])
        head-transforms (conj head-transforms transform)]
    (assert (not (built-in-special-head? head)))
    (swap! *predicate-transforms* assoc head head-transforms)))

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

(defn initialize-prolog []
  "Reset/clear the knowledge base, clear and re-define transforms."
  (reset! *assertions* {})
  (create-predicate-transforms))

(defn- predicate-arity-assertions [predicate arity]
  (get (get @*assertions* predicate)
       arity))

;;; In case of ?var in predicate position, return candidate assertions
;;; of `arity` (perhaps `variadic`) for all predicates.
(defn- arity-assertions [arity]
  (mapcat (fn [predicate-assertions]
            (get predicate-assertions arity))
          (vals @*assertions*)))

(defn- all-assertions []
  (mapcat (fn [predicate-assertions]
            (let [arity-assertions (vals predicate-assertions)]
              (apply concat arity-assertions)))
          (vals @*assertions*)))

;;; Duplicate:
;;; (defn- all-assertions []
;;;   (vec (apply concat (mapcat vals (vals @*assertions*)))))

;;; Check whether a term symbol is a Prolog ?var (variable).
(defn- ?var? [thing]
  (and (symbol? thing)
       (= \? (first (name thing)))))

(def ^:private public-built-in-special-heads '#{truthy? do evals-from?
                                                var ground
                                                and or not if
                                                first 
                                                same
                                                true false})

;;; Make sure a using namespace gets public symbols (those not in
;;; `clojure.core`) we have introduced for built-in predicates.
(def truthy?)
(def evals-from?)
(def ground)
(def same)

(defn- public-built-in-special-head? [head]
  (contains? public-built-in-special-heads head))

(def ^:private private-built-in-special-heads
  '#{and... or... ; Non-leashed.
     sys-and ; Non-leashed, does not inc/dec `*special-form-depth*`.
     if-then then else drop-else fail-if succeed-if
     fail-first succeed-first})

(defn- private-built-in-special-head? [head]
  (contains? private-built-in-special-heads head))

(defn- built-in-special-head? [head]
  (or (public-built-in-special-head? head)
      (private-built-in-special-head? head)))

;;; We distinguish the first/source/whole occurrence of a multi-arity
;;; special form (`and`, `or`) by ellipsis-suffixing (`and...`,
;;; `or...`) its subsequent occurrences that we introduce as we work
;;; down its list (of conjuncts, disjuncts).

(defn- non-transformable-predicate? [goal]
  (and (seq? goal)
       (let [head (first goal)]
         (built-in-special-head? head))))

(defn- transformable-predicate? [goal]
  (and (seq? goal)
       (let [head (first goal)]
         (contains? @*predicate-transforms* head))))

(defn- special-goal? [goal]
  (or (non-transformable-predicate? goal)
      (transformable-predicate? goal)))

(defn- candidate-variadic-assertions-predicate [predicate &-position]
  (vec (mapcat #(predicate-arity-assertions predicate %)
               (filter #(>= % (dec &-position))
                       ;; This will include `variadic`.
                       (keys (get @*assertions* predicate))))))

(defn- candidate-variadic-assertions [goal]
  (let [goal (vec goal)
        &-position (.indexOf goal '&)]
    (if (= &-position 0)
      (all-assertions)
      (let [predicate (get-predicate goal)
            predicate-assns (candidate-variadic-assertions-predicate predicate &-position)]
        (if (= predicate 'variable)
          predicate-assns
          (vec (concat predicate-assns
                       (candidate-variadic-assertions-predicate 'variable &-position))))))))

(declare i?var?)

;;; FUTURE: Index beyond predicates.  
(defn- candidate-assertions [goal]
  (when goal
    (if (or (i?var? goal) (= goal '(&)))
        (all-assertions)
        (if (some #{'&} goal) ; `&` at top level.
          (candidate-variadic-assertions goal)
          ;; Not variadic (but could match variadic).
          (let [predicate (get-predicate goal)
                arity (count (rest goal))]
            (if (= predicate 'variable)
              ;; Covers `variable`.
              (vec (concat (arity-assertions 'variadic)
                           ;; Includes `non-ground-complex`.
                           (arity-assertions arity)))
              ;; Not`(= predicate 'variable)`.
              (if (or (= predicate 'non-ground-complex)
                      ;; Covers ground-complex.
                      (complex? predicate))
                ;; We need everything.
                (vec (concat (predicate-arity-assertions 'variable 'variadic)
                             (predicate-arity-assertions predicate 'variadic)
                             ;; Our future trie will facilitate
                             ;; retrieval of assertions headed by
                             ;; complex predicates.  For now, we grab
                             ;; everything of like arity (and let
                             ;; unification sort it out).
                             (arity-assertions arity)))
                ;; Not complex.
                (vec (concat (predicate-arity-assertions predicate arity)
                             (predicate-arity-assertions predicate 'variadic)
                             (predicate-arity-assertions 'variable arity)
                             (predicate-arity-assertions 'variable 'variadic))))))))))

(declare i?var-unify)
(declare unify)
(declare de-reference)

(defn- get-assertion-matches [assn-index goal bindings]
  (when-not (or (nil? goal)
                (special-goal? goal))
    (mapcat (fn [assertion]
              (let [assertion (if assn-index
                                (indexify assertion assn-index)
                                assertion)
                    unindexed? (if assn-index false :unindexed)
                    match (if unindexed? unify i?var-unify)
                    head (first assertion)
                    goals (rest assertion)
                    ;; If not for our fancy predicate notions (e.g.,
                    ;; predicates that are ?vars), we might here pass
                    ;; to `i?var-unify` just the `rest` of `goal-form`
                    ;; and of `head`.
                    bindings? (and goal head
                                   (match (de-reference bindings goal unindexed?)
                                          (de-reference bindings head unindexed?)
                                          bindings))]
                (when bindings?
                  (list [assertion bindings?]))))
            (candidate-assertions (indexify goal 0)))))

(defn get-matching-assertions [clause-pattern]
  "Return a vector of the assertions matching `clause-pattern`."
  (vec (map first (get-assertion-matches nil clause-pattern [{} {}]))))

(declare subsumes?)

(defn get-subsumed-assertions [clause-pattern]
  "Return a vector of the assertions subsumed by `clause-pattern`."
  (vec (map first
            (filter (fn [match]
                      (let [[pattern-env assn-env] (second match)]
                        (subsumes? pattern-env assn-env)))
                    (get-assertion-matches nil clause-pattern [{} {}])))))

(defn get-subsuming-assertions [clause-pattern]
  "Return a vector of the assertions subsuming `clause-pattern`."
  (vec (map first
            (filter (fn [match]
                      (let [[pattern-env assn-env] (second match)]
                        (subsumes? assn-env pattern-env)))
                    (get-assertion-matches nil clause-pattern [{} {}])))))

(comment ; Roll your own...
  (defn listing [clause-pattern]
    (doseq [assn (get-matching-assertions clause-pattern)]
      (pprint assn))))

(defn- retract-subsumed-predicate-arity-assertions [predicate arity clause-pattern]
  (let [predicate-assns (or (get @*assertions* predicate) {})
        arity-assns (set (or (get predicate-assns arity) []))
        retracted-assns (set (get-subsumed-assertions clause-pattern))
        remaining-assns (difference arity-assns retracted-assns)
        actually-retracted-assns (vec (difference arity-assns remaining-assns))
        remaining-assns (vec remaining-assns)]
    ;; FUTURE: Provide some useful feedback?
    (if-not (seq remaining-assns)
      (swap! *assertions* update-in [predicate] dissoc arity)
      (swap! *assertions* update-in [predicate] assoc arity remaining-assns))
    (when-not (seq (get @*assertions* predicate))
      (swap! *assertions* dissoc predicate))))

(defn- retract-subsumed-assertions-variadic [clause-pattern]
  (let [clause-pattern (vec clause-pattern)
        &-position (.indexOf clause-pattern '&)]
    (if (= &-position 0)
      ;; So, `(and (= arity 0) (?var? (second clause-pattern)))`.
      (reset! *assertions* {})
      ;; Else we have a predicate.
      (let [predicate (get-predicate clause-pattern :unindexed)]
        (if (= predicate 'variable)
          (if (= &-position 1)
            (reset! *assertions* {})
            ;; Drop greater arities of all predicates.
            (mapv (fn [predicate]
                    (retract-subsumed-assertions-variadic `(~predicate ~@(rest clause-pattern))))
                  (keys @*assertions*)))
          (if (= &-position 1)
            ;; Drop all arities.
            (swap! *assertions* dissoc predicate)
            ;; Drop greater arities.
            (mapv (fn [arity]
                    (retract-subsumed-predicate-arity-assertions predicate arity clause-pattern))
                  (filter #(>= % (dec &-position))
                          (keys (get @*assertions* predicate))))))))))
      
;;; `clause-pattern` here is for assertions' head clauses (only).
(defn retract-subsumed-assertions [clause-pattern]
  "Retract the assertions subsumed by `clause-pattern`."
  ;; (println (cl-format nil "retract-subsumed-assertions: [~s]" clause-pattern))
  (if (?var? clause-pattern)
    (reset! *assertions* {})
    (if (some #{'&} clause-pattern)
      (retract-subsumed-assertions-variadic clause-pattern)
      (let [predicate (get-predicate clause-pattern :unindexed)
            arity (count (rest clause-pattern))]
        (if (or (= predicate 'variable)
                ;; Later, store complex-predicate assertions in a
                ;; trie.  Now, this is our way to cover all the ground
                ;; ones.
                (= predicate 'non-ground-complex))
          ;; Drop all subsumed clauses of exhibited arity.
          (do (mapv (fn [predicate]
                      (let [clause-pattern `(~predicate ~@(rest clause-pattern))]
                        (retract-subsumed-predicate-arity-assertions predicate arity clause-pattern)))
                    (keys @*assertions*))
              ;; Handle an input non-ground-complex `clause-pattern`.
              (retract-subsumed-predicate-arity-assertions predicate arity clause-pattern))
          (retract-subsumed-predicate-arity-assertions predicate arity clause-pattern))))))

;;; Compare to Prolog "abolish".
(defmacro --- [clause-pattern]
  "The macro version of function `retract-subsumed-assertions`."
  `(retract-subsumed-assertions (quote ~clause-pattern)))

;;; The above will retract any assertion whose head matches
;;; `clause-pattern`.  To retract just a specific assertion, use
;;; `retract-specific-assertion`.

;;; Compare to Prolog "retract".
(defn- retract-specific-assertion-predicate-arity [predicate arity assertion]
  (let [predicate-assns (or (get @*assertions* predicate) {})
        arity-assns (or (get predicate-assns arity) [])
        ;; FUTURE: Warn, when appropriate, if `assertion` is missing.
        remaining-assns (remove #{assertion} arity-assns)]
    (if-not (seq remaining-assns)
      (swap! *assertions* update-in [predicate] dissoc arity)
      (swap! *assertions* update-in [predicate] assoc arity remaining-assns))
    (when-not (seq (get @*assertions* predicate))
      (swap! *assertions* dissoc predicate))))

(comment ; No productive use case.
  (defn- retract-specific-assertion-variable-head [assertion]
    ;; Variable-head assertions are not refined by arity (cover all arities).
    (let [assertions (or (get @*assertions* 'variable-head) {})
          remaining-assns (remove assertions assertion)]
      (when-not (seq remaining-assns)
        (swap! *assertions* dissoc 'variable-head)))))

(defn- retract-specific-assertion-variadic-head [assertion]
  (let [head (first assertion)
        predicate (get-predicate head :unindexed)
        &-position (.indexOf head '&)]
    (map (fn [arity]
           (retract-specific-assertion-predicate-arity predicate arity assertion))
         (filter #(>= % (dec &-position))
                 (keys (get @*assertions* predicate))))))

(defn retract-specific-assertion [assertion]
  "Retract `assertion`, using `=` (so, respecting ?var symbols)."
  (let [head (first assertion)]
    (cond
      ;; No productive use case.
      ;; (or (?var? head)
      ;;     (= '& (first head)))
      ;; (retract-specific-assertion-variable-head assertion))

      (some #{'&} head)
      (retract-specific-assertion-variadic-head assertion)
      
      :else
      (let [predicate (get-predicate head :unindexed)
            arity (if (some #{'&} head)
                    'variadic
                    (count (rest head)))]
        (retract-specific-assertion-predicate-arity predicate arity assertion)))))

(defmacro -- [& clauses]
  "The macro version of function `retract-specific-assertion`."
  `(retract-specific-assertion (quote ~clauses)))

;;;;; Knowledge base ^^
;;;;; ----------------------------------------------------------------
;;;;; Matching (AKA unification), de-referencing, exporting i?vars:

;;; We need our own type here, to distinguish Prolog's [index ?var]
;;; pair from a user's similarly structured pair.  (We don't need to
;;; do the same thing for our goals, exclusively internal to Prolog.)
;;;
;;; Indexed ?var:
(defrecord ^:private I?var [index ?var])

;;; To trace the full namespace, comment out these print functions.
(defn- format-i?var [x]
  (read-string (cl-format nil "~a:~d" (:?var x) (:index x))))

(defmethod print-method I?var [x ^java.io.Writer writer]
  (print-method (format-i?var x) writer))

(defmethod print-dup I?var [x ^java.io.Writer writer]
  (print-dup (format-i?var x) writer))

(defn- i?var? [expr]
  (= (type expr) clolog.core.I?var))

(defn unprint-i?var [e]
  "Convert an i?var's print representations to an actual i?var."
  (or (when (symbol? e)
        (let [e-name (name e)]
          (and (= \? (first e-name)) ; It's a ?var (should be an i?var).
               (when-let [pos (str/index-of e-name \:)]
                 (let [index (read-string (subs e-name (inc pos)))
                       ?var (read-string (subs e-name 0 pos))]
                   (->I?var index ?var))))))
      e))

(defn unprint-i?vars [expr]
  "Convert i?vars' print representations in `expr` to actual
   i?vars---making it easier to execute expressions copied from
   Clojure execution traces."
  (postwalk unprint-i?var expr))

;;; Matches anything, binds nothing.
(defn- anonymous-i?var? [e]
  (and (i?var? e)
       (let [var-string (name (:?var e))]
         (or (= "?" var-string)
             (= \_ (second var-string))))))

(defn- anonymous-?var? [e]
  (and (?var? e)
       (let [var-string (name e)]
         (or (= "?" var-string)
             (= \_ (second var-string))))))

;;; Let's just use `(->I?var index ?var)`.
;;; (defn- make-I?var [index ?var]
;;;   (->I?var index ?var))

(defn- ?var-binding [bindings index ?var]
  (let [env (get bindings index)]
    (get env ?var 'none)))

;;; De-reference a ?var or a term (or a clause, ...).
(defn- de-reference
  ([bindings term]
   (de-reference bindings term false))
  ([bindings term unindexed?]
   ;; Stop when you get to a non-?var or to a ?var with no binding.
   ;; Per the "push-up" strategy, we should never have to traverse
   ;; more than one hop of indirection here.
   (let [is-?var? (if unindexed? ?var? i?var?)
         var-binding (fn [the-var]
                       (if unindexed?
                         (get bindings the-var 'none)
                         (let [[index ?var] (vals the-var)]
                           (?var-binding bindings index ?var))))
         val (if (is-?var? term)
               (var-binding term)
               term)]
     (cond (= val 'none)
           term

           (is-?var? val)
           (de-reference bindings val unindexed?)
           
           (and (or (seq? val) (vector? val))
                (not (empty? val)))
           ;; `&` never is bound, directly, could be nested.
           (let [seq-result (if (= '& (first val)) 
                              (let [twoth (second val)]
                                (if (is-?var? twoth)
                                  (let [twoth-binding (var-binding twoth)]
                                    (if (= twoth-binding 'none)
                                      `(~'& ~twoth)
                                      (if-not (is-?var? twoth-binding)
                                        ;; Get the value.
                                        (de-reference bindings twoth-binding unindexed?)
                                        ;; Retain `&`.
                                        `(~'& ~@(de-reference bindings twoth-binding unindexed?)))))
                                  ;; `(not (is-?var? twoth))`
                                  ;; De-reference, in case of transparent term.
                                  `(~(de-reference bindings twoth unindexed?))))
                              ;; `(not= '& (first val))`: Map normally.
                              `(~(de-reference bindings (first val) unindexed?)
                                ~@(de-reference bindings (rest val) unindexed?)))]
             (if (seq? val) seq-result (vec seq-result)))
           
           :else 
           ;; We have hit a non-?var thing we don't traverse.
           val))))

;;; Used in logic transform application.
(defn- de-reference-unindexed [bindings term]
  (de-reference bindings term :unindexed))

(defmacro ^:private walk-exprs [predicate handler expr]
  `(postwalk (fn [~'expr]
               (if (~predicate ~'expr)
                 (~handler ~'expr)
                 ~'expr))
             ~expr))

(defn- i?vars-of [expr]
  (let [vars (atom #{})]
    ;; Here we're generating a nonsense expr version that we
    ;; discard...
    (walk-exprs i?var?
                #(swap! vars conj %) ; ...for this effect.
                expr)
    @vars))

(defn- ?vars-of [expr]
  (let [vars (atom #{})]
    (walk-exprs ?var?
                #(swap! vars conj %)
                expr)
    @vars))

(defn- ground?
  ([expr]
   (not (seq (i?vars-of expr))))
  ([expr unindexed?]
   (if unindexed?
     (not (seq (?vars-of expr)))
     (ground? expr))))

;;; When exiting a successful assertion (see Search section), we need
;;; to process any exported ?vars (as defined in `./architecture.md`).

;;; FUTURE: Support multiple parallel threads.
(def ^:private ^:dynamic *unbound-var-counter* (atom 0))

(defn- new-unbound-?var
  ([]
   (new-unbound-?var '?unbound))
  ([root-symbol]
   (let [counter @*unbound-var-counter*]
     (swap! *unbound-var-counter* inc)
     (read-string (cl-format nil "~a-~d" root-symbol counter)))))

(defn- register-unbound-?var [?var-renamings index term-?var]
  (let [renamed-i?var (if (re-matches #"\?unbound-\d*" (name term-?var))
                        ;; Respect existing (unique) name, update
                        ;; index.
                        (->I?var index (:?var term-?var))
                        (or (get ?var-renamings term-?var)
                            (->I?var index (new-unbound-?var))))
        ?var-renamings (assoc ?var-renamings term-?var renamed-i?var)]
    ?var-renamings))

(defn- update-?var-renamings [index term-i?vars ?var-renamings]
  (if (empty? term-i?vars)
    ?var-renamings
    (let [term-i?var (first term-i?vars)
          term-i?vars (rest term-i?vars)
          term-?var (:?var term-i?var)
          ?var-renamings (register-unbound-?var ?var-renamings
                                                index
                                                term-?var)]
      (update-?var-renamings index term-i?vars ?var-renamings))))

(defn- get-i?var-value [bindings i?var]
  (let [[index ?var] (vals i?var)
        env (get bindings index {})
        binding (get env ?var 'none)]
    binding))

(defn- assoc-i?var-binding
  ([bindings i?var val?]
   (assoc-i?var-binding bindings i?var val? false))
  ([bindings i?var val overwrite?]
   (let [[index ?var] (vals i?var)
         env (or (get bindings index) {})
         env (let [existing (get env ?var 'none)]
               (if (or (= existing 'none) ; Respect (don't overwrite) user `nil`.
                       (i?var? existing)
                       overwrite?)
                 (assoc env ?var val)
                 env))]
     (assoc bindings index env))))

(defn- rename-exported-?vars
  [bindings reference-i?var assn-index update-val ?var-renamings]
  (if (or (seq? update-val) (vector? update-val))
    ;; Replace i?vars at `reference-index` that are contained in complex
    ;; assertion terms and left unbound upon successful assertion
    ;; exit.  (Any assertion ?vars that were bound matched the goal,
    ;; so can be ignored, as can any that were left unbound but were
    ;; not contained in complex terms.)
    (let [term update-val
          term-i?vars (i?vars-of term)
          ;; Retain only ?vars at assn-index.
          term-i?vars (filter #(= assn-index (:index %)) term-i?vars)
          reference-index (:index reference-i?var)
          ?var-renamings (update-?var-renamings reference-index
                                                term-i?vars
                                                ?var-renamings)
          renamed-term (walk-exprs i?var?
                                   #(or (get ?var-renamings (:?var %))
                                        %)
                                   (de-reference bindings term))]
      (assoc-i?var-binding bindings reference-i?var renamed-term
                           :overwrite))
    bindings))

(defn- rename-unbound-?vars
  ([assn-index bindings]
   (let [goal-index (dec assn-index)
         goal-env (get bindings goal-index {})
         ;; Ensure consistent renamings across exported ?var
         ;; occurrences, by recording these in `?var-renamings`.
         ?var-renamings {}
         bindings (rename-unbound-?vars assn-index
                                        goal-index
                                        bindings goal-env
                                        ?var-renamings)]
     bindings))
  ([assn-index goal-index bindings goal-env ?var-renamings]
   (if (empty? goal-env)
     bindings
     (let [goal-binding (first goal-env) ; [?var val]
           goal-env (rest goal-env)
           goal-?var (first goal-binding)
           goal-val (second goal-binding)
           ;; Handle the i?var "push-up" strategy.
           reference-i?var (if (i?var? goal-val)
                             goal-val
                             (->I?var goal-index goal-?var))
           update-val (if (i?var? goal-val)
                        (get-i?var-value bindings goal-val)
                        goal-val)]
       (let [bindings (rename-exported-?vars bindings
                                             reference-i?var
                                             assn-index
                                             update-val
                                             ?var-renamings)]
         (rename-unbound-?vars assn-index goal-index bindings goal-env
                               ?var-renamings))))))

;;; Goals always have indices lesser by 1 than the assertions they're
;;; unified with.  Not so for `same` forms...
;;;
;;; In `evals?-from` form, we unify left- (reference) and
;;; right-hand (evaluated) subforms---not `goal-form`,
;;; `assn-form`. (misnomers, strictly)
;;;
;;; Called when at least one of `goal-form`, `assn-form` is an i?var.
(defn- i?var-updated-bindings [bindings goal-form assn-form]
  (if (i?var? assn-form)
    (if-not (i?var? goal-form)
      ;; Write concrete `goal-form` to `assn-form` i?var.
      (assoc-i?var-binding bindings assn-form goal-form)
      ;; `(i?var? goal-form)`
      (let [goal-value (get-i?var-value bindings goal-form)]
        (if (= goal-value 'none)
          ;; Write the goal i?var to the assn i?var.
          ;; (Leave the goal i?var blank.  We know nothing concrete,
          ;; yet.)
          (assoc-i?var-binding bindings assn-form goal-form)
          ;; For clarity, leaving this as an `if` with identical
          ;; actions, different comments.
          (if (i?var? goal-value)
            ;; There is already a (lesser-indexed) "reference" i?var
            ;; pointed to by the goal i?var.  Push our value up the
            ;; stack by recording the reference i?var as our value.
            (assoc-i?var-binding bindings assn-form goal-value)
            ;; `(not (i?var? goal-value))`
            ;; Push a concrete value up, also.
            (assoc-i?var-binding bindings assn-form goal-value)))))
    ;; `(not (i?var? assn-form))`
    ;; We must have `(i?var? goal-form)`, to have been called.
    (let [goal-value (get-i?var-value bindings goal-form)]
      (if (= goal-value 'none)
        (assoc-i?var-binding bindings goal-form assn-form)
        ;; `(not= goal-value 'none)`
        ;; We must have `(i?var? goal-value)`.
        ;; Write assn-form to (lesser-indexed) goal i?var.
        (assoc-i?var-binding bindings goal-value assn-form)))))

;;; The symmetry here supports subsumption operations over the results
;;; of unindexed unification.
(defn- updated-bindings [[env-a env-b] a b]
  (let [env-a (if (?var? a)
                (assoc env-a a b)
                env-a)
        env-b (if (?var? b)
                (assoc env-b b a)
                env-b)]
    [env-a env-b]))

(defn- like-rest [seq-or-vec]
  (if (vector? seq-or-vec)
    (vec (rest seq-or-vec))
    (rest seq-or-vec)))

(defn- unify
  ([a b] ; Terms (or clauses, assertions, ...).
   (unify a b [{} {}]))
  ([a b bindings]
   (unify a b bindings false))
  ([a b bindings indexed?]
   (let [is-?var? (if indexed? i?var? ?var?)
         is-anonymous-?var? (if indexed? anonymous-i?var? anonymous-?var?)
         updated (if indexed? i?var-updated-bindings updated-bindings)]
     ;; (do (pprint "unify:") (pprint bindings) (pprint a) (pprint b))
     (if (or (and (= a []) (= b []))
             (and (= a ()) (= b ())))
       bindings
       ;; Recursion bottoms out (or we started empty).  We don't unify
       ;; seqs with vecs.  Return bindings.
       (cond 
         ;; Discard any anonymous ?vars.
         (or (is-anonymous-?var? a) (is-anonymous-?var? b))
         bindings
         
         ;; Bind any ?vars.
         (or (is-?var? a) (is-?var? b))
         (updated bindings a b)

         ;; Look inside vectors and sequences.
         (or (and (vector? a) (vector? b))
             (and (seq? a) (seq? b)))
         (let [[a-head a-tail] [(first a) (like-rest a)]
               [b-head b-tail] [(first b) (like-rest b)]]
           (cond (and (= a-head '&) (= b-head '&))
                 (unify a-tail b-tail bindings indexed?)

                 (= a-head '&)
                 (unify (first a-tail) ; `(& ?rest)` ==> `?rest`
                        b bindings indexed?)

                 (= b-head '&)
                 (unify a (first b-tail) bindings indexed?)

                 :else
                 (let [bindings (unify a-head b-head bindings indexed?)]
                   (when bindings
                     (unify (de-reference bindings a-tail (not indexed?))
                            (de-reference bindings b-tail (not indexed?))
                            bindings indexed?)))))

         ;; Treat anything else as atomic.
         :else
         (when (= a b)
           bindings))))))

(defn- i?var-unify [a b bindings]
  (unify a b bindings :indexed))

;;;;; Unification ^^
;;;;; ----------------------------------------------------------------
;;;;; Answer processing:

(def ^:private ^:dynamic *answers*)
(def ^:private ^:dynamic *answer-template*)
(def ^:private ^:dynamic *query-i?vars*)
(def ^:dynamic *answer-count-limit*
  "When truthy, terminate query execution upon having recorded (positive
  integer) `*answer-count-limit*` answers."
  nil)
(def ^:private ^:dynamic *answers-countdown*)
(def ^:dynamic *discard-subsumed-answers*
  "When truthy, during query execution discard answers subsumed by other
  answers."
  true)

;;; The following checks won't work on answers including ?var-bearing
;;; maps or sets.  They all assume that `a` and `b` unify, per `env-a`
;;; and `env-b` (which considers only seqs and vecs).

;;; You're subsumed if every one of your ?vars binds a ?var that binds
;;; you.  (There could be other ?vars binding your non-?var parts.)
(defn- subsumes? [env-a env-b] ; Unindexed.
  (every? (fn [[?var-b val-b]]
            (= (get env-a val-b) ?var-b))
          env-b))

(defn- duplicates? [env-a env-b]
  (and (subsumes? env-a env-b)
       (subsumes? env-b env-a)))

(defn- adjudication-status [new existing]
  (let [envs (unify new existing)]
    (if-not envs
      :different
      ;; Else they match.
      (let [[env-new env-existing] envs
            new-subsumes? (subsumes? env-new env-existing)
            existing-subsumes? (subsumes? env-existing env-new)
            duplicates? (and new-subsumes? existing-subsumes?)]
        (if duplicates?
          :equivalent
          (if existing-subsumes?
            :subsumes
            (if new-subsumes?
              :subsumed
              ;; Else they unify, without subsumption.
              :disjoint)))))))

(defn- remove-subsumed-answers [answers adjudications]
  (vec (mapcat (fn [answer adjudication]
                 (if (= adjudication :subsumed)
                   []
                   [answer]))
               answers
               adjudications)))

(defn- record-answer [answer]
  (swap! *answers* conj answer)
  (when *answers-countdown*
    (swap! *answers-countdown* dec)))

(defn- adjudicate-answer [answer]
  ;; Does `answer` unify with any existing answer?  If so, then...
  ;;
  ;; - Duplicate answer if ?vars get bound to ?vars, only (technicaly,
  ;;   subsumes both ways).
  ;;
  ;; - One-way ?var binding is strict subsumption.  If by new answer,
  ;;   how many existing answers are subsumed?
  ;;
  ;; - Unique answer if ?vars get bound to non-?vars in both
  ;;   directions.
  ;;
  ;; If not, then answer is unique.
  ;;
  ;; We must check existing answers one at a time.  (Consider
  ;; standardizing answers' ?vars, storing all existing answers in a
  ;; trie?  This would work for duplicate checking, not for strict
  ;; subsumption.)
  (let [answers @*answers*]
    (if (empty? answers)
      (do (record-answer answer)
          :different)
      (let [adjudications (map #(adjudication-status answer %)
                               answers)]
        (if (some #(= % :equivalent) adjudications)
          :equivalent ; Discard (leave *answers* as is).
          (if-not *discard-subsumed-answers*
            ;; Not a duplicate and not checking subsumption.
            (record-answer answer)
            ;; Else check subsumption.
            (if (some #(= % :subsumes) adjudications)
              :subsumed ; Discard subsumed answer.
              (if (some #(= % :subsumed) adjudications)
                ;; Remove subsumed existing answers...
                (let [former-count    (count answers)
                      answers         (remove-subsumed-answers answers
                                                       adjudications)
                      present-count   (count answers)
                      count-reduction (- former-count present-count)
                      ;; ...and add the new one.
                      answers         (conj answers answer)]
                  (reset! *answers* answers)
                  (when *answers-countdown*
                    (swap! *answers-countdown* - count-reduction))
                  ;; Return the number subsumed.
                  count-reduction)
                ;; Else nothing to report.  (Treat `:disjoint` like
                ;; `:different`.)
                (do (record-answer answer)
                    :different)))))))))

(def ^:dynamic *leash*
  "When truthy, during query execution, write informative reports to
  standard output."
  false)

(defn- handle-answer [bindings]
  ;; Not penetrating sets, maps, ...  Consider walking?
  (let [answer (de-reference bindings *answer-template*)
        answer (unindexify answer 0)]
    (let [adjudication (adjudicate-answer answer)]
      ;; Display answer info.
      (when *leash*
        (case adjudication
          ;; FUTURE: Print literal answers (e.g., "quoted strings").
          nil (println "Recorded answer:" answer) ; Happens when not discarding subsumed.
          :different (println "Recorded answer:" answer)
          :equivalent (println "Duplicate answer (not recorded):" answer)
          :subsumed (println "Subsumed answer (not recorded):" answer)
          ;; FUTURE: Say which answers were discarded?  Store them somewhere?
          (println (cl-format nil
                              "Recorded subsuming answer (discarded ~d subsumed answer(s)): "
                              adjudication)
                   answer))))))

;;;;; Answer extraction ^^
;;;;; ----------------------------------------------------------------
;;;;; Search---leashing, stack machine, querying:

(comment ; When we were using Riddley, before replacing that with
         ; `postwalk`:
  ;; In order to quote symbols (or whatever) for export from logic to
  ;; Lisp, we need a version of `quote` that our walker will traverse
  ;; and (per specs in the next two functions) not macroexpand.
  (defmacro kwote [x] (list 'quote x)))

(defn- indexify [thing index]
  ;; It's nice for us that Riddley won't penetrate our i?vars.
  ;; It's not so nice that Riddley expands all except specified macros.
  (walk-exprs ?var? #(->I?var index %) thing))

(defn- unindexify [thing index]
  (walk-exprs (fn [expr]
                (and (i?var? expr)
                     (= (:index expr) index)))
              #(:?var %)
              thing))

(defn- leash-pad [special-form-depth index]
  (apply str (repeat (+ index special-form-depth)
                     \space)))

(defn- leash-prefix [special-form-depth index]
  (let [pad (leash-pad special-form-depth index)
        prefix (str pad index \.)]
    prefix))

(defn- goal-signature [goal]
  (if-not (?var? goal)
    (str (pr-str (first goal)) "/" (dec (count goal)))
    (pr-str goal)))

(defn- leash-->?-transform [special-form-depth index]
  (when *leash*
    (let [pad (leash-pad special-form-depth index)]
      (println pad "Applied ->? transform"))))

(defn- leash-assertion-success [special-form-depth index head bindings]
  (when (and head *leash*) ; Top-level query has no head.
    (let [prefix (leash-prefix special-form-depth index)
          signature (goal-signature head)]
      (println prefix "Succeeded" (str (pr-str signature) \:)
               (de-reference bindings head)))))

(defn- leash-assertion-body [special-form-depth assn-index head body goal bindings]
  (comment ; Disable.
    (when (and goal *leash*)
      (let [[bindings> bindings<] bindings
            ;; goal-prefix (leash-prefix (inc assn-index))
            assn-prefix (leash-prefix special-form-depth assn-index)]
        ;; (println assn-prefix "bindings>:" bindings>)
        ;; (println assn-prefix "bindings<:" bindings<)
        (if head 
          (println assn-prefix "Working on goal"
                   (cl-format nil "~s:" goal)
                   (de-reference bindings goal))
          ;; Nothing to de-reference at top level.
          (println assn-prefix "Working on goal" goal))
        (println assn-prefix "Remaining goals:"
                 ;; Filter out private goals.
                 (remove #(private-built-in-special-head? (first %))
                         (de-reference bindings body)))))))

(defn- leash-assertion-head [special-form-depth assn-index head goal bindings]
  (when (and head goal *leash*)
    (let [; goal-prefix (leash-prefix (inc assn-index))
          assn-prefix (leash-prefix special-form-depth assn-index)]
      ;; (println goal-prefix "bindings>:" bindings>)
      ;; (println goal-prefix "bindings<:" bindings<)
      (println assn-prefix "Matched head"
               (cl-format nil "~s:" head)
               (de-reference bindings head)))))

(defn- leash-assertion-backtracking [special-form-depth index goal bindings]
  (when *leash*
    (let [prefix (leash-prefix special-form-depth index)
          goal (de-reference bindings goal)
          signature (goal-signature goal)]
      (println prefix "Backtracking into" (str (pr-str signature) \:)
               goal))))

(defn- leash-failure [special-form-depth index goal bindings]
  (when *leash*
    (let [prefix (leash-prefix special-form-depth index)
          goal (de-reference bindings goal)
          signature (goal-signature goal)]
      (println prefix "Failed" (str (pr-str signature) \:)
               goal))))

(defn- leash-goal [special-form-depth index goal bindings]
  (when (and goal *leash*)
    (let [prefix (leash-prefix special-form-depth index)
          goal (de-reference bindings goal)
          signature (goal-signature goal)]
      (println prefix "Entering" (str (pr-str signature) \:)
               goal))))

(defn- standard-split
  "Split `s` at whitespace chars, returning a vec of (unnormalized)
  tokens."
  [s]
  (str/split (str/triml s) #"\s+"))

(defn- backtracking-leash-report? [leash-report index]
  (and (string? leash-report)
       (.contains leash-report (str index ". " "Backtracking"))))

;;; A "special" stack frame (for a goal headed by a special predicate)
;;; will not have assertions.

(defrecord ^:private
           StackFrame [leash-report ; String.
                       head ; The clause head associated (via clause) with `goals`.
                       goal-index
                       goal
                       assertion-matches ; Remaining assertion matches.
                       special-form-stack ; Per assertion (or query) goals.
                       special-form-depth ; Global/stack-wide.*
                       body-remainders ; Body continuations.  FIFO.
                       bindings
                       ;; Next assertion, or (if none) previous goal, or (if none) see caller.
                       continuation ; For failure.
                       ])
;;; * This accounts for depth across all frames (including
;;; parents)---not just within an assertion.  Consider `(or (and
;;; <clause>*)*)`, where any embedded <clause> may in its body invoke
;;; a similar conditional.

;;; We have some macros that let us avoid a lot of typing/source code
;;; repetition.  The functions that use these macros all respect the
;;; local names established here.

(defmacro ^:private with-stack-frame [stack-frame & body]
  `(let [~'leash-report (:leash-report ~stack-frame)
         ~'head (:head ~stack-frame)
         ~'goal-index (:goal-index ~stack-frame)
         ~'goal (:goal ~stack-frame)
         ~'assn-index (inc (:goal-index ~stack-frame))
         ~'assertion-matches (:assertion-matches ~stack-frame)
         ~'special-form-stack (:special-form-stack ~stack-frame)
         ~'special-form-depth (:special-form-depth ~stack-frame)
         ~'body-remainders (:body-remainders ~stack-frame)
         ~'bindings (:bindings ~stack-frame)
         ~'continuation (:continuation ~stack-frame)]
     ~@body))

(defmacro ^:private gather-stack-frame []
  '(->StackFrame leash-report
                 head
                 goal-index
                 goal
                 assertion-matches
                 special-form-stack
                 special-form-depth
                 body-remainders
                 bindings
                 continuation))

(defrecord ^:private 
           BodyRemainder [capos ; Tells us which `process-...` functions have written here.
                          head ; The head associated (via clause) with this body.
                          body-index
                          goals ; Remaining goals.
                          ;; A stack of the (complete) logic forms
                          ;; we've visited up to this point, in
                          ;; processing the present assertion.
                          special-form-stack
                          special-form-depth])

(defmacro ^:private with-body-remainder [body-remainder & body]
  `(let [~'capos (:capos ~body-remainder)
         ~'head (:head ~body-remainder)
         ~'body-index (:body-index ~body-remainder)
         ~'goals (:goals ~body-remainder)
         ~'special-form-stack (:special-form-stack ~body-remainder)
         ~'special-form-depth (:special-form-depth ~body-remainder)]
     ~@body))

(defmacro ^:private gather-body-remainder []
  '(->BodyRemainder capos head body-index goals special-form-stack special-form-depth))

;;; This requires `body-remainders` and `goals` to have values.
(defmacro ^:private gathering-body-remainder [& body]
  `(let [~'capos (cons ~'capo ~'capos)
         ~'body-remainder (when (seq ~'goals)
                            (gather-body-remainder))
         ~'body-remainders (if ~'body-remainder
                             (cons ~'body-remainder ~'body-remainders)
                             ~'body-remainders)]
     ~@body))

;;; Should be private in production.
(def ^:private debugging-stack nil)

(declare process-stack-frame)

;;; FUTURE: Add indices within open-arity forms: `and`, `or`, `case[*, !]`.
(defn- operator-leash-prefix [special-form-depth index special-form-stack]
  (let [logic-path (reverse (map first special-form-stack))
        pad (leash-pad special-form-depth index)]
    (str pad (cl-format nil "~s:" logic-path))))

(defn- leash-special [special-form-depth index verb special-form-stack bindings]
  (when *leash*
    (let [prefix (operator-leash-prefix special-form-depth index special-form-stack)
          logic-form (de-reference bindings (first special-form-stack))]
      (println prefix verb (cl-format nil "~s" logic-form)))))

;;; We don't need `leash-special "Backtracking into"` for `and`.  We'll
;;; backtrack on the conjuncts, individually (when these have `or` or
;;; user predicates).

;;; In arriving here, we've not disturbed `body-remainders`.  So, we
;;; could just append the conjuncts.  However, for leashing purposes,
;;; we'd like to know when we're done with the `and`.  Such
;;; considerations are manifold among these `process-...` functions.
(defn- process-and-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-and-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [and-form goal
          operator (first and-form)
          capo (cons operator (map first (rest and-form)))
          and-goals (rest and-form) ; Lose operator.
          goal (first and-goals) ; Gathered into stack frame.
          ;; Ok, even if not looking at a predicate goal:
          assertion-matches (get-assertion-matches assn-index goal bindings)
          and-goals (rest and-goals)
          stack-frame-special-form-stack special-form-stack
          stack-frame-special-form-depth special-form-depth
          continuation (if (= operator 'and)
                         (assoc continuation :leash-report
                                (str (with-out-str (leash-special special-form-depth
                                                                  goal-index "Failed"
                                                                  special-form-stack
                                                                  bindings))
                                     (:leash-report continuation)))
                         continuation)]
      (when (= operator 'and)
        ;; Original source form---not our repetition (`and...`).
        (leash-special special-form-depth goal-index "Entering" special-form-stack bindings))
      (let [body-remainder (or (first body-remainders)
                               (let [capos ()
                                     goals nil
                                     body-index goal-index]
                                 (gather-body-remainder)))
            body-remainders (rest body-remainders)]
        (if (seq goal) ; `and-form` was not degenerate, on entry.
          ;; Add conjunction remainder to this assertion's body
          ;; remainder.
          (with-body-remainder body-remainder
            (let [operator (if (= operator 'and)
                             'and...
                             operator) ; Works for `sys-and`.
                  and-form `(~operator ~@and-goals)
                  goals `(~and-form ~@goals)
                  special-form-stack stack-frame-special-form-stack
                  special-form-depth stack-frame-special-form-depth]
              (gathering-body-remainder
               #(process-stack-frame (gather-stack-frame)))))
          ;; Empty conjunction---degenerate on entry.  Forget this
          ;; `and` form and move on to other goals of assertion.
          ;; Compare to `succeed-simple-special-form`...
          (do (when-not (= operator 'sys-and)
                (leash-special special-form-depth goal-index "Succeeded" special-form-stack bindings))
            (if (seq body-remainder)
              (with-body-remainder body-remainder
                (let [capos (cons capo capos)
                      goal (first goals)
                      assertion-matches (get-assertion-matches assn-index goal bindings)
                      goals (rest goals) ; Gathered into body remainder.
                      ;; FYI: continuation continuation
                      special-form-stack (if (= operator 'and...)
                                           (rest special-form-stack)
                                           special-form-stack)
                      special-form-depth (if (= operator 'and...)
                                           (dec special-form-depth)
                                           special-form-depth)
                      body-remainder (gather-body-remainder)
                      body-remainders (cons body-remainder body-remainders)]
                  #(process-stack-frame (gather-stack-frame))))
              #(process-stack-frame continuation))))))))

(defn- process-or-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-or-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [or-form goal
          operator (first or-form)
          capo (cons operator (map first (rest or-form)))
          or-goals (rest or-form) ; Lose operator.
          goal (first or-goals) ; Gathered into stack frame.
          ;; `nil`, if not looking at a predicate goal:
          assertion-matches (when-not assertion-matches ; Respect an empty coll.
                              (get-assertion-matches assn-index goal bindings))
          or-goals (rest or-goals)
          outer-special-form-stack special-form-stack
          outer-special-form-depth special-form-depth
          or-form (when goal
                    ;; Restore `or...` (our repetition).
                    (cons 'or... or-goals))
          continuation (if or-form
                         (let [goal or-form
                               assertion-matches nil]
                           (gather-stack-frame))
                         continuation)]
      (if (= operator 'or)
        ;; Original source form---not our repetition (`or...`).
        (leash-special special-form-depth goal-index "Entering" special-form-stack bindings)
        (when (seq goal)
          (leash-special special-form-depth goal-index "Backtracking into" special-form-stack bindings)))
      (if (seq goal)
        (if (seq body-remainders)
          (let [body-remainder (first body-remainders)
                body-remainders (rest body-remainders)
                leash-report (if (= operator 'or)
                               (str (with-out-str
                                      (leash-special
                                       outer-special-form-depth
                                       goal-index "Succeeded"
                                       outer-special-form-stack bindings))
                                    leash-report)
                               leash-report)
                body-remainder (assoc body-remainder :leash-report leash-report)
                body-remainders (cons body-remainder body-remainders)]
            #(process-stack-frame (gather-stack-frame)))
          #(process-stack-frame (gather-stack-frame)))
        ;; We have an empty disjunction.  Fail.
        (do (leash-special special-form-depth goal-index "Failed" special-form-stack bindings)
            #(process-stack-frame continuation))))))

(defmacro ^:private process-answer-and-continue []
  `(do (handle-answer ~'bindings)
       #(process-stack-frame ~'continuation)))

;;; `and`, `or` are too idiomatic for this.
(defmacro ^:private succeed-simple-special-form []
  `(let [~'body-remainder (first ~'body-remainders)]
     (if (seq ~'body-remainder)
       (with-body-remainder ~'body-remainder
         (let [~'body-remainders (rest ~'body-remainders)
               ~'goal (first ~'goals)
               ~'goals (rest ~'goals)]
           (gathering-body-remainder
            #(process-stack-frame (gather-stack-frame)))))
       #(process-answer-and-continue))))

(defn- process-fail-first-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-fail-first-frame" stack-frame]))
  (with-stack-frame stack-frame
    (leash-special special-form-depth goal-index "Failed" special-form-stack bindings)
    #(process-stack-frame continuation)))

(defn- process-succeed-first-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-succeed-first-frame" stack-frame]))
  (with-stack-frame stack-frame
    (leash-special special-form-depth goal-index "Succeeded, cutting" special-form-stack bindings)
    (let [capo 'succeed-first
          ;; leash-report ""
          continuation (second goal)]
      ;; Specialization of...
      ;; (succeed-simple-special-form)
      (let [body-remainder (first body-remainders)]
        (if (seq body-remainder)
          (with-body-remainder body-remainder
            (let [special-form-stack (rest special-form-stack)
                  ;; ^^ Lose the `if` form we're succeeding from. vv
                  special-form-depth (dec special-form-depth)
                  body-remainders (rest body-remainders)
                  goal (first goals)
                  goals (rest goals)]
              (gathering-body-remainder
               #(process-stack-frame (gather-stack-frame)))))
          #(process-answer-and-continue))))))

;;; FUTURE: Document: Note that "cut" renders ineffective (at least,
;;; potentially wasteful---ultimately disregarded) "or" parallelism
;;; within the scope of its choice point.
(defn- process-first-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-first-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [capo 'first
          first-goal (second goal)
          ;; `first` continuation frame:
          goal '(fail-first)
          ;; Already so: assertion-matches nil
          continuation (gather-stack-frame)
          ;; `first` content frame:
          goal first-goal
          assertion-matches (get-assertion-matches goal-index goal bindings)
          body-remainder (first body-remainders)
          capos (:capos body-remainder)
          goals `((~'succeed-first ~continuation)
                  ~@(:goals body-remainder))
          body-index goal-index
          body-remainders (cons (gather-body-remainder) (rest body-remainders))
          body-index goal-index]
      (leash-special special-form-depth goal-index "Entering first" special-form-stack bindings)
      #(process-stack-frame (gather-stack-frame)))))

;;; We employ several pseudo-frames for `if`, towards managing
;;; leashing.  Perhaps simpler (idea): Make process-stack-frame deal
;;; with leash messages directly, rather than embedding them in stack
;;; frames.

(defn- process-fail-if-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-fail-if-frame" stack-frame]))
  (with-stack-frame stack-frame
    (leash-special special-form-depth goal-index "Failed" special-form-stack bindings)
    #(process-stack-frame continuation)))

(defn- process-succeed-if-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-succeed-if-frame" stack-frame]))
  (with-stack-frame stack-frame
    (leash-special special-form-depth goal-index "Succeeded" special-form-stack bindings)
    (let [capo 'succeed-if]
      ;; Specialization of...
      ;; (succeed-simple-special-form)
      (let [body-remainder (first body-remainders)]
        (if (seq body-remainder)
          (with-body-remainder body-remainder
            (let [special-form-stack (rest special-form-stack)
                  ;; ^^ Lose the `if` form we're succeeding from. vv
                  special-form-depth (dec special-form-depth)
                  body-remainders (rest body-remainders)
                  goal (first goals)
                  goals (rest goals)]
              (gathering-body-remainder
               #(process-stack-frame (gather-stack-frame)))))
          #(process-answer-and-continue))))))

;;; Unpile piled continuations, post-slice.
(defn- process-else-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-else-frame" stack-frame]))
  (with-stack-frame stack-frame
    ;; FUTURE: Have leash print at most the else branch.
    (leash-special special-form-depth goal-index "Taking 'else' branch of" special-form-stack bindings)
    (let [capo 'else
          goal (second goal) ; Lose `else`.
          assertion-matches (get-assertion-matches goal-index goal bindings)
          body-remainder (first body-remainders)
          capos (:capos body-remainder)
          goals (cons '(succeed-if) (:goals body-remainder))
          body-remainders (rest body-remainders)
          body-index goal-index]
      (gathering-body-remainder
       #(process-stack-frame (gather-stack-frame))))))

(defn- unpile-continuations [pile stack-frame]
  (if (not (seq pile))
    stack-frame
    (unpile-continuations (pop pile)
                          (assoc (peek pile) :continuation stack-frame))))

(comment
  "FUTURE: Better idea (?):
    [Optional: Start using vec (rather than nested linked list) for continuations.
     We will be conjing to vec end.]
    Store cut-frame index in `drop-else` clause.
    If you don't find it there, it's already gone.
    If you do find it, slice it out.
    Constant time---no more searching.")
(defn- splice-out-continuation
  ([continuation cut-frame]
   (let [dropped (splice-out-continuation continuation cut-frame [])]
     (if (= dropped :missing)
       continuation ; The cut frame already was dropped.
       dropped))) ; We've just cut it here.
  ;; Toss stack frames on a pile, until we find the one that has our
  ;; continuation we want to drop.
  ([continuation
    cut-frame
    pile] ; Reversed vec of visited stack frames.
   (if (:final continuation)
     ;; FUTURE: This treatment is inefficient.  Use "better idea,"
     ;; above, to avoid memory leak exposure in a TRO situation.
     :missing ; We've already dropped this continuation.
     (if (identical? continuation cut-frame)
       ;; Reverse the pile, stacking back onto continuation after
       ;; slicing out the one dropped.
       (unpile-continuations
        pile
        ;; Slice out the `else` continuation.
        (:continuation continuation))
       (splice-out-continuation (:continuation continuation)
                               cut-frame
                               (conj pile continuation))))))

(defn- process-drop-else-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-drop-else-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [capo 'drop-else
          else-frame (second goal)
          ;; Unnecessary: assertion-matches nil
          continuation (splice-out-continuation continuation else-frame)
          body-remainder (first body-remainders) ; Has at least `(succeed-if)`.
          capos (:capos body-remainder)
          goal '(succeed-if) ; Simplify `(sys-and (succeed-if))`.
          goals (rest (:goals body-remainder))
          body-remainders (rest body-remainders)
          body-index goal-index]
      (gathering-body-remainder
         #(process-stack-frame (gather-stack-frame))))))

(defn- process-then-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-then-frame" stack-frame]))
  (with-stack-frame stack-frame
    ;; FUTURE: Have leash print at most the then branch.
    (leash-special special-form-depth goal-index "Taking 'then' branch of" special-form-stack bindings)
    (let [capo 'then
          goal (second goal) ; Lose `then`.
          assertion-matches (get-assertion-matches goal-index goal bindings)
          body-remainder (first body-remainders) ; Has at least `(drop-else ...)`.
          capos (:capos body-remainder)
          goals (:goals body-remainder)
          body-remainders (rest body-remainders)
          body-index goal-index]
      (gathering-body-remainder
       #(process-stack-frame (gather-stack-frame))))))

(defn- process-if-then-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-if-then-frame" stack-frame]))
  (with-stack-frame stack-frame
    ;; FUTURE: Have leash print at most the condition.
    (leash-special special-form-depth goal-index "Checking 'if' condition" special-form-stack bindings)
    (let [capo 'if-then
          condition-form (nth goal 1) ; Lose `if-then`.
          then-form (nth goal 2)
          then-goal `(~'then ~then-form)
          goal condition-form
          assertion-matches (get-assertion-matches goal-index goal bindings)
          else-frame continuation
          body-remainder (first body-remainders)
          capos (:capos body-remainder)
          goals `((~'sys-and ; System-level `and`.
                   ~then-goal
                   ;; Throw (private) system-level `else-frame` into
                   ;; system-level special predicate `drop-else`.
                   (~'drop-else ~else-frame)
                   (~'succeed-if))
                  ~@(:goals body-remainder))
          body-remainders (rest body-remainders)
          body-index goal-index]
      (gathering-body-remainder
       #(process-stack-frame (gather-stack-frame))))))

(defn- process-if-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-if-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [if-form (nth goal 1) ; (second goal)
          then-form (nth goal 2)
          else-form (nth goal 3)
          ;; We chain some continuation frames here.
          goal '(fail-if)
          fail-if-frame (gather-stack-frame)
          ;; Another frame:
          goal `(~'else ~else-form)
          continuation fail-if-frame
          else-frame (gather-stack-frame)
          ;; Now our initial stack frame:
          goal `(~'if-then ~if-form ~then-form)
          continuation else-frame
          if-then-frame (gather-stack-frame)]
      (leash-special special-form-depth goal-index "Entering" special-form-stack bindings)
      ;; Ok here to bypass `process-stack-frame`, as this is
      ;; deterministic.
      #(process-if-then-frame if-then-frame))))

(declare query)

;;; Note: The answer template in the recursive `query` call is
;;; ?var-free.  Given that this is the only way `query` ever is called
;;; recursively, we can get away with assuming any template's index is
;;; 0.  See `handle-answer`.
(defn- process-not-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-not-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [capo 'not
          not-goal (second goal) ; Lose `not`.
          goal nil ; Gathered.
          not-goal (de-reference bindings not-goal)
          _side-effect (leash-special special-form-depth goal-index "Entering" special-form-stack bindings)
          success? (not (seq (query true `(~not-goal)
                                    :stack-index goal-index
                                    :special-form-stack special-form-stack
                                    :special-form-depth special-form-depth)))]
      (if success?
        (do (leash-special special-form-depth goal-index "Succeeded" special-form-stack bindings)
            (succeed-simple-special-form))
        (do (leash-special special-form-depth goal-index "Failed" special-form-stack bindings)
            #(process-stack-frame continuation))))))

(defn- process-true-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-true-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [capo 'true
          goal nil]
      (leash-special special-form-depth goal-index "Entering" special-form-stack bindings)
      (leash-special special-form-depth goal-index "Succeeded" special-form-stack bindings)
      (succeed-simple-special-form))))

(defn- process-false-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-false-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [goal nil]
      (leash-special special-form-depth goal-index "Entering" special-form-stack bindings)
      (leash-special special-form-depth goal-index "Failed" special-form-stack bindings)
      #(process-stack-frame continuation))))

(defn- process-truthy?-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-truthy?-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [capo 'truthy?
          clojure-form (second goal) ; Lose `truthy?`.
          goal nil ; Gathered.
          clojure-form (de-reference bindings clojure-form)
          _side-effect (leash-special special-form-depth goal-index "Entering" special-form-stack bindings)
          grounded? (ground? clojure-form)
          success? (and grounded? (eval clojure-form))]
      (if success?
        (do
          (leash-special special-form-depth goal-index "Succeeded" special-form-stack bindings)
          (succeed-simple-special-form))
        (let [leash-verb (if grounded?
                           "Failed"
                           "Failed, not ground")]
          (leash-special special-form-depth goal-index leash-verb special-form-stack bindings)
          #(process-stack-frame continuation))))))

(defn- process-var-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-var-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [capo 'var
          clojure-form (second goal) ; Lose `var`.
          goal nil ; Gathered.
          clojure-form (de-reference bindings clojure-form)
          _side-effect (leash-special special-form-depth goal-index "Entering" special-form-stack bindings)]
      (if (i?var? clojure-form)
        (do (leash-special special-form-depth goal-index "Succeeded" special-form-stack bindings)
            (succeed-simple-special-form))
        (do (leash-special special-form-depth goal-index "Failed" special-form-stack bindings)
            #(process-stack-frame continuation))))))

(defn- process-ground-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-ground-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [capo 'var
          clojure-form (second goal) ; Lose `ground`.
          goal nil ; Gathered.
          clojure-form (de-reference bindings clojure-form)
          _side-effect (leash-special special-form-depth goal-index "Entering" special-form-stack bindings)]
      (if (ground? clojure-form)
        (do (leash-special special-form-depth goal-index "Succeeded" special-form-stack bindings)
            (succeed-simple-special-form))
        (do (leash-special special-form-depth goal-index "Failed" special-form-stack bindings)
            #(process-stack-frame continuation))))))

(defn- process-do-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-do-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [capo 'do
          clojure-form goal ; Keep `do`.
          goal nil ; Gathered.
          clojure-form (de-reference bindings clojure-form)]
      (leash-special special-form-depth goal-index "Entering" special-form-stack bindings)
      (if (ground? clojure-form)
        (do (eval clojure-form)
            (leash-special special-form-depth goal-index "Succeeded" special-form-stack bindings)
            (succeed-simple-special-form))
        (do (leash-special special-form-depth goal-index "Failed, not ground" special-form-stack bindings)
            #(process-stack-frame continuation))))))

(defn- process-evals-from?-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-evals-from?-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [capo 'evals-from?
          logic-form (second goal)
          clojure-form (nth goal 2) ; (third goal)
          goal nil ; Gathered.
          logic-form (de-reference bindings logic-form)
          clojure-form (de-reference bindings clojure-form)
          _side-effect (leash-special special-form-depth goal-index "Entering" special-form-stack bindings)]
      (if (ground? clojure-form)
        (let [clojure-result (eval clojure-form)
              ;; In case we introduce any ?vars.  Because we've
              ;; required `clojure-form` to be ground, we needn't
              ;; worry that we'll indexify an i?var.  FUTURE: Consider
              ;; means to rename any ?vars introduced here, as needed.
              clojure-result (indexify clojure-result goal-index)
              bindings? (i?var-unify logic-form clojure-result bindings)]
          (if bindings?
            (do (leash-special special-form-depth goal-index "Succeeded" special-form-stack bindings?)
                (let [bindings bindings?]
                  (succeed-simple-special-form)))
            (do (leash-special special-form-depth goal-index "Failed" special-form-stack bindings)
                #(process-stack-frame continuation))))
        (do (leash-special special-form-depth goal-index "Failed, not ground" special-form-stack bindings)
            #(process-stack-frame continuation))))))

(defn- process-same-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-same-frame" stack-frame]))
  (with-stack-frame stack-frame
    (let [capo 'same
          a-form (second goal)
          b-form (nth goal 2) ; (third goal)
          goal nil ; Gathered.
          a-form (de-reference bindings a-form)
          b-form (de-reference bindings b-form)
          _side-effect (leash-special special-form-depth goal-index "Entering" special-form-stack bindings)
          bindings? (i?var-unify a-form b-form bindings)]
      (if bindings?
        (do (leash-special special-form-depth goal-index "Succeeded" special-form-stack bindings?)
            (let [bindings bindings?]
              (succeed-simple-special-form)))
        (do (leash-special special-form-depth goal-index "Failed" special-form-stack bindings)
            #(process-stack-frame continuation))))))

(defn- apply-predicate-transform [transform form leash-args]
  (let [input-pattern (first transform)
        output-pattern (second transform)
        bindings>< (unify input-pattern form)]
    (if bindings><
      (let [[bindings> _bindings<] bindings><
            [special-form-depth assn-index special-form-stack leash-bindings] leash-args
            output-pattern (de-reference-unindexed bindings> output-pattern)]
        (leash-special special-form-depth assn-index "Applying logic transform"
                  (cons input-pattern special-form-stack)
                  ;; leash-bindings ; Don't de-reference...
                  [{} {}])
        output-pattern)
      'nope)))

;;; TODO: Consider de-referencing form, first (in case some logic
;;; element is there per a ?var binding).
(defn- transform-predicate
  ([form leash-args]
   (let [head (first form)
         transforms (get @*predicate-transforms* head)]
     (transform-predicate form transforms leash-args)))
  ;; Take the first successful transform, or (error,
  ;; really---warn---FUTURE) just return input form.
  ([form transforms leash-args]
   (if-not (seq transforms)
     'no-matching-transform ; Avoid stack overflow.
     (let [transformed (apply-predicate-transform
                        (first transforms) form leash-args)]
       (if (not= transformed 'nope)
         transformed
         (transform-predicate form (rest transforms) leash-args))))))

;;; Ensure `(not (transformable-predicate? (first goal)))`.  I.e.,
;;; apply transforms until you can't (so `process-special-frame` can
;;; exercise its `case` form.
(defn- recursively-transform-predicate [form leash-args]
  (if (not (transformable-predicate? form))
    form
    (let [form (transform-predicate form leash-args)]
      (recursively-transform-predicate form leash-args))))

(defn- process-special-frame [stack-frame]
  (with-stack-frame stack-frame
    (let [leash-args [special-form-depth assn-index special-form-stack bindings]
          goal (recursively-transform-predicate goal leash-args)
          special-head (first goal)
          special-form-stack (if-not (private-built-in-special-head? special-head)
                               (cons goal special-form-stack)
                               special-form-stack)
          special-form-depth (if-not (private-built-in-special-head? special-head)
                               (inc special-form-depth)
                               special-form-depth)
          leash-report "" ; Clear incoming report.
          stack-frame (gather-stack-frame)]
      (case special-head
        ;; Goal-nesting forms:
        first #(process-first-frame stack-frame)
        fail-first #(process-fail-first-frame stack-frame)
        succeed-first #(process-succeed-first-frame stack-frame)
        and #(process-and-frame stack-frame)
        and... #(process-and-frame stack-frame)
        sys-and #(process-and-frame stack-frame)
        or #(process-or-frame stack-frame)
        or... #(process-or-frame stack-frame)
        not #(process-not-frame stack-frame)
        if #(process-if-frame stack-frame)
        if-then #(process-if-then-frame stack-frame)
        then #(process-then-frame stack-frame)
        else #(process-else-frame stack-frame)
        drop-else #(process-drop-else-frame stack-frame)
        fail-if #(process-fail-if-frame stack-frame)
        succeed-if #(process-succeed-if-frame stack-frame)
        ;; Non-nesting forms:
        truthy? #(process-truthy?-frame stack-frame)
        do #(process-do-frame stack-frame)
        evals-from? #(process-evals-from?-frame stack-frame)
        var #(process-var-frame stack-frame)
        ground #(process-ground-frame stack-frame)
        same #(process-same-frame stack-frame)
        true #(process-true-frame stack-frame)
        false #(process-false-frame stack-frame)))))

(defn- process-predicate-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-predicate-frame:" stack-frame]))
  (with-stack-frame stack-frame
    (if-not (seq assertion-matches)
      (do
        (when-not (backtracking-leash-report? (:leash-report stack-frame)
                                              assn-index)
          (leash-goal special-form-depth assn-index goal bindings))
        (leash-failure special-form-depth assn-index goal bindings)
        ;; Backtrack.
        #(process-stack-frame continuation))
      (let [[assertion match-bindings] (first assertion-matches)
            assertion-matches (rest assertion-matches)
            ;; For failure continuation:
            leash-report (with-out-str
                           (leash-assertion-backtracking
                            special-form-depth assn-index goal bindings))
            ;; Use the above backtracking leash report.
            continuation (gather-stack-frame)
            bindings match-bindings
            head (first assertion)]
        (when-not (backtracking-leash-report? (:leash-report stack-frame)
                                              assn-index)
          (leash-goal special-form-depth assn-index goal bindings)
          (leash-assertion-head special-form-depth assn-index head goal bindings))
        ;; Compare to `succeed-simple-special-form`:
        (let [goals (rest assertion)
              goal (first goals)
              capo (first goal) ; Diagnostic.
              capos () ; Diagnostic.
              goals (rest goals)
              goal-index assn-index
              body-index assn-index ; Gathered into body remainder.
              assertion-matches (get-assertion-matches
                                 assn-index goal bindings)
              leash-report (with-out-str
                             ;; (leash-assertion-head assn-index head goals goal bindings)
                             (leash-assertion-body
                              special-form-depth assn-index head goals goal bindings))]
          (gathering-body-remainder
           #(process-stack-frame (gather-stack-frame))))))))

;;; Only standard predicates should call this.
;;; (So, we're not accommodating ?vars introduced by `evals-from?`
;;; forms---which would require `rename-unbound-?vars`).
(defn- process-assertion-success [stack-frame]
  (when debugging-stack
    (pprint ["process-assertion-success:" stack-frame]))
  (with-stack-frame stack-frame
    (leash-assertion-success special-form-depth goal-index head bindings)
    (let [capo 'process-assertion-success
          bindings (rename-unbound-?vars goal-index bindings)]
      (if (empty? body-remainders)
        #(process-answer-and-continue)
        ;; From the first remainder, pop off one goal for the stack
        ;; frame.
        (let [body-remainder (first body-remainders)
              body-remainders (rest body-remainders)]
          (with-body-remainder body-remainder
            (let [goal-index body-index ; Gathered into stack frame.
                  goal (first goals)
                  goals (rest goals)
                  assertion-matches (when-not assertion-matches ; Respect an empty coll.
                                      (get-assertion-matches assn-index goal bindings))
                  leash-report (str (with-out-str
                                      (when-not (private-built-in-special-head? (first goal))
                                        (leash-assertion-body special-form-depth
                                                              goal-index
                                                              head goals goal
                                                              bindings)))
                                    leash-report)]
              (gathering-body-remainder
               #(process-stack-frame (gather-stack-frame))))))))))

;;; Return either its input or `sys-and` of (first) as many
;;; `evals-from?` goals as necessary and (then) a `(->? ...)`-free
;;; version of the input goal.  We keep `evals-from?` forms in
;;; their `(->? ...)` order, in case there are any side
;;; effects.  Nested `(->?  ...)` forms are not supported.
(defn- transform-->?s [stack-frame]
  (with-stack-frame stack-frame
    (if-not (or (not (special-goal? goal)) ; * See below.
                (= (first goal) 'same))
      goal
      (let [evals-from?-goals (atom [])
            ->?-free-goal ; ...
            (walk-exprs #(and (seq? %) (= '->? (first %)))
                        (fn [->?-form]
                          (let [clojure-form (second ->?-form)
                                ??-i?var (indexify (new-unbound-?var '??) goal-index)]
                            (swap! evals-from?-goals conj
                                   `(~'evals-from? ~??-i?var ~clojure-form))
                            ;; Replace in goal with...
                            ??-i?var))
                        goal)]
        (if (= ->?-free-goal goal)
          goal
          (do (leash-->?-transform special-form-depth goal-index)
              `(~'sys-and ~@(apply list @evals-from?-goals) ~->?-free-goal)))))))
;;; Note : Lispy goals (`do`, `truthy`, `evals-from?`) don't need
;;; it.  (Not doing this transform on `second` of an `evals-from?`
;;; goal.*) Other special forms all have subgoals, to whose terminal
;;; forms---user predicates---the transform will be applied directly.
;;; Among built-in special forms, we subject only `same` to the
;;; transform.
;;;
;;; * We might take this on by recognizing our auto-generated `->?-<n>`
;;; ?var as a signal that such a form alreay had been processed.

(comment ; No help, so far.
  ;; Clojure stack is limiting us adequately, considering bindings.
  ;; Revisit under future logic tail recursion.
  (def ^:dynamic *stack-index-limit* 1000))

(defn- process-stack-frame [stack-frame]
  (when debugging-stack
    (pprint ["process-stack-frame" stack-frame]))
  (with-stack-frame stack-frame
    ;; Not working as expected.
    ;; #dbg ^{:break/when (> goal-index *stack-index-limit*)}
    (let [answer-limit-reached (and *answers-countdown*
                                    (= @*answers-countdown* 0))]
      (when (and *leash* answer-limit-reached)
        (println "Answer limit reached."))
      (when (and *leash*
                 (:final stack-frame)
                 (not answer-limit-reached))
        (print (:leash-report stack-frame)))
      (if (or answer-limit-reached (:final stack-frame))
        @*answers*
        ;; Else keep working.
        (do (when *leash*
              (print leash-report)
              (when (public-built-in-special-head? (first goal))
                (let [goals (or (:goals (first body-remainders))
                                ())]
                  ;; Handled separately in `process-predicate-frame`:
                  (leash-assertion-body special-form-depth goal-index head goals goal bindings))))
            (if (nil? goal) ; So, also `(nil? assertion-matches)`.
              #(process-assertion-success stack-frame)
              ;; Else, we have a goal.
              (let [goal (transform-->?s stack-frame)
                    goal (de-reference bindings goal)]
                (if (special-goal? goal)
                  #(process-special-frame (gather-stack-frame))
                  ;; Else we have a standard, predicate stack frame.
                  (let [assertion-matches (if (nil? assertion-matches)
                                            ;; If we've gotten here from a special
                                            ;; stack frame, we won't yet have
                                            ;; fetched our assertion matches.
                                            (get-assertion-matches (inc (inc goal-index))
                                                                   goal bindings)
                                            assertion-matches)]
                    #(process-predicate-frame (gather-stack-frame)))))))))))

(defn- leash-query [special-form-depth index verb input-goals]
  (when *leash*
    (let [prefix (leash-prefix special-form-depth index)]
      (println prefix verb "query:" input-goals))))

;;; For creation of tests/clolog/leash-tests.txt.
(def ^:private ^:dynamic *transcribe-query-info* false)

;;; Implement standard depth-first backtracking search.
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
  (when (and *transcribe-query-info* (= special-form-depth 0))
    (println)
    (pprint `(~'do (~'initialize-prolog)
              ~@(map (fn [assn] `(~'assert<- '~assn))
                     (get-matching-assertions '?_))))
    (println)
    (pprint `(~'query '~answer-template '~goals
              :limit ~limit
              :discard-subsumed ~discard-subsumed))
    (println))
  ;; An answer template is an expr usually including
  ;; ?vars---e.g., [?x], [?x ?y], unless we don't care about
  ;; bindings (e.g., for negation as failure---NAF).  An answer
  ;; template may also include arbitrary stuff, like
  ;; symbols---e.g., [?person bigger_than ?issue].
  ;; 
  ;; A goal is a clause.
  ;;
  ;; Any template ?vars that remain unbound (even those that do not
  ;; occur among the goals) are left as is.
  (if (empty? goals)
    [answer-template] ; Cheesey, not covered by *transcribe-query-info*.
    (let [; stack-index 0
          goal-index stack-index
          ;; Automatic: assn-index (inc goal-index)
          input-goals goals
          goals (indexify goals stack-index)
          query-i?vars (set (i?vars-of goals))
          goal (first goals)
          goals (rest goals)
          head nil ; Gathered into body-remainder.
          body-index goal-index ; Gathered into body-remainder.
          body-remainders () ; For `gathering-body-remainder`.
          bindings {}
          assertion-matches (get-assertion-matches (inc goal-index) goal bindings)]
      (binding [*answer-template* (indexify answer-template stack-index)
                *query-i?vars* query-i?vars
                *answers* (atom [])
                *discard-subsumed-answers* discard-subsumed
                *answers-countdown* (if (and discard-subsumed
                                             (not (seq query-i?vars)))
                                      ;; One answer is enough, for a
                                      ;; constant template.  (This
                                      ;; defeats leashing of this
                                      ;; class of duplicate
                                      ;; solutions.)
                                      (atom 1)
                                      (when limit (atom limit)))
                *unbound-var-counter* (atom 0)] ; Ok for NAF.
        (let [capo 'query
              capos ()
              leash-report (with-out-str
                             (when (= special-form-depth 0)
                               (leash-query special-form-depth stack-index "Processing" input-goals)))
              ;; Just the stack-frame fields we need (not really a StackFrame).
              continuation {:leash-report (if (= special-form-depth 0)
                                            (with-out-str
                                              (leash-query special-form-depth stack-index "Exhausted" input-goals))
                                            "")
                            :goal-index 0
                            :final true}]
          (gathering-body-remainder
           (let [result (trampoline process-stack-frame (gather-stack-frame))]
             (when (and *transcribe-query-info* (= special-form-depth 0))
               (pprint result))
             result)))))))

(defmacro ? [answer-template & goals] ; Does not support keyword args.
  "The macro version of function `query`."
  `(query (quote ~answer-template) (quote ~goals)))

;;; ----------------------------------------------------------------
;;; Housekeeping:

;;; --> clolog dirs

;;; CLJS, other target platforms

;;; Maven, ... ?

;;; Elemental Cognition ?

;;; Present doc strings.

