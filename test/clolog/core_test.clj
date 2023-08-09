(ns clolog.core-test
  (:require [clojure.test :refer :all]
            [clolog.core :refer :all]
            [clojure.pprint :refer [cl-format]]))

(def ^:dynamic *goal-from-clj*) ; See using test.

(deftest test-assert<-
  (testing "assert<-"
    (do (initialize-prolog)
        (assert<- '((has-subtype ?type ?subsubtype) ; <--
                    (has-subtype ?type ?subtype)
                    (has-subtype ?subtype ?subsubtype))))
    (is (= '[((has-subtype ?type ?subsubtype)
              (has-subtype ?type ?subtype)
              (has-subtype ?subtype ?subsubtype))]
           (get-matching-head-assertions '?)))
    (do (initialize-prolog)
        (assert<- '((has-subtype ?type ?subsubtype) ; <--
                    (has-subtype ?type ?subtype)
                    (has-subtype ?subtype ?subsubtype)))
        (assert<- '((has-subtype vertebrate mammal)))
        (assert<- '((has-subtype mammal primate)))
        (assert<- '((has-subtype primate human)))
        (assert<- '((has-subtype NONSENSE)))
        (assert<- '((NONSENSE primate human)))
        (assert<- '((NONSENSE))))
    (is (= '[((has-subtype ?type ?subsubtype)
              (has-subtype ?type ?subtype)
              (has-subtype ?subtype ?subsubtype))
             ((has-subtype vertebrate mammal))
             ((has-subtype mammal primate))
             ((has-subtype primate human))
             ((has-subtype NONSENSE))
             ((NONSENSE primate human))
             ((NONSENSE))]
           (get-matching-head-assertions '?)))
    (is (= '[((has-subtype vertebrate mammal))]
           (get-subsumed-head-assertions '(has-subtype ?type mammal))))
    (is (= '[((has-subtype ?type ?subsubtype)
              (has-subtype ?type ?subtype)
              (has-subtype ?subtype ?subsubtype))
             ((has-subtype vertebrate mammal))]
           (get-matching-head-assertions '(has-subtype ?type mammal))))
    ;; Access?
    (is (= '[((has-subtype ?type ?subsubtype)
              (has-subtype ?type ?subtype)
              (has-subtype ?subtype ?subsubtype))
             ((has-subtype vertebrate mammal))
             ((has-subtype mammal primate))
             ((has-subtype primate human))]
           (get-matching-head-assertions '(has-subtype ? ?))))
    (is (= '(((has-subtype ?type ?subsubtype)
              (has-subtype ?type ?subtype)
              (has-subtype ?subtype ?subsubtype))
             ((has-subtype vertebrate mammal))
             ((has-subtype mammal primate))
             ((has-subtype primate human))
             ((NONSENSE primate human)))
           (get-matching-head-assertions '(? ? ?))))
    ;; Variants:
    (is (= '[((bar))]
           (do (assert<--- '((bar)))
               (get-matching-head-assertions '?))))
    (is (= '[((bar))]
           (do (assert<-- '((bar)))
               (get-matching-head-assertions '?))))
    (is (= '[((bar)) ((bar))]
           (do (assert<-0 '((bar)))
               (get-matching-head-assertions '?))))
    ;; Retraction:
    (do (initialize-prolog)
        (assert<--- '((bar))))
    (is (= []
           (do (retract-subsumed-head-assertions '(bar))
               (get-matching-head-assertions '?))))
    (assert<--- '((bar)))
    (is (= [] (do (retract-subsumed-head-assertions '?)
                  (get-matching-head-assertions '?))))
    (assert<--- '((bar)))
    (is (= [] (do (retract-subsumed-assertions '(?))
                  (get-matching-head-assertions '?))))
    (assert<--- '((bar)))
    (assert<- '((bar none)))
    (is (= []
           (do (retract-subsumed-head-assertions '(bar &))
               (get-matching-head-assertions '?))))
    (assert<- '((bar none)))
    (is (= []
           (do (--- (bar &))
               (get-matching-head-assertions '?))))
    (do (initialize-prolog)
        (<- (variadic-term []))
        (<- (variadic-term [1]))
        (<- (variadic-term [1 2])))
    (is (= []
           (do (--- (variadic-term [& ?rest]))
               (get-matching-head-assertions '?))))
    (do (initialize-prolog)
        (<- (variadic-term []))
        (<- (variadic-term [1]))
        (<- (variadic-term [1 2])))
    (is (= '[((variadic-term []))]
           (do (--- (variadic-term [1 & ?rest]))
               (get-matching-head-assertions '?))))
    (do (initialize-prolog)
        (<- (variadic-term [& ?rest]))
        (<- (variadic-term []))
        (<- (variadic-term [1]))
        (<- (variadic-term [1 2])))
    (is (= '[((variadic-term []))
             ((variadic-term [1]))
             ((variadic-term [1 2]))]
           (do (-- (variadic-term [& ?rest]))
               (get-matching-head-assertions '?))))
    (do (initialize-prolog)
        (<- (variadic))
        (<- (variadic 1))
        (<- (variadic 1 2)))
    (is (= []
           (do (--- (variadic & ?rest))
               (get-matching-head-assertions '?))))
    ;; Non-ground complex predicate:
    (<--- ([complex 1] 1))
    (is (= []
           (do (--- ([complex ?x] ?x))
               (get-matching-head-assertions '?))))
    (<--- ([complex ?x] ?x))
    (is (= []
           (do (--- ([complex ?x] ?x))
               (get-matching-head-assertions '?))))
    (<--- ([complex & ?rest] ?rest))
    (is (= '[(([complex & ?rest] ?rest))]
           (do (--- ([complex 1] (1)))
               (get-matching-head-assertions '?))))
    (<--- ([complex 1] (1)))
    (is (= []
           (do (--- ([complex ?x] ?x))
               (get-matching-head-assertions '?))))
    (do (<--- ([complex 1] (1)))
        (<- ([complex ?x] ?x)))
    (is (= '[(([complex 1] (1)))]
           (do (-- ([complex ?x] ?x))
               (get-matching-head-assertions '?))))
    ;; Retrieval:
    (<--- ([complex ?x] ?x))
    (is (= (get-subsuming-head-assertions '([complex 1] 1))
           '[(([complex ?x] ?x))]))
    (<--- ([complex 1] 1))
    (is (= '[(([complex 1] 1))]
           (get-subsumed-head-assertions '([complex ?x] ?x))))
    ;; Minimalism:
    (do (initialize-prolog)
        (<-_ (has-subtype vertebrate mammal))
        (<-_ (has-subtype vertebrate ?mammal)))
    (is (= '[((has-subtype vertebrate ?mammal))]
           (get-matching-head-assertions '?)))
    (do (initialize-prolog)
        (<-_ (has-subtype vertebrate ?mammal))
        (<-_ (has-subtype vertebrate mammal)))
    (is (= '[((has-subtype vertebrate ?mammal))]
           (get-matching-head-assertions '?)))
    ;; For token-matcher:
    (do (initialize-prolog)
        (doseq [assn '[((has-subkind* ?kind ?subkind) (has-subkind ?kind ?subkind))
                       ((has-subkind* ?kind ?subsubkind)
                        (has-subkind ?kind ?subkind)
                        (has-subkind* ?subkind ?subsubkind))
                       ((has-kind "really big show" kind))
                       ((has-kind "John" kind))
                       ((has-kind "John Smith" kind))
                       ((has-kind "really" kind))
                       ((has-kind "something" kinder))
                       ((has-kind "kinder" kinder))
                       ((has-kind "something really big" kinder))
                       ((has-kind "kinder gentler" kinder))
                       ((has-kind "Book 1" kindle))
                       ((has-kind "Book 2" kindle))]]
          (assert<-_ assn)))
    (is (= (get-matching-head-assertions '?)
           '[((has-subkind* ?kind ?subkind) (has-subkind ?kind ?subkind))
             ((has-subkind* ?kind ?subsubkind)
              (has-subkind ?kind ?subkind)
              (has-subkind* ?subkind ?subsubkind))
             ((has-kind "really big show" kind))
             ((has-kind "John" kind))
             ((has-kind "John Smith" kind))
             ((has-kind "really" kind))
             ((has-kind "something" kinder))
             ((has-kind "kinder" kinder))
             ((has-kind "something really big" kinder))
             ((has-kind "kinder gentler" kinder))
             ((has-kind "Book 1" kindle))
             ((has-kind "Book 2" kindle))]))
    ))

(deftest query-test
  (testing "query"
    ;; Empty goals:
    (initialize-prolog)
    (is (= []
           ;; Not defined: `pseudo-fail`.
           (query true '((pseudo-fail)))))
    (is (= [true]
           ;; Implicit `and` here.
           (query true '())))
    ;; Ground, unit assertions:
    (do (initialize-prolog)
        (assert<- '((has-subtype vertebrate mammal)))
        (assert<- '((has-subtype mammal primate)))
        (assert<- '((has-subtype primate human))))
    (is (= [true]
           (query true
                  '((has-subtype vertebrate mammal)))))
    (is (= '[mammal]
           (query '?x
                  '((has-subtype vertebrate ?x)))))
    (is (= '[(has-subtype vertebrate mammal)
             (has-subtype mammal primate)
             (has-subtype primate human)]
           (query '(has-subtype ?type ?subtype)
                  '((has-subtype ?type ?subtype)))))
    (is (= '[(has-subtype vertebrate mammal)
	     (has-subtype mammal primate)
	     (has-subtype primate human)]
           (query '(?pred ?type ?subtype)
                  '((?pred ?type ?subtype)))))
    (is (= '[(primate)]
           (query '(?subtype)
                  '((has-subtype mammal ?subtype)
                    (has-subtype ?subtype human)))))
    ;; Add non-ground, non-unit assertions.
    (do (initialize-prolog)
        ;; `has-subtype` is non-transitive (to avoid infinite recursion) .
        (assert<- '((has-subtype vertebrate mammal)))
        (assert<- '((has-subtype mammal primate)))
        (assert<- '((has-subtype primate human)))
        (assert<- '((has-subtype* ?type ?subtype)
                    (has-subtype ?type ?subtype)))
        ;; This assertion of `has-subtype*` is transitive.
        (assert<- '((has-subtype* ?type ?subsubtype)
                    (has-subtype ?type ?subtype)
                    (has-subtype* ?subtype ?subsubtype))))
    (is (= [true]
           (query true '((has-subtype* vertebrate primate)))))
    (is (= [true]
           (binding [*discard-subsumed-answers* false]
             (query true '((has-subtype* vertebrate primate))))))
    (is (= '[mammal primate human]
           (? ?x (has-subtype* vertebrate ?x))))
    (is (= '[[vertebrate mammal]
             [mammal primate]
             [primate human]
             [vertebrate primate]
             [vertebrate human]
             [mammal human]]
           (? [?x ?y] (has-subtype* ?x ?y))))
    ;; Alternative formulation:
    (do (initialize-prolog)
        (<- (is-type vertebrate))
        (<- (is-type mammal))
        (<- (is-type primate))
        (<- (is-type human))
        ;; `has-subtype` is non-transitive (to avoid infinite recursion) .
        (assert<- '((has-subtype vertebrate mammal)))
        (assert<- '((has-subtype mammal primate)))
        (assert<- '((has-subtype primate human)))
        (assert<- '((has-subtype* ?type ?subtype)
                    (has-subtype ?type ?subtype)))
        ;; This assertion of `has-subtype*` is transitive.
        (assert<- '((has-subtype* ?type ?subsubtype)
                    (is-type ?type)
                    (is-type ?subsubtype)
                    (truthy? (not= (quote ?type) (quote ?subsubtype)))
                    (has-subtype ?type ?subtype)
                    (is-type ?subtype)
                    (truthy? (not= (quote ?type) (quote ?subtype)))
                    (has-subtype* ?subtype ?subsubtype))))
    (is (= [true]
           (query true '((has-subtype* vertebrate primate)))))
    (is (= [true]
           (binding [*discard-subsumed-answers* false]
             (query true '((has-subtype* vertebrate primate))))))
    (is (= '[mammal primate human]
           (? ?x (has-subtype* vertebrate ?x))))
    (is (= '[[vertebrate mammal]
             [mammal primate]
             [primate human]
             [vertebrate primate]
             [vertebrate human]
             [mammal human]]
           (? [?x ?y] (has-subtype* ?x ?y))))
    ;; Complex terms:
    (do (initialize-prolog)
        (assert<- '((successor 0 (s 0)))))
    (is (= '[(s 0)]
           (query '?x
                  '((successor 0 ?x)))))
    (is (= '[0]
           (query '?x
                  '((successor ?x (s 0))))))
    (is (= '[0]
           (query '?x
                  '((successor ?x (s ?x))))))
    (do (initialize-prolog)
        (assert<- '((successor 0 (s 0))))
        (assert<- '((successor (s ?x) (s (s ?x))))))
    (is (= '[(s 0)]
           (query '?x
                  '((successor ?x (s (s 0)))))))
    ;; Non-ground assertions:
    (do (initialize-prolog)
        (assert<- '((has-subtype thing ?thing))))
    (is (= [true]
           (query true
                  '((has-subtype thing mammal)))))
    ;; Template ?var answers:
    (is (= '[?bar]
           (query '?bar
                  '((has-subtype thing ?bar)))))
    (do (initialize-prolog)
        (assert<- '((successor ?x (s ?x)))))
    (is (= '[[?q (s ?q)]]
           (query '[?q ?r] '((successor ?q ?r)))))
    (is (= '[(s ?q)]
           (query '?r '((successor ?q ?r)))))
    (do (initialize-prolog)
        (assert<- '((pseudo-same ?x ?x))))
    (is (= '[[?q ?r]]
           (query '[?q ?r] '((pseudo-same ?q ?r)))))
    (is (= '[?x]
           (query '?x '((pseudo-same ?x ?x)))))
    (is (= '[?x]
           (query '?x '((same ?x ?x)))))
    ;; Multi-goal assertions:
    (do (initialize-prolog)
        (assert<- '((uncle ?nephew ?uncle) ; <--
                    (parent ?nephew ?parent)
                    (sibling ?uncle ?parent)
                    (male ?uncle)
                    (male ?nephew)))
        (assert<- '((sibling ?x ?y) ; <--
                    (brother ?x ?y)))
        (assert<- '((sibling ?x ?y) ; <--
                    (sister ?x ?y)))
        (assert<- '((sister laban rebecca)))
        (assert<- '((male laban)))
        (assert<- '((male jacob)))
        (assert<- '((parent jacob rebecca)))
        (assert<- '((both-male ?one ?two) ; <--
                    (male ?one)
                    (male ?two))))
    (is (= '[(laban laban) (laban jacob) (jacob laban) (jacob jacob)]
           (query '(?x ?y) '((both-male ?x ?y)))))
    (is (= '[laban]
           (query '?uncle '((uncle jacob ?uncle)))))
    (is (= '[[laban rebecca]]
           (query '[?x ?y] '((sibling ?x ?y)))))
    ;; Answer limit:
    (is (= '[(laban laban) (laban jacob)]
           (binding [*answer-count-limit* 2]
             (query '(?x ?y) '((both-male ?x ?y))))))
    (is (= '[laban]
           (query '?uncle '((sister ?uncle rebecca)
                            (male ?uncle)))))
    ;; Answer subsumption:
    (do (initialize-prolog)
        (<- (sister laban rebecca))
        (<- (sister ?x ?y)))
    (is (= '[[?x ?y]]
           (query '[?x ?y] '((sister ?x ?y)))))
    ;; Smaller.
    (do (initialize-prolog)
        (assert<- '((sister laban rebecca)))
        (assert<- '((male laban)))
        (assert<- '((male jacob))))
    ;; Unbound (non-template) ?var answers:
    (do (initialize-prolog)
        (assert<- '((treasure (buried ?x)))))
    (is (= '[(buried ?unbound-0)]
           (query '?r '((treasure ?r)))))
    (do (initialize-prolog)
        (<- (treasure (buried ?x)))
        (<- (marks-the-spot X)))
    (is (= '[[(buried ?unbound-0) X]]
           (? [?r ?x] (treasure ?r) (marks-the-spot ?x))))
    ;; String predicate:
    (do (initialize-prolog)
        (assert<- '(("treasure" (buried ?x)))))
    (is (= '[(buried ?unbound-0)]
           (query '?r '(("treasure" ?r)))))
    ;; Complex predicate:
    (do (initialize-prolog)
        (assert<- '(([treasure] (buried ?x)))))
    (is (= '[(buried ?unbound-0)]
           (query '?r '(([treasure] ?r)))))
    (do (initialize-prolog)
        (assert<- '(([treasure chest] (buried ?x)))))
    (is (= '[(buried ?unbound-0)]
           (query '?r '(([treasure ?thing] ?r)))))
    (is (= '[[(buried ?unbound-0) chest]]
           (query '[?r ?thing] '(([treasure ?thing] ?r)))))
    ;; ?var as predicate:
    (do (initialize-prolog)
        (assert<- '((male jacob))))
    (is (= '[male]
           (query '?pred '((?pred jacob)))))
    ;; ?var as goal.
    (do (initialize-prolog)
        (assert<- '((male jacob)))
        (assert<- '((goal (male ?male)))))
    (is (= '[(male jacob)]
           (query '?goal '((goal ?goal) ?goal))))
    (do (initialize-prolog)
        (assert<- '((male jacob))))
    (is (= '[(male jacob)]
           (query '?goal '(?goal))))
    (comment ; These work fine at the REPL, but they don't compile from here.
      (is (= '[jacob]
             (binding [*goal-from-clj* '(male ?x)]
               (? ?x (evals-from? ?goal *goal-from-clj*)
                     ?goal))))
      (is (= '[jacob]
             (binding [*goal-from-clj* '(male ?x)]
               (query '?x '((evals-from? ?goal *goal-from-clj*)
                            ?goal)))))
      )
    ;; `and` goal:
    (initialize-prolog)
    (is (= [true]
           (query true '((and)))))
    (is (= []
           (query true '((and (pseudo-fail))))))
    (is (= [true]
           (query true '((and) (and)))))
    (is (= [true]
           (query true '((and (and))))))
    (is (= [true]
           (query true '((and (and (and)))))))
    (do (initialize-prolog)
        (assert<- '((male laban))))
    (is (= [true]
           (query true '((and (male ?x))))))
    (is (= [true]
           (query true '((and) (male ?x)))))
    (is (= [true]
           (query true '((and (male ?x) (male ?x))))))
    (is (= []
           (query true '((and (male ?x) (female ?x))))))
    (is (= [true]
           (query true '((and (male ?x) (and (male ?x)))))))
    (do (initialize-prolog)
        (assert<- '((male laban)))
        (assert<- '((male jacob))))
    (is (= [true]
           (query true '((and (male ?x) (male ?y))))))
    ;; `or` goal:
    (do (initialize-prolog)
        (assert<- '((pseudo-succeed))))
    (is (= []
           (query true '((or)))))
    (is (= []
           (query true '((or (pseudo-fail))))))
    (is (= [true]
           (query true '((or (pseudo-succeed))))))
    (is (= [true]
           (query true '((or (pseudo-fail) (pseudo-succeed))))))
    (is (= []
           (query true '((or) (or)))))
    (is (= [true]
           (query true '((or (or (pseudo-succeed)))))))
    (is (= [true]
           (query true '((or (or (or (pseudo-succeed))))))))
    (do (initialize-prolog)
        (assert<- '((male laban))))
    (is (= [true]
           (query true '((or (male ?x))))))
    (is (= [true]
           (query true '((or (male ?x) (male ?x))))))
    (is (= [true]
           (query true '((or (male ?x) (or (male ?x)))))))
    (do (initialize-prolog)
        (assert<- '((male laban)))
        (assert<- '((male jacob))))
    (is (= '[laban jacob]
           (query '?x '((or (male ?x) (male ?x))))))
    (is (= '[?y]
           (query '?y '((or (male ?x) (male ?x))))))
    (is (= [true]
           (query true '((or (male ?x) (male ?y))))))
    (is (= '[[laban ?y] [jacob ?y] [?x laban] [?x jacob]]
           (query '[?x ?y] '((or (male ?x) (male ?y))))))
    (is (= '[[?x ?y]]
           (binding [*discard-subsumed-answers* true]
             (query '[?x ?y] '((or (male ?x) (male ?y) (male ?z)))))))
    ;; `succeed` goal:
    (initialize-prolog)
    (is (= [true]
           (query true '((true)))))
    (do (initialize-prolog)
        (assert<- '((male laban)))
        (assert<- '((male jacob))))
    (is (= '[[laban jacob]]
           (query '[laban jacob] '((male ?x) (true) (male ?x)))))
    ;; `fail` goal:
    (initialize-prolog)
    (is (= []
           (query true '((false)))))
    ;; `truthy?` goal:
    (is (= [true]
           (query true '((truthy? true)))))
    (is (= [true]
           (query true '((truthy? (+ 1 2))))))
    (is (= [true]
           (query true '((truthy? true)
                         (true)))))
    (do (initialize-prolog)
        (assert<- '((male laban))))
    (is (= '[laban]
           (query '?x '((male ?x)
                        (truthy? (list (quote ?x)))))))
    (is (= '[(laban)]
           (query '?y '((male ?x)
                        (evals-from? ?y (list (quote ?x)))))))
    (is (= '[laban]
           (query '?x '((and (male ?x)
                             (truthy? (list (quote ?x))))))))
    (is (= '[laban]
           (query '?x '((male ?x)
                        (truthy? (= (quote ?x) 'laban))))))
    (is (= []
           (query '?x '((male ?x)
                        (truthy? nil)))))
    (is (= []
           (query '?x '((truthy? ?x)))))
    (is (= '[laban]
           (query '?x '((or (male leah)
                            (male ?x)
                            (truthy? (list (quote ?x))))))))
    ;; `do` goal:
    (is (= '["Hello, laban"]
           (? ?message (male ?x)
                       (evals-from? ?message
                                    (str "Hello, " (quote ?x))))))
    (is (= [true]
           (query true '((male ?x)
                         (do ; println
                           (clojure.pprint/cl-format nil "Hello, ~a." (quote ?x)))))))
    ;; `evals-from?` goal:
    (is (= '["Hello, laban."]
           (query '?message '((male ?x)
                              (evals-from? ?message
                                           (clojure.pprint/cl-format nil "Hello, ~a." (quote ?x)))))))
    (is (= '["Hello, laban."]
           (query '?message '((male ?x)
                              (evals-from? [?message]
                                           [(clojure.pprint/cl-format nil "Hello, ~a." (quote ?x))])))))
    ;;; `same` goal:
    (initialize-prolog)
    (is (= '[[1 2]]
           (query '[?a ?b] '((same [?a 2] [1 ?b])))))
    (is (= '[(1 2)]
           (query '(?a ?b) '((same [?a 2] [1 ?b])))))
    ;;; `not` goal:
    (is (= [true]
           (query true '((not (truthy? false))))))
    (is (= [true]
           (query true '((not (brother laban rebecca))))))
    (do (initialize-prolog)
        (assert<- '((sister laban rebecca))))
    (is (= '[[laban rebecca]]
           (query '[?x ?y] '((sister ?x ?y)
                             (not (sister ?y ?x))))))
    (initialize-prolog)
    (is (= [true]
           (query '?x '((and (evals-from? ?x true) (truthy? (quote ?x)))))))
    (is (= [true]
           (query '?x '((and (evals-from? ?x true) (truthy? ?x))))))
    ;;; `if` goal:
    (is (= [true]
           (query true '((if (true) (true) (true))))))
    (is (= [true]
           (query true '((if (truthy? true) (true) (false))))))
    (is (= [true]
           (query '?x '((if (true)
                          (evals-from? ?x true)
                          (evals-from? ?x false))))))
    (is (= [false]
           (query '?x '((if (false)
                          (evals-from? ?x true)
                          (evals-from? ?x false))))))
    (is (= [false]
           (query '?x '((if (false)
                          (evals-from? ?x true)
                          (if (false)
                            (evals-from? ?x true)
                            (evals-from? ?x false)))))))
    (is (= [:inner-else]
           (query '?x '((if (true)
                          (if (false)
                            (evals-from? ?x :inner-then)
                            (evals-from? ?x :inner-else))
                          (evals-from? ?x :outer-else))))))
    (do (initialize-prolog)
        (assert<- '((sister laban rebecca))))
    (is (= [true]
           (query '?x '((if (sister laban rebecca)
                          (evals-from? ?x true)
                          (evals-from? ?x false))))))
    (do (initialize-prolog)
        (assert<- '((sister laban rebecca)))
        (assert<- '((sister rachel leah))))
    (is (= '[[laban rebecca true] [rachel leah true]]
           (query '[?sibling ?sister ?x] '((if (sister ?sibling ?sister)
                                             (evals-from? ?x true)
                                             (evals-from? ?x false))))))
    (initialize-prolog)
    (is (= '[[?sibling ?sister false]]
           (query '[?sibling ?sister ?x] '((if (sister ?sibling ?sister)
                                             (evals-from? ?x true)
                                             (evals-from? ?x false))))))
    ;;; `first` goal:
    (do (initialize-prolog)
        (assert<- '((sister laban rebecca)))
        (assert<- '((sister rachel leah))))
    (is (= '[[laban rebecca]]
           (query '[?sibling ?sister] '((first (sister ?sibling ?sister))))))
    (is (= '[[laban rebecca true]]
           (query '[?sibling ?sister ?x] '((if (first (sister ?sibling ?sister))
                                             (evals-from? ?x true)
                                             (evals-from? ?x false))))))
    (is (= '[[laban rebecca]]
           (query '[?sibling ?sister] '((first (and (sister ?sibling ?sister)
                                                    (sister ?sibling ?sister)))))))
    ;; `var` goal:
    (initialize-prolog)
    (is (= [true]
           (? true (var ?x))))
    (is (= [true]
           (query true '((var ?x)))))
    (is (= '[?x]
           (query '?x '((var ?x)))))
    (is (= '[?y]
           (query '?y '((var ?x)))))
    (is (= []
           (query true '((var 1)))))
    ;; Anonymous ?vars:
    (do (initialize-prolog)
        (assert<- '((sister laban rebecca)))
        (assert<- '((sister rachel leah))))
    (is (= '[true]
           (query true '((sister ?_person ?_person)))))
    (is (= '[true]
           (query true '((sister ?_ ?_)))))
    (is (= '[true]
           (query true '((sister ? ?)))))
    ;; Compound special forms:
    (initialize-prolog)
    (is (= '[]
           (query '?x '((and (if (true)
                               (same ?x :succeed)
                               (same ?x :fail))
                             (evals-from? ?x :succeed)
                             (false))))))
    (is (= '[:fail]
           (query '?x '((and (if (false)
                               (same ?x :succeed)
                               (same ?x :fail))
                             (evals-from? ?x :fail)
                             (true))))))
    (is (= '[:fail]
           (query '?x '((and (if (false)
                               (same ?x :succeed)
                               (same ?x :fail))
                             (evals-from? ?x :fail)
                             (or (true) (false)))))))
    (is (= '[:fail]
           (query '?x '((and)
                        (evals-from? ?x :fail)
                        (true)))))
    (is (= '[:fail]
           (query '?x '((and (and)
                             (evals-from? ?x :fail)
                             (true))))))
    ;; Logic macros:
    (initialize-prolog)
    (is (= []
           (query true '((cond*)))))
    (do (initialize-prolog)
        (assert<- '((sister laban rebecca)))
        (assert<- '((sister rachel leah))))
    (is (= '[[laban rebecca true]]
           (query '[?sibling ?sister ?x] '((if% (sister ?sibling ?sister)
                                             (evals-from? ?x true)
                                             (evals-from? ?x false))))))
    (is (= '[[?sibling false]]
           (query '[?sibling false] '((cond% (sister ?sibling adam)
                                             (evals-from? ?x 'adam)

                                             (sister ?sibling eve)
                                             (evals-from? ?x 'eve)

                                             :else
                                             (evals-from? ?x false))))))
    (is (= '[[?sibling ?sister]]
           (binding [*discard-subsumed-answers* true]
             (query '[?sibling ?sister]
                    ;; Wrong definition of `optional`:
                    '((or (sister ?sibling ?sister) (true)))))))
    (is (= '[[laban rebecca]]
           (query '[?sibling ?sister]
                  ;; Also wrong definition of `optional`:
                  '((first (or (sister ?sibling ?sister) (true)))))))
    (is (= '[[laban rebecca] [rachel leah]]
           (query '[?sibling ?sister]
                  '((optional (sister ?sibling ?sister))))))
    (do (initialize-prolog)
        (assert<- '((sister laban rebecca)))
        (assert<- '((sister rachel leah)))
        (create-predicate-transforms :debugging))
    (is (= '[[?sibling false]]
           ;; Avoid backtracking into intended-transform predicates.
           (binding [*answer-count-limit* 1]
             (query '[?sibling false] '((cond% (sister ?sibling adam)
                                               (evals-from? ?x 'adam)

                                               (sister ?sibling eve)
                                               (evals-from? ?x 'eve)

                                               :else
                                               (evals-from? ?x false)))))))
    (initialize-prolog)
    (is (= [true]
           (? true (ground [a b]))))
    (is (= [true]
           (query true '((ground [a b])))))
    (is (= []
           (? true (ground ?x))))
    (is (= [1]
           (? ?x (same ?x 1) (ground ?x))))
    (is (= '[[?sibling ?sister]]
           (query '[?sibling ?sister]
                  '((optional (sister ?sibling ?sister))))))
    (is (= [true]
           (query true '((different 1 2)))))
    (is (= []
           (query true '((different 2 2)))))
    ;; `->?` forms in goals:
    (is (= [true]
           (query true '((same (->? (+ 0 1)) 1)))))
    ;; `&` in answer template:
    (is (= [[1 2 3 4]]
           (query '[1 2 & ?rest] '((same ?rest [3 4])))))
    ;; `&` in assertion head statement:
    (do (initialize-prolog)
        (<- (variadic 1))
        (<- (variadic 1 2)))
    (is (= '[(1) (1 2)]
           (? ?rest (variadic & ?rest))))
    ;; `&` in goal term:
    (is (= '[(variadic 1) (variadic 1 2)]
           (? (variadic & ?rest) (variadic & ?rest))))
    ;; `&` in assertion head statement term:
    (do (initialize-prolog)
        (<- (variadic-term [1]))
        (<- (variadic-term [1 2])))
    (is (= '[[1] [1 2]]
           (? ?rest (variadic-term [& ?rest]))))
    (is (= '[[] [2]]
           (? ?rest (variadic-term [1 & ?rest]))))
    (is (= []
           (? ?rest (variadic-term (& ?rest)))))
    (do (initialize-prolog)
        (<- (variadic))
        (<- (variadic 1))
        (<- (variadic 1 2)))
    (is (= '[() (1) (1 2)]
           (? ?rest (variadic & ?rest))))
    (is (= '[(variadic) (variadic 1) (variadic 1 2)]
           (? ?rest (& ?rest))))
    (do (initialize-prolog)
        (<- (variadic & ?rest)))
    (is (= [true]
           (? true (variadic 1))))
    (comment ; Deferred.  (Marginal value.)
      ;; Map answer template:
      (do (initialize-prolog)
          (<- (foo 1)))
      (is (= [{:answer 1}]
             (? {:answer ?x} (foo ?x)))))
    ;; Complex predicate:
    (do (initialize-prolog)
        (<- ([complex] 1)))
    (is (= [1]
           (? ?x ([complex] ?x))))
    ;; Non-ground complex predicate:
    (do (initialize-prolog)
        (<- ([complex 1] 1)))
    (is (= [1]
           (? ?x ([complex ?x] ?x))))
    (do (initialize-prolog)
        (<- ([complex ?x] ?x)))
    (is (= [true]
           (? true ([complex 1] 1))))
    (do (initialize-prolog)
        (<- ([complex & ?rest] ?rest)))
    (is (= [true]
           (? true ([complex 1] (1)))))
    ;; For kanl:
    (do (initialize-prolog)
        (doseq [assn '[((has-kind* ?instance ?kind) (has-kind ?instance ?kind))
                       ((has-kind* ?instance ?kind)
                        (has-subkind* ?kind ?subkind)
                        (has-kind ?instance ?subkind))
                       ((has-subkind* ?kind ?subkind) (has-subkind ?kind ?subkind))
                       ((has-subkind* ?kind ?subsubkind)
                        (has-subkind ?kind ?subkind)
                        (has-subkind* ?subkind ?subsubkind))
                       ((supports-subject-type ?predicate ?subtype)
                        (supports-subject-type ?predicate ?type)
                        (has-subkind ?type ?subtype))
                       ((supports-subject-type "allowed to use" "person"))
                       ((supports-subject-type "permissioned to" "person"))
                       ((supports-object-type ?predicate ?subtype)
                        (supports-object-type ?predicate ?type)
                        (has-subkind* ?type ?subtype))
                       ((supports-object-type "allowed to use" "resource"))
                       ((supports-object-type "permissioned to" "resource"))
                       (("allowed to use" ?person ?resource)
                        ("permissioned to" ?person ?resource))
                       (("allowed to use" ?person ?resource)
                        (not ((neg "allowed to use") ?person ?resource))
                        (not (has-kind* ?resource "restricted resource")))
                       ((has-subkind "restricted resource" "resource"))
                       ((has-kind "Bob" "person"))
                       ((has-kind "Repo 2" "resource"))]]
          (assert<-_ assn)))
    (is (= '[["Bob" "Repo 2"]]
           (binding [*leash* true]
             (query '[?subject ?object]
                    '((has-kind* ?subject "person")
                      (has-kind* ?object "resource")
                      ("allowed to use" ?subject ?object))))))
    ))

;;; Run this (at a clolog.core REPL), to generate leash tests.
;;; Copy any authoritative output to leash-tests.txt.
(comment (binding [*transcribe-query-info* true
                   *leash* true
                   *answer-count-limit* nil
                   ;; Try also `false` (and expect to fail a few tests).
                   *discard-subsumed-answers* true]
           (clolog.core-test/query-test)))

(comment
;; Not maintained.  See leash-tests.txt (which we diff against output
;; from the above).
  (deftest test-leashing
    (testing "Leashing"
      (do (initialize-prolog)
          (assert<- '((male laban))))
      (is (= (with-out-str
               (print "0. Processing query: ((male ?x))
0. Working on goal (male ?x:0)
0. Remaining goals: ()
 1. Entering male/1: (male laban)
 1. Matched head (male laban): (male laban)
 1. Succeeded male/1: (male laban)
Recorded answer: laban
 1. Backtracking into male/1: (male laban)
 1. Failed male/1: (male laban)
0. Finished query: ((male ?x))
"))
             ;; Harder (w.r.t. initial  continuation `:done`):
             ;; 1. Backtracking into male/1: (male ?x:0)
             ;; 1. Failed male/1: (male ?x:0)
             ;; Skipping that tail, for now.
             (with-out-str
               (binding [*leash* true]
                 (query '?x '((male ?x)))))))
      (do (initialize-prolog)
          (assert<- '((male laban)))
          (assert<- '((male jacob))))
      (is (= (with-out-str
               (print "0. Processing query: ((male ?x))
0. Working on goal (male ?x:0)
0. Remaining goals: ()
 1. Entering male/1: (male laban)
 1. Matched head (male laban): (male laban)
 1. Succeeded male/1: (male laban)
Recorded answer: laban
 1. Backtracking into male/1: (male laban)
 1. Succeeded male/1: (male jacob)
Recorded answer: jacob
 1. Backtracking into male/1: (male jacob)
 1. Failed male/1: (male jacob)
0. Finished query: ((male ?x))
"))
             (with-out-str
               (binding [*leash* true]
                 (query '?x '((male ?x)))))))

      ;; Missing predicate:
      (initialize-prolog)
      (is (= (with-out-str
               (print "0. Processing query: ((foo))
0. Working on goal (foo)
0. Remaining goals: ()
 1. Entering foo/0: (foo)
 1. Failed foo/0: (foo)
0. Finished query: ((foo))
"))
             (with-out-str
               (binding [*leash* true]
                 (query true '((foo)))))))

      (do (initialize-prolog)
          (assert<- '((male laban))))
      (is (= (with-out-str
               (print "0. Processing query: ((male ?x) (foo))
0. Working on goal (male ?x:0)
0. Remaining goals: ((foo))
 1. Entering male/1: (male laban)
 1. Matched head (male laban): (male laban)
 1. Succeeded male/1: (male laban)
0. Working on goal (foo)
0. Remaining goals: ()
 1. Entering foo/0: (foo)
 1. Failed foo/0: (foo)
 1. Backtracking into male/1: (male laban)
 1. Failed male/1: (male laban)
0. Finished query: ((male ?x) (foo))
"))
             (with-out-str
               (binding [*leash* true]
                 (query '?x '((male ?x) (foo)))))))

      (do (initialize-prolog)
          (assert<- '((uncle ?nephew ?uncle) ; <--
                      (parent ?nephew ?parent)
                      (sibling ?uncle ?parent)
                      (male ?uncle)
                      (male ?nephew)))
          (assert<- '((sibling ?x ?y) ; <--
                      (brother ?x ?y)))
          (assert<- '((sibling ?x ?y) ; <--
                      (sister ?x ?y)))
          (assert<- '((sister laban rebecca)))
          (assert<- '((male laban)))
          (assert<- '((male jacob)))
          (assert<- '((parent jacob rebecca)))
          (assert<- '((both-male ?one ?two) ; <--
                      (male ?one)
                      (male ?two))))
      (is (= (with-out-str
               (print "0. Processing query: ((uncle jacob ?uncle))
0. Working on goal (uncle jacob ?uncle:0)
0. Remaining goals: ()
 1. Entering uncle/2: (uncle jacob ?uncle:1)
 1. Matched head (uncle ?nephew:1 ?uncle:1): (uncle jacob ?uncle:1)
 1. Working on goal (parent ?nephew:1 ?parent:1): (parent jacob ?parent:1)
 1. Remaining goals: ((sibling ?uncle:1 ?parent:1) (male ?uncle:1) (male jacob))
  2. Entering parent/2: (parent jacob rebecca)
  2. Matched head (parent jacob rebecca): (parent jacob rebecca)
  2. Succeeded parent/2: (parent jacob rebecca)
 1. Working on goal (sibling ?uncle:1 ?parent:1): (sibling ?uncle:1 rebecca)
 1. Remaining goals: ((male ?uncle:1) (male jacob))
  2. Entering sibling/2: (sibling ?x:3 rebecca)
  2. Matched head (sibling ?x:3 ?y:3): (sibling ?x:3 rebecca)
  2. Working on goal (brother ?x:3 ?y:3): (brother ?x:3 rebecca)
  2. Remaining goals: ()
   3. Entering brother/2: (brother ?x:3 rebecca)
   3. Failed brother/2: (brother ?x:3 rebecca)
  2. Backtracking into sibling/2: (sibling ?x:3 rebecca)
  2. Working on goal (sister ?x:3 ?y:3): (sister ?x:3 rebecca)
  2. Remaining goals: ()
   3. Entering sister/2: (sister laban rebecca)
   3. Matched head (sister laban rebecca): (sister laban rebecca)
   3. Succeeded sister/2: (sister laban rebecca)
 1. Working on goal (male ?uncle:1): (male laban)
 1. Remaining goals: ((male jacob))
  2. Entering male/1: (male laban)
  2. Matched head (male laban): (male laban)
  2. Succeeded male/1: (male laban)
 1. Working on goal (male ?nephew:1): (male jacob)
 1. Remaining goals: ()
  2. Entering male/1: (male jacob)
  2. Matched head (male jacob): (male jacob)
  2. Succeeded male/1: (male jacob)
Recorded answer: laban
  2. Backtracking into male/1: (male jacob)
  2. Failed male/1: (male jacob)
  2. Backtracking into male/1: (male laban)
  2. Failed male/1: (male laban)
   3. Backtracking into sister/2: (sister laban rebecca)
   3. Failed sister/2: (sister laban rebecca)
  2. Backtracking into sibling/2: (sibling ?x:3 rebecca)
  2. Failed sibling/2: (sibling ?x:3 rebecca)
  2. Backtracking into parent/2: (parent jacob rebecca)
  2. Failed parent/2: (parent jacob rebecca)
 1. Backtracking into uncle/2: (uncle jacob ?uncle:1)
 1. Failed uncle/2: (uncle jacob ?uncle:1)
0. Finished query: ((uncle jacob ?uncle))
"))
             (with-out-str
               (binding [*leash* true]
                 (query '?uncle '((uncle jacob ?uncle)))))))
      )))

;;; OBE: Try this on a failing leash test.
(comment
  (defn elucidate-leash-test-result [result]
    (clojure.string/split-lines result))
  )

(comment
  ;; Change `defn-` to `defn` in now-private `adjudication-status` and
  ;; `unify`, then uncomment to run these tests.


  (deftest adjudication-status-test
    (testing "adjudication-status"
      (is (= :subsumed
             (adjudication-status '?x true)))
      (is (= :subsumes
             (adjudication-status true '?x)))
      (is (= :equivalent
             (adjudication-status true true)))
      (is (= :equivalent
             (adjudication-status '?y '?x)))
      (is (= :different
             (adjudication-status true false)))
      ))

  (deftest unify-test
    (testing "unify"
      (is (= '[{?all [1 2 3]} {}]
             (unify '[& ?all] [1 2 3])))
      (is (= '[{} {?all [1 2 3]}]
             (unify [1 2 3] '[& ?all])))
      (is (= '[{?all [2 3]} {}]
             (unify '[1 & ?all] [1 2 3])))
      (is (= '[{?some [2 3]} {}]
             (unify '[1 & ?some] [1 2 3])))
      (is (= '[{?rest ?more} {?more ?rest}]
             (unify '[1 2 & ?rest] '[1 2 & ?more])))
      (comment (is (= '[{?rest [3 4]} {}]
                      ;; We don't expect/generally support this usage.
                      (unify '[1 2 & ?rest] '[1 2 & [3 4]]))))
      (is (= '[{?rest [3 4]} {}]
             (unify '[1 2 & ?rest] '[1 2 3 4])))
      (is (= '[{?rest (3 4)} {}]
             (unify '(1 2 & ?rest) '(1 2 3 4))))
      ))

  )
