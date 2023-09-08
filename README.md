# clolog

Full-featured logic programming (AKA "Prolog") embedded in/callable
from and supporting calls to Clojure.  In the spirit of LogLisp, Lisp
Machine Prolog, and Franz Inc.'s Allegro Prolog, with some extra
goodies.

## Highlights, with examples

- **Clojure-based, Lispy (i.e., homoiconic) syntax, e.g., ...**

  ```clojure
  (do 
      ;; Set up, clear knowledge base.
      (initialize-prolog)
      ;; Create unit assertion.    
      (<- (has-subtype vertebrate mammal)) 
      ;; Execute query.
      (? ?x ; Answer template
         (has-subtype vertebrate ?x) ; Goal.
         )
      )
    [mammal] ; Answer(s) in vector (perhaps empty).
    ```
    
- **Logical variable- ("?var")-containing Clojure seqs (so, lists) and
  vectors as "complex" terms---in assertion statements and answer templates**

  ```clojure
  > (? (?a ?b)
       (same [?a 2] [1 ?b]))
  [(1 2)]
  ```

- **Clojure calling predicates**

  - Truthiness check: `truthy?`

    ```clojure
    > (? true (truthy? (+ 1 2)))
    [true]
    ```

  - ?var-bearing term unification: `evals-from?`

    ```clojure
    > (? ?x (evals-from? ?x (+ 1 2)))
    [3]
    ```

  - Side effect: `do`

    ```clojure
    > (? nil (do (println "Hello")))
    Hello
    [nil]
    ```

- **Access to ?var bindings in Clojure calls---even within quoted
  expressions**

  ```clojure
  > (do (<-- (male laban))
        (? ?y (male ?x) (evals-from? ?y (list '?x))))
  [(laban)]
  ```  

- **Negation as failure: `not`**

  ```clojure
  > (do (initialize-prolog) ; Clear knowledge base.
        (? :nothing (not (Huh?))))
  [:nothing]
  ```

- **Facilitated access to Clojure values (`evals-from?` shorthand
    `->?`) in goals with Clojure-calling predicates**

  ```clojure
  > (binding [*leash* true]
      (? true (same (->? (+ 0 1)) 1)))
  0. Processing query: ((same (->? (+ 0 1)) 1))
   Applied ->? transform
   (evals-from?): Entering (evals-from? ??-0:0 (+ 0 1))
   (evals-from?): Succeeded (evals-from? 1 (+ 0 1))
   (same): Entering (same 1 1)
   (same): Succeeded (same 1 1)
  Recorded answer: true
  Answer limit reached. ; Because answer template `true` has no ?vars.
  [true]
  ```
  
- **Built-in term [non-]matching predicates: `same`, `different`**

  ```clojure
  > (? (?a ?b)
       (same [?a 2] [1 ?b]))
  [(1 2)]

  > (? (?a ?b)
       (different [?a 2] [1 ?b]))
  []
  ```

- **Built-in term inspection predicates: `var`, `ground`**

  ```clojure
  > (? ?y (var ?x))
  [?y]
  ```

  ```clojure
  > (? ?x (same ?x 1) (ground ?x))
  [1]
  ```

- **Built-in unconditional predicates: `true`, `false`**

  ```clojure
  > (? true (true))
  [true]
  ```

  ```clojure
  (? true (false))
  []
  ```

- **Nestable built-in logical operators: `and`, `or`, `not`, `if`**

  ```clojure
  > (? ?x (and (if (false)
                 (same ?x :succeed)
                 (same ?x :fail))
               (evals-from? ?x :fail)
	       (or (true) (false))))
  [:fail]
  ```

- **"Cut" operator: `first`**

  ```clojure
  > (do (initialize-prolog)
        (<- (sister laban rebecca))
        (<- (sister rachel leah))
        (? [?sibling ?sister]
           (first (sister ?sibling ?sister))))
   [[laban rebecca]]
   ```

- **User-custom predicate transforms, supporting (e.g.) 
  varieties of `if`, `cond`, `optional`**

  ```clojure
  > (create-predicate-transform '((if% ?if ?then ?else)
                                (if (first ?if) ?then ?else)))
  ```

- **Full leashing of predicates, including operators**

  ```clojure
  > (binding [*leash* true]
      (? [?sibling ?sister ?x] 
        (if% (sister ?sibling ?sister)
             (evals-from? ?x true)
             (evals-from? ?x false))))
  0. Processing query: ((if% (sister ?sibling ?sister) (evals-from? ?x true) (evals-from? ?x false)))
   (if%): Applying logic transform (if% ?if ?then ?else)
   (if): Entering (if (first (sister ?sibling:0 ?sister:0)) (evals-from? ?x:0 true) (evals-from? ?x:0 false))
   (if): Checking 'if' condition (if (first (sister ?sibling:0 ?sister:0)) (evals-from? ?x:0 true) (evals-from? ?x:0 false))
    (if first): Entering first (first (sister ?sibling:0 ?sister:0))
     1. Entering "sister/2": (sister ?sibling:0 ?sister:0)
     1. Matched head (sister laban rebecca): (sister laban rebecca)
     1. Succeeded "sister/2": (sister laban rebecca)
    (if first): Succeeded, cutting (first (sister laban rebecca))
   (if): Taking 'then' branch of (if (first (sister laban rebecca)) (evals-from? ?x:0 true) (evals-from? ?x:0 false))
    (if evals-from?): Entering (evals-from? ?x:0 true)
    (if evals-from?): Succeeded (evals-from? true true)
   (if): Succeeded (if (first (sister laban rebecca)) (evals-from? true true) (evals-from? true false))
  Recorded answer: [laban rebecca true]
    (if first): Failed (first (sister ?sibling:0 ?sister:0))
   (if): Failed (if (first (sister ?sibling:0 ?sister:0)) (evals-from? ?x:0 true) (evals-from? ?x:0 false))
  0. Exhausted query: ((if% (sister ?sibling ?sister) (evals-from? ?x true) (evals-from? ?x false)))
  [[laban rebecca true]]
    ```
    
- **Symbols interpreted as logic terms or predicates, regardless of their Clojure values**

  ```clojure
  > (do (<- (false true))
        (? ?x (false ?x)))
  [true]

  > (do (<- (neg? 3))
        (? true (neg? 3)))
  [true]
  ```

- **Arbitrary Clojure things as terms or predicates, e.g., ...**

  - Strings (supporting, e.g., RDF URIs)

    ```clojure
    > (do (<- ("false" true))
          (? ?x ("false" ?x)))
    [true]
    ```
  
  - Numbers

    ```clojure
    > (do (<- (3 neg?))
          (? ?x (3 ?x)))
    [neg?]
    ```

  - Complex terms

    ```clojure
    > (do (initialize-prolog)
          (<- ([treasure] (buried ?x)))
	  (? ?r ([treasure] ?r)))
    [(buried ?unbound-0)]
    ```
  
- **Predicates that are ?var-bearing complex terms**

  ```clojure
  > (do (initialize-prolog)
        (<- ([treasure chest] (buried ?x)))
	(? [?r ?thing] ([treasure ?thing] ?r)))
  [[(buried ?unbound-0) chest]]
  ```

- **Predicates that are ?vars**

  ```clojure
  > (do (initialize-prolog)
        (<- (male jacob))
	(? ?pred (?pred jacob)))
  [male]
  ```

- **Variadic (variable-tail/arity) predicates and complex terms**

  ```clojure
  > (do (initialize-prolog)
        (<- (variadic))
        (<- (variadic 1))
        (<- (variadic 1 2))
        (? ?rest (variadic & ?rest)))
  [() (1) (1 2)]

  > (do (initialize-prolog)
        (<- (variadic-term [1]))
        (<- (variadic-term [1 2]))
	(? ?rest (variadic-term [1 & ?rest])))
  [[] [2]]
  ```

- **Goals that are ?vars**

  ```clojure
  > (do (initialize-prolog)
        (<- (male jacob))
	(? ?goal ?goal)) ; Tell me everything you can prove.
  [(male jacob)]
  ```

  ```clojure
  > (do (initialize-prolog)
        (<- (male jacob))
	(? ?goal (unasserted) ?goal)) ; ...with what you know so far.
  []
  ```

- **Anonymous ?vars**

  ```clojure
  > (do (initialize-prolog)
        (<- (sister laban rebecca))
        (<- (sister rachel leah))
        (? true (sister ?_person ?_person)))
  [true]

  > (? true (sister ? ?))
  [true]
  ```

- **Suppression of answers that are (under ?var renaming) duplicates**

  ```clojure
  > (do (initialize-prolog)
        (<- (male laban))
	(<- (male jacob))
	(binding [*leash* true]
          (? ?x (or (male ?x) (male ?x)))))
  0. Processing query: ((or (male ?x) (male ?x)))
   (or): Entering (or (male ?x:0) (male ?x:0))
    1. Entering "male/1": (male laban)
    1. Matched head (male laban): (male laban)
    1. Succeeded "male/1": (male laban)
  Recorded answer: laban
    1. Backtracking into "male/1": (male ?x:0)
    1. Succeeded "male/1": (male jacob)
  Recorded answer: jacob
    1. Backtracking into "male/1": (male ?x:0)
    1. Failed "male/1": (male ?x:0)
   (or): Backtracking into (or (male ?x:0) (male ?x:0))
    1. Entering "male/1": (male laban)
    1. Matched head (male laban): (male laban)
    1. Succeeded "male/1": (male laban)
  Duplicate answer (not recorded): laban
    1. Backtracking into "male/1": (male ?x:0)
    1. Succeeded "male/1": (male jacob)
  Duplicate answer (not recorded): jacob
    1. Backtracking into "male/1": (male ?x:0)
    1. Failed "male/1": (male ?x:0)
   (or): Failed (or (male ?x:0) (male ?x:0))
  0. Exhausted query: ((or (male ?x) (male ?x)))
  [laban jacob]
  ```

- **Optional suppression of answers subsumed by other answers**

  ```clojure
  > (do (initialize-prolog)
        (<- (sister laban rebecca))
        (<- (sister ?x ?y))
        (binding [*leash* true]
          (? [?x ?y] (sister ?x ?y))))
  0. Processing query: ((sister ?x ?y))
   1. Entering "sister/2": (sister laban rebecca)
   1. Matched head (sister laban rebecca): (sister laban rebecca)
   1. Succeeded "sister/2": (sister laban rebecca)
  Recorded answer: [laban rebecca]
   1. Backtracking into "sister/2": (sister ?x:0 ?y:0)
   1. Succeeded "sister/2": (sister ?x:0 ?y:0)
  Recorded subsuming answer (discarded 1 subsumed answer(s)):  [?x ?y]
   1. Backtracking into "sister/2": (sister ?x:0 ?y:0)
   1. Failed "sister/2": (sister ?x:0 ?y:0)
  0. Exhausted query: ((sister ?x ?y))
  [[?x ?y]]
  ```

- **Failure (i.e., not system error) when no assertions have been
  defined for a called logic predicate and arity**

  ```clojure
  > (do (initialize-prolog)
                 (binding [*leash* true]
                   (? answer (undefined ?arity-1))))
  0. Processing query: ((undefined ?arity-1))
   1. Entering "undefined/1": (undefined ?arity-1:0)
   1. Failed "undefined/1": (undefined ?arity-1:0)
  0. Exhausted query: ((undefined ?arity-1))
  []
  ```

## Grammar

In production rules below, ...
- Angle brackets surround a grammar \<element\>.
- \<element\>+ denotes one or more of \<element\>.
- \<element\>* denotes zero or more of \<element\>.
- ":-" separates rules' left- and right-hand sides.
- "|" separates right-hand sides' alternatives.

\<assertion\>: `(`\<head-statement\>+ \<body-statement\>*`)`

\<head-statement\> :- \<statement\>

\<body-statement\> :- \<statement\>

\<statement\> :- \<fixed-arity-statement\> | \<variable-arity-statement\>

\<fixed-arity-statement\> :- `(`\<predicate\>+ \<argument-term\>\*`)`

\<argument-term\> :- \<term\>

\<variable-arity-statement\> :- `(`\<predicate\>+ \<term\>* `&` \<?var\>`)`

\<predicate\> :- \<special-predicate\> | \<assertion-predicate\>

\<special-predicate\> :- \<built-in-predicate\> | \<transform-predicate\>

\<built-in-predicate\> :- \<operator\> | \<Clojure-calling-predicate\> | `same` | `different` | `var` | `ground` | `true` | `false`

\<operator\> :- `and` | `or` | `if` | `not` | `first`

\<Clojure-calling-predicate\> :- `truthy?` | `evals-from?` | `do`

\<transform-predicate\>: A predicate constant registered using `create-predicate-transform`

\<assertion-predicate\>: A predicate all of whose assertions (if any) are from calls to one of the `<-`... macros or `assert<-`... functions

\<term\> :- \<transparent-term\> | \<opaque-term\>

\<transparent-term\> :- \<?var\> | \<complex-term\>

\<complex-term\> :- \<fixed-artiy-complex-term\> | \<variable-arity-complex-term\>

\<fixed-arity-complex-term\> :- `(`\<term\>\*`)` | `[`\<term\>\*`]` 

\<variable-arity-complex-term\> :- `(`\<term\>\* `&` \<?var\>`)` | `[`\<term\>\* `&` \<?var\>`]`

\<opaque-term\> :- Any Clojure value supporting Clojure `=` (so, not a regex) that is not a transparent term

\<?var\> :- \<binding-?var\> | \<anonymous-?var\>

\<anonymous-?var\> :- `?` | \<`_`-anonymous-?var\>

\<`_`-anonymous-?var\>: Symbol whose name begins with `"?_"`

\<constant\>: An opaque term or a ?var-free complex term

\<answer-template\> :- \<term\>

Note:

- All predicates are terms.

- All ?vars are symbols.

- Statements and assertions, being lists, are terms.

- The arguments of operators are statements.  See our Built-in predicates
  section.

- Outside of Clojure-calling predicates' Clojure form arguments:
  Symbols appearing in statements are taken at face value, not evaluated.
  A symbol used in Prolog otherwise has no relationship to its value
  (or the lack thereof) in Clojure.

## Additional terminology and conventions

Considering for the moment only assertion (not special) predicates,
logic programming **search** processes (or **calls**), in turn from
left to right, each **goal** in an (implicitly) conjunctive **query**
by...

- Identifying assertions whose head statement matches the goal

- Prepending a matching assertion's body statements (AKA the assertion's
  **goals**) to the query's remaining goals, after applying the
  match's ?var bindings to each such goal

- Processing remaining goals, recursively, ...

  - **Backtracking** to remaining matching assertions, when matching a
    given assertion **fails**

  - When no goals remain, **succeed** by...

    - Recording an **answer** that realizes the query's **answer
      template** according to ?var matches made along the search path
    
    - Backtracking to search for any additional answers.

Search generally proceeds depth-first and from left to right.

We **match** two statements or transparent terms by associating their
respective terms and ?vars, position by position, with consistent
matching for non-anonymous ?vars.  In matching (AKA "unification"),
...

- A ?var matches a ?var, a transparent term, or a constant.

- Constants match equal (Clojure `=`) constants.

- Complex terms match recursively.

- A **tail ?var** (last in a statement or complex term, and preceded by
  `&`) matches the (possibly empty) seq or vector of terms remaining in
  the parallel traversal of its opposing complex term.

One term **subsumes** another if the two terms match and---considering
?var occurrences---the former is at least as general as the latter.

A **ground** term has no ?vars (none outside of any opaque included
terms, where they are not treated as ?vars).

Here---and in leash (execution tracing) reports---the notation
\<predicate\>/\<integer\> (e.g., `sibling/2`) refers to the
\<integer\> arity of \<predicate\>.

By convention, we take the first argument of a 2-ary statement to be the
predicate's **subject**, the second to be its **object**.  Thus, in
`(brother Jane John)`, we take `Jane` to be the subject (or agent),
`John` to be the object (or patient).  ("A brother of Jane is John.")

A **unit** assertion has only a head statement, no body statements.

## API

### Initialization

Clear the knowledge base and any existing special predicate
transforms, then execute the transform definitions in function
`create-predicate-transforms`.

```clojure
(initialize-prolog)
```

### Knowledge base and predicate transform contexts

Bind `*assertions*` and/or `*predicate-transforms*`, per their doc
strings, to set up contexts for different knowledge bases and/or
transform definitions.

### Creating assertions---macros and functions

We provide four assertion creation functions and four corresponding
macros.  The macros, which don't require quoting arguments, so are
simpler to use at the REPL or from top level in a file, take their
statement arguments at top-level.  The functions take theirs in a list.

An assertion's head statement...

- May not be a ?var.

- May be variadic, but must require arity >= 1 (i.e., must not start
  with `&`).

- Must not have a built-in special predicate in its predicate
  position.  We don't flag assertions to transform predicates;
  however, once a predicate has been used on the left-hand side of a
  transform's defining production rule, we refrain from exercising
  same-predicate assertions.

See the functions' doc strings for other fine points.

The following forms have equivalent effect: Add the assertion with
head statement `(sibling ?x ?y)` and lone goal statement `(brother ?x ?y)`
to the knowledge base.

```clojure
(<- (sibling ?x ?y) (brother ?x ?y)) ; Macro.

(assert<- '((sibling ?x ?y) (brother ?x ?y))) ; Function.
```

The following place their constant-predicate, fixed-arity assertion
first for consideration in search.  We provide no explicit control
over the order in which (less conventional) assertions with variadic,
variable, or non-ground complex head statement predicates are examined
during backtracking search.

```clojure
(<-0 (sibling ?x ?y) (brother ?x ?y)) ; Macro.

(assert<-0 '((sibling ?x ?y) (brother ?x ?y))) ; Function.
```

The following clear `sibling/2` before making their assertion.

```clojure
(<-- (sibling ?x ?y) (brother ?x ?y)) ; Macro.

(assert<-- '((sibling ?x ?y) (brother ?x ?y))) ; Function.
```

The following clear the entire knowledge base of all but special
transforms before making their assertion.

```clojure
(<--- (sibling ?x ?y) (brother ?x ?y)) ; Macro.

(assert<--- '((sibling ?x ?y) (brother ?x ?y))) ; Function.
```

The following---when employed systematically---avoid
subsumed-subsuming assertion pairs in the knowledge base, by declining
to add would-be-subsumed assertions and by retracting subsumed
assertions.

```clojure
(<-_ (sibling ?x ?y) (brother ?x ?y)) ; Macro.

(assert<-_ '((sibling ?x ?y) (brother ?x ?y))) ; Function.
```

We retrieve assertions once upon calling a predicate, and assertion or
retraction operations otherwise relevant to that predicate will be
reflected during the call.

### Retrieving assertions

We provide three functions for retrieving assertions by matching their
heads against a statement pattern.  Each returns a vector containing the
knowledge base's assertions whose head statements exhibit the function's
required relationship to `statement-pattern`.

Get assertions whose head matches `statement-pattern`.
```clojure
(get-matching-head-assertions statement-pattern)
```

Get assertions whose head is subsumed by `statement-pattern`.
```clojure
(get-subsumed-head-assertions statement-pattern)
```

Get assertions whose head subsumes `statement-pattern`.
```clojure
(get-subsuming-head-assertions statement-pattern)
```

We provide two similar functions that match assertions against a
full assertion pattern.

Get assertions entirely subsumed by `assertion-pattern`.
```clojure
(get-subsumed-assertions assertion-pattern)
```

Get assertions entirely subsuming `assertion-pattern`.
```clojure
(get-subsuming-assertions assertion-pattern)
```

### Retracting assertions

We provide two functions, and two corresponding macros, for retracting
assertions by matching their head statements against a pattern and
one function to retract assertions entirely matching an assertion pattern.

The following have equivalent effect.  As in the assertion retrieval
functions, `statement-pattern` refers to assertions' head statements.

```clojure
(retract-subsumed-head-assertions statement-pattern)

(--- statement-pattern)
```

The following have equivalent effect.  Here, `assertion` must be equal
(Clojure `=`, including equal ?var symbols) to an assertion in the
knowledge base, for the latter to be retracted.

```clojure
(retract-specific-assertion assertion) ; Function.

(-- statement-pattern) ; Macro.
```

```clojure
(retract-subsumed-assertions '((?pred deceased-person)))
```

## Querying

The following macro and function are equivalent---except that the
macro does not support keyword arguments (instead, bind the
default-value globals).  With a truthy limit, terminate search upon
having recorded so many answers.

```clojure
(? answer-template & goals) ; Macro.

(query answer-template goals ; Function.
       :limit *answer-count-limit*
       :discard-subsumed *discard-subsumed-answers*)
```

## Leashing

For now, leashing is an all-or-nothing proposition.  Perform any query
with `*leash*` bound truthy, for goal-by-goal reports describing
execution.

```clojure
(binding [*leash* true]
  ;; Query form(s) in here.
  )
```

As demonstrated in our Highlights section and in
`test/prolog/leash-tests.txt`, leashing reports...

- Entry into and success or failure of goals
- Backtracking into...
  - Remaining matching assertions of goals with assertion predicates
  - Remaining disjuncts (remaining alternatives goals) of `or` goals
- `first` operator-induced cuts
- Application of predicate transforms
- The discovery of answers and their disposition
- Search termination upon reaching an answer count limit.

Leashing also...

- Indexes reports per depth of assertion nesting
- Indicates the nesting of built-in predicates for the current assertion
- Left-pads reports per nesting of assertion and built-in predicate goals.

When `*pprint-leash-statements*` is truthy, ...`"Entering"`, ...

- `"Matched head"` leash reports are omitted.
- `"Succeeded"`, and `"Failed"` leash reports pprint (vs. print)
  statement content, starting on a new line, with indentation, as in...

```clojure
clolog.core> (binding [*leash* true
                       *pprint-leash-statements* true]
               (query '[?h ?w ?z] '((zebra ?h ?w ?z)) :limit 1))
0. Processing query: ((zebra ?h ?w ?z))
 1. Entering `zebra`/3:
    (zebra ?h:0 ?w:0 ?z:0)

  1. (same): Entering...
             (same
              ?h:0
              ((house norwegian ?anon-0:1 ?anon-1:1 ?anon-2:1 ?anon-3:1)
               ?anon-4:1
               (house ?anon-5:1 ?anon-6:1 ?anon-7:1 milk ?anon-8:1)
               ?anon-9:1
               ?anon-10:1))

  1. (same): Succeeded...
             (same
              ((house norwegian ?anon-0:1 ?anon-1:1 ?anon-2:1 ?anon-3:1)
               ?anon-4:1
               (house ?anon-5:1 ?anon-6:1 ?anon-7:1 milk ?anon-8:1)
               ?anon-9:1
               ?anon-10:1)
              ((house norwegian ?anon-0:1 ?anon-1:1 ?anon-2:1 ?anon-3:1)
               ?anon-4:1
               (house ?anon-5:1 ?anon-6:1 ?anon-7:1 milk ?anon-8:1)
               ?anon-9:1
               ?anon-10:1))

  2. Entering `member`/2:
     (member
      (house englishman ?anon-11:1 ?anon-12:1 ?anon-13:1 red)
      ((house norwegian ?anon-0:1 ?anon-1:1 ?anon-2:1 ?anon-3:1)
       ?anon-4:1
       (house ?anon-5:1 ?anon-6:1 ?anon-7:1 milk ?anon-8:1)
       ?anon-9:1
       ?anon-10:1))
```

## Built-in predicates

We support the following built-in predicates.  We borrow some notation
from our Grammar section and allow ourselves to introduce types via
obvious naming (e.g., a \<condition-statement\> is a
\<statement\>---distinguished merely by its role/argument position in the
built-in predicate `if`).  We invoke the exclued middle: If a goal
does not succeed, then it fails.

- `(and` \<statement\>*`)` succeeds if, proceeding from left to right,
  every conjunct statement succeeds.

- `(or` \<statement\>*`)` succeeds if, proceeding from left to
  right, some disjunct statement succeeds (and remaining disjuncts are
  ignored).  Backtracking will explore first alternative ways to
  satisfy a failing statement, then subsequent statements.

- `(if` \<condition-statement\> \<then-statement\> \<else-statement\>`)`
  succeeds if either:

  - The condition statement succeeds and the then statement succeeds (in which
    case we do not examine the else statement under the bindings for
    the condition statement's ?vars)

  - The condition statement fails and the else statement succeeds (in which
    case we do not examine `then-statement`).

  Backtracking will explore alternative ways to satisfy the argument
  statements.

- `(not \<statement\>)` succeeds if the wrapped statement fails.

- `(first \<statement\>)` succeeds if the argument statement succeeds.  This
  form (AKA Prolog "cut") skips backtracking to explore other ways of
  satisfying the statement, upon its first success.

- `(same \<term\> \<term\>)` succeeds if the two terms match.

- `(true)` succeeds unconditionally.

- `(false)` fails unconditionally.

- `(var \<term\>)` succeeds if the argument term is a ?var.

- `(ground \<term\>)` succeeds if the argument term is ground.

- `(truthy? \<form\>)` succeeds if the argument form is ground and
  the result of its evaluation (in Clojure) is truthy.

- `(evals-from? \<term\> \<form\>)` succeeds if the argument form is
  ground and the result of its evaluation (in Clojure) matches the
  argument term (often a ?var).

- `(do \<form\>)` succeeds if the argument form is ground, evaluating
  it (in Clojure) for side effect, only.

## Creating special transforms

The function call below---performed by `initialize-prolog`---seeds
Clolog with some transforms for predicates we have found useful in
other Lisp-based Prologs.  As we intend this facility to support
customization, you may wish to copy our version of
`create-predicate-transforms` and edit it to your liking.

```clojure
(create-predicate-transforms)
```

`create-predicate-transforms` includes calls to
`create-predicate-transform`.  Each call is a production rule.  During
search, a goal matching `source-statement` is transformed---via
de-referencing---into `target-statement`.

```clojure
(create-predicate-transform source-statement target-statement)
```

The execution machinery for transform predicates applies the first
matching transform irrevocably, with no backtracking in case of
failure.  Compared to an assertion predicate defined using using one
assertion per transform and the same statements in each
transform-assertion pair, it is as if the transform predicate's goal
always were wrapped with `first`.  We consider predicate transforms to
be "macros" for Prolog, affording us cleaner leashing than would
similar assertion predicates.  Assertion predicatess more verbose
leashing may nonetheless be helpful in prototyping and debugging
prospective transforms.  It may help to call
`create-predicate-transforms` with optional argument `debugging?`
truthy---and either disregard any effects resulting from backtracking
into prospective transform predicates ultimately intended or (as in
`tests/clolog/core_tests.clj`) avoid backtracking by limiting the
count of answers found.

## Potential future enhancements

We might pursue some of the following ideas towards increasing
expressivity/leashing, robustness/scale, and efficiency, given
motivating use cases.

- Potential enhancements to expressiveness and leashing:

  - Accommodate non-ground Clojure expressions in Clojure-calling
    forms---in case a called form would use these in crafting
    subsequent goal (e.g.).

  - Make the local/lexical environment accessible within called
    Clojure forms.

  - Support RDF, RDFS, selected aspects of OWL (e.g., inverses,
    functional dependencies).

  - Selective leashing, considering (e.g.) predicate, arity,
    report type (e.g., answer disposition).
  
  - Selective detail in leashing, e.g., re `if` subgoals
  
  - Greater precision in leash report prefixes for n-ary operators
    `and`, `or` (e.g., indexing potentially like-predicate conjuncts,
    disjuncts).

- Potential enhancements to robustness and scale

  - Error-check user/application inputs more pervasively.

  - Support Prolog stack limits, breakpoints, stepping/debugger
    integration.

  - Support database integration---access to unit ground assertions.

- Potential efficiency enhancements

  - Perform further indexing, including trie-based indexing.

  - Qualify seq/vector matching with early check for compatible
    lengths of candidate-matching seqs and vectors.

  - Decline to explore alternative satisfactions of a ground goal.

  - Skirt search branches that cannot instantiate an answer template
    ?var.

  - Support parallelism and/or laziness.

## License

Copyright © 2023 Robert Carl Schrag

This program and the accompanying materials are made available under
the terms of the Eclipse Public License 2.0 which is available at
http://www.eclipse.org/legal/epl-2.0.

This Source Code may also be made available under the following
Secondary Licenses when the conditions for such availability set forth
in the Eclipse Public License, v. 2.0 are satisfied: GNU General
Public License as published by the Free Software Foundation, either
version 2 of the License, or (at your option) any later version, with
the GNU Classpath Exception which is available at
https://www.gnu.org/software/classpath/license.html.
