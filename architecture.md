# clolog design

## Matching, bindings, de-referencing

We have two different representations for the bindings that result
from matching one expression against another---unindexed and indexed.
Depending on values of optional keyword arguments, core matching and
de-referencing functions exercise one representation or the other.
(To **de-reference** a ?var is to retrieve its (most) concrete value,
following chains of ?var-?var bindings as necessary.  To de-reference
a term is to return a version of the term in which all ?vars have been
de-referenced.)

### Unindexed bindings

The unindexed representation covers single-level matching
needs---retrieving clauses for knowledge base management operations,
comparing answers.  Unindexed bindings, resulting from unindexed
matching, are pairs of complementary ?var-value maps, one from the
perspective of each of the two match arguments.  This representation
facilitates computing subsumption relationships.

### Indexed bindings

This representation indexes ?vars by search depth, to distinguish
(potentially clashing) different assertions' ?vars.  We start at index
0 for query goals, then index 1 for an assertion called by a query
goal, index 2 for an assertion called by a first-level assertion's
goal, etc.  We call an index-?var pair an i?var.  In leashing (and for
discussion here), i?vars are rendered as \<?var\>`:`\<index\> (e.g.,
`?x:3`).

We maintain i?var bindings in a map (usually referred to locally as
`bindings`) whose keys are indices and whose values are maps of ?vars
(the i?vars at that search level) to matching values.

When we need to exhibit a value---for a leash report or for an
answer---we extract it from `bindings`.

Note:

- When matching an i?var to an i?var, ...

  - We will enter a lower-indexed i?var as a higher- one's value (so
    that, e.g., `?x:2` may have value `?x:1`)---never vice versa.
    This prevents i?var-value cycles in `bindings`.  (Same-indexed
    i?vars are matched only per a hack in processing calls to built-in
    predicate `same`---not ordinarily.)

  - If, during above matching, the lower-indexed i?var already has as
    its value a yet-lower-indexed i?var (e.g., `?x:1` has value
    `?x:0`), we will use the latter as the higher- one's (so,
    `?x:2`'s) value.  Thus, we push unbound i?vars "up" (index-wise)
    the search stack.  We call this the "push-up" strategy.

- When matching an i?var to a non-i?var, ...

  - If the i?var does not already have as its value another i?var,
    we install the non-i?var as its value.

  - If the i?var has as its value another (lesser-indexed) i?var, we
    install the non-i?var as the latter's value.  Thus, we push a
    non-i?var value to its least search level (lowest index in
    `bindings`).  Call this the "reference" level.  Since, per the
    above, all intermediate i?vars in any i?var chain also point to
    this level, de-referencing a given i?var (for a leash report, say)
    requires at most one hop of indirect look-up.

 - Instantiating an answer template requires merely looking up the
   template's ?var values (if any) at index 0.

A nuance arises when a lower-indexed ?var becomes bound to a complex
term containing a higher-indexed ?var that remains unbound, as in the
following example (from `tests/clolog/core_tests.clj`).

```clojure
> (do (initialize-prolog)
      (<- (treasure (buried ?x)))
      (<- (marks-the-spot X)))
> (? ?r (treasure ?r) (marks-the-spot ?x))
[[(buried ?unbound-0) X]]
```

When exiting the successful assertion call, we must "export" the
assertion's ?var `?x`, renaming it uniquely (here, as `?unbound-0`) to
prevent clashes with a same-named query ?var (such as `?x`, that we
index here as `?x:0`).  We can't keep referring to the exported ?var
as `?x:1`, either, in case ?var `?x` might occur in another matching
assertion for `treasure/1` (e.g., with head `(treasure (buried (twice
?x)))`).  In our "push-up" scheme, we index such a renamed, exported
?var at the reference level (here, 0).

## Stack machine

Our Prolog interpreter is a stack machine.  Each goal to be processed
is associated with a stack frame, and each type of goal---as
distinguished by its predicate---has an appropriate stack frame
handler.  We have one handler for assertion predicates, another
handler for each public special predicate, and still more handlers for
private special predicates that ("under the hood") facilitate leashing
and special control for processing of goals with predicates `if` and
`first`.  We dispatch to these specialized handlers via the
general-purpose handler `process-stack-frame`.  Each handler (also a
couple of other key functions) is named `process-...`.  Our
search-launching function, `query`, calls `trampoline` directly on
`process-stack-frame`.  Then every other call to a a `process-...`
function is accordingly anonymized.  Prolog continuations
(representing backtrack points) are passed in (and as) stack frames.
Clojure stack depth for stack machine execution is effectively a
non-issue, regardless of Prolog search depth.

Prolog bindings (also passed in stack frames) track Prolog search
depth.

## Potential future enhancements

Beyond enhancements suggested in `README.md`, we might support...

- Prolog tail recursion

- Prolog compilation---e.g., per-assn partial evaluation of
  unification and assertion exit operations.

