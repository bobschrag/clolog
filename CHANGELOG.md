	# Changelog
	
	All notable changes to this project will be documented in this file.

	The format is based on [Keep a
	Changelog](https://keepachangelog.com/en/1.0.0/), and this project
	adheres to [Semantic
	Versioning](https://semver.org/spec/v2.0.0.html).

	## [0.4.0]: next

	- Make bindings of anonymous ?vars accessible where
	appropriate---by materializing corresponding, distingusihed
	`?anon...` ?vars at assertion and (for query goals) at query time.

	- Add built-in predicate `different` (and drop related example
	transform predicate).

	- Repair i?var-to-i?var de-referencing.
	
	- Repair one-empty sequential unification.

	- Add Zebra puzzle to tests.

	- Drop this property of matching...
	  *Seqs match only seqs, vecs only vecs.*
	  ...inconsistent with this property: *Constants match equal (Clojure `=`) constants.*
	
	## [0.3.0]: 2023-08-14

	- Important bug fixes (mediated by improved index integrity checking)
	- Improved documentation
	- Improved leashing distinguishing string predicates

	## [0.2.0]: 2023-07-29

	- Rename...

	`get-matching-assertions` `get-matching-head-assertions`
	`get-subsumed-assertions` `get-subsumed-headassertions`
	`get-subsuming-assertions` `get-subsuming-head-assertions`

	- Add...

	`get-matching-assertions`
	`get-subsumed-assertions`
	`get-subsuming-assertions`
	`retract-subsumed-assertions`
	`assert<-_`
	`<-_`

