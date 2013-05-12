Correctness proof of a log-based semantics for software transactional memory
with respect to a stop-the-world semantics, using Agda.

The exact version described in chapter 9 of my [thesis][] is [tagged as
such][$thesis]. Futher refinements are on the [master branch][$master],
including compatibility fixes for more recent versions of [Agda][] and/or
[Nisse's standard library][stdlib].

This current version typechecks with the development versions of the
aforementioned as of 2013-05-11, but fails with Agda 2.3.2 (released on
2012-11-12) due to [a couple of][agda#665] [regressions][agda#824].

[thesis]: http://www.cs.nott.ac.uk/~gmh/hu-thesis.pdf
 "Compiling Concurrency Correctly: Verifying Software Transactional Memory"
[$thesis]: https://github.com/liyang/stm-proof/tree/thesis "tag: thesis"
[$master]: https://github.com/liyang/stm-proof/tree/master "branch: master"
[agda]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download "Agda: is it a dependently-typed programming language? Is it a proof-assistant based on intuitionistic type theory? ¯\(°_0)/¯ Dunno, lol."

[agda#665]: https://code.google.com/p/agda/issues/detail?id=665
 "auto-dotting can break with records"
[agda#824]: https://code.google.com/p/agda/issues/detail?id=824
 "recCon-NOT-PRINTED in error message"
[stdlib]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary
 "Agda Standard Library"

