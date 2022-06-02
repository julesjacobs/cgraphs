MPGV: multiparty session types
===============================

This is the Coq development of MPGV.
This development proves the main theorems that MPGV satisfies:
- Global progress
- Deadlock freedom
- Full reachability (memory leak freedom)

The files of interest are:
- langdef.v: Definition of the MPGV language (syntax + operational semantics + type system).
- globaltypes.v: The definition of global types, and proof that global type consistency implies coinductive consistency.
- binary.v: Encoding binary session types in MPGV.
- definitions.v: Definitions required to formulate the main theorems (mainly, definition of deadlock freedom and full reachability).
- theorems.v: The proofs of the main theorems (global progress, deadlock freedom, and full reachability).

The correspondence between these files and the paper is as follows:
- langdef.v: Section 3
- globaltypes.v: Section 3.2.
-  binary.v: Section 4
- definitions.v: First half of section 5 (the definitions)
- theorems.v: Second half of section 5 (the theorems)

The other files in this folder contain internal details of the proofs.
These files are checked by Coq and hence need not be checked to verify the correctness of the theorems.
- rtypesystem.v: Run-time type system of MPGV.
- invariant.v: Definition of the configuration invariant and various lemmas about it.
- progress.v: Lemmas showing that the invariant implies strong progress. These lemmas are used by theorems.v.
- ycombinator.v: Definition of the y-combinator that can be used to build recursive functions.
- mutil.v: Various utilities and imports.

# Difference between the paper and Coq

The Coq development is slightly more general than the paper.
In Coq, we first define a coinductive consistency relation (called [consistent] in Coq).
We then prove that this implies the consistency notion used in the paper (called [consistent_gt] in Coq), which uses global types.
This is stronger than what is in the paper, because we can potentially type check more programs using [consistent] than with [consistent_gt].
The reviewers asked for this change, and in the final version of the paper we will also use these two notions of consistency, like we already do in Coq.
