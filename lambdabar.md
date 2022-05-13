# Artifact for ƛ: A Self-Dual Distillation of Session Types (Pearl)

Title of the submitted paper: ƛ: A Self-Dual Distillation of Session Types (Pearl)
ECOOP submission number for the paper: #67
We claim the functional and available badges.


## Artifact contents

This artifact is a Coq mechanization of the ƛ language, and of the theorems about ƛ from the paper.
It consists of Coq source code in the form of .v files.

Relevant for the artifact reviewers are these files:
* lambdabar/langdef.v -- definition of the language, operational semantics, and type system.
* lambdabar/definitions.v -- the definitions about deadlock freedom / reachability / global progress corresponding to those in the paper.
* lambdabar/theorems.v -- the proofs of the theorems in the paper.
* lambdabar/sessions.v -- the encoding of session types in ƛ.

Additionally, these proofs make use of lemmas proved in the following files and directories:
* lambdabar/langtools.v -- imports the required libraries
* lambdabar/rtypesystem.v -- definition of the run-time type system.
* lambdabar/invariant.v -- definition and proofs about the configuration invariant.
* cgraphs/**.v -- definitions and lemmas about graphs and separation logic, a modified version of [1]
These files are internal details of the proofs, which are checked by Coq, so the reviewers need not check their correctness.

We will publish the artifact on DARTS, as suggested by ECOOP's the call for artifacts.


## Getting started

To test the artifact, you need a recent version of Coq, and an installation of Iris.
We have tested it with Coq 8.14.1 and coq-iris.dev.2022-01-24.0.72a4bd62.

The installation instructions for Coq can be found at: https://coq.inria.fr/download
The installation instructions for Iris can be found at: https://gitlab.mpi-sws.org/iris/iris/#working-with-iris

We advise using opam (OCaml package manager) to install Coq and Iris.
On Unix-like platforms it can probably be installed with your OS' package manager, or on OS X with `brew install opam`.
In that case you do not need to install Coq separately; opam will install it when installing Iris.

After installing these, the development can be built with `make`.
This will let Coq check all the definitions and theorems.

## Evaluation instructions

To ascertain the correctness of the mechanization, the reviewers should check:

1. That the language definition in lambdabar/langdef.v corresponds to the language in the paper.
   There are minor differences in the presentation, e.g. in the Coq mechanization we have n-ary sum types,
   whereas we only have binary sum types in the paper. N-ary sums are strictly stronger.
   We use coinduction in Coq to model equi-recursive types. This is again strictly stronger than what is in the paper.
2. That the definitions in lambdabar/definitions.v correspond to those in the paper.
   Each definition has been labeled with a comment indicating which definition in the paper corresponds to it.
3. That the theorems in lambdabar/theorems.v correspond to those in the paper.
   Each theorem has been labeled with a comment indicating which theorem in the paper corresponds to it.
4. That the encoding of session types in lambdabar/sessions.v corresponds to the encoding in the paper.
   Here again the Coq mechanization is slightly stronger, because we mechanize n-ary choice plus message sends.
   The encoding of send/choice in the paper are special cases.
5. That Coq agrees that the theorems are correct, by running `make` without errors.


[1] https://zenodo.org/record/5675138