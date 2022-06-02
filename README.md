# Connectivity Graphs Coq Development

This is the repository for the Connectivity Graphs Coq development.
The individual components are in the subfolders of the `theories` folder:
* theories/cgraphs: the generic connectivity graphs library on which the other developments are based.
* theories/sessiontypes: deadlock freedom for binary session types.
* theories/multiparty: deadlock freedom for MPGV multiparty session types.
* theories/lambdabar: deadlock freedom for a language with synchronous barriers.

The subfolders contain documentation for each of the individual developments.


To build the code, install the following dependencies:

* Coq (we tested with Coq 8.15.1)
* std++ (we tested with dev.2022-05-16.1.411eb445)
* Iris (we tested with dev.2022-05-25.0.d46e4472)

We recommend installing the `opam` package manager, and then installing the `coq-iris` package as follows:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install coq-iris

This will install the required dependencies.

You can then compile this project with `make`.