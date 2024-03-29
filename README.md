# Connectivity Graphs Coq Development

This is the repository for the Connectivity Graphs Coq development.
The source repository can be found at https://github.com/julesjacobs/cgraphs

The individual components of this repository are in the subfolders of the `theories` folder:
* theories/cgraphs: the generic connectivity graphs library on which the other developments are based.
* theories/multiparty: deadlock freedom for MPGV multiparty session types.
* theories/sessiontypes: deadlock freedom for binary session types.
* theories/lambdabar: deadlock freedom for a language with synchronous barriers.
* theories/locks: deadlock freedom for a language with locks.

The subfolders contain documentation for each of the individual developments.

To build the code, install the opam package manager, and then execute the following in the root folder:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install .

Alternatively, install the following dependencies:
* Coq
* std++
* Iris
(see cgraphs.opam for versions)

These can be installed by running:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install coq-iris

You can then compile this project with `make`.