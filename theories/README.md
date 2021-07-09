This repository contains the connectivity graph library (./cgraphs) and
a formalization of deadlock and leak freedom for a session typed language (./sessiontypes).

Build instructions:
-------------------
1. Install Coq 8.13.2 (https://coq.inria.fr/).
2. Install Iris dev.2021-07-07.0.ba841bb0 using opam (https://gitlab.mpi-sws.org/iris/iris/#working-with-iris).
   This is the latest development version as of writing this README. Newer development versions may or may not work.
3. Run `make`.

Structure of the development & LOC:
-----------------------------------

### Connectivity graph library:
- Utilities and data structures:
  * 224 ./cgraphs/multiset.v
  * 131 ./cgraphs/map_to_multiset.v
  * 146 ./cgraphs/mapexcl.v
  * 665 ./cgraphs/util.v
- Separation logic:
  * 459 ./cgraphs/upred.v
  * 183 ./cgraphs/bi.v
  * 153 ./cgraphs/seplogic.v
- Undirected forests:
  * 1250 ./cgraphs/uforests.v
- Connectivity graphs:
  * 1401 ./cgraphs/cgraph.v
- Generic invariant and transformation lemmas:
  * 376 ./cgraphs/genericinv.v

**Total:** 1401 + 665 + 224 + 131 + 146 + 459 + 376 + 1250 + 183 + 153 = 4988

### Language definition:
* 447  ./langdef.v

**Total:** 447 = 447

### Deadlock and leak freedom proof:
- Run-time type system:
  * 111 ./sessiontypes/langlemmas.v
  * 1284 ./sessiontypes/rtypesystem.v
- Invariant and preservation proof:
  * 359 ./sessiontypes/invariant.v
- Global progress proof:
  * 698 ./sessiontypes/progress.v
- Final theorem statement:
  * 10 ./sessiontypes/safety.v
- Y-combinator example:
  * 80 ./sessiontypes/ycombinator.v

**Total:** 1284 + 10 + 359 + 80 + 111 + 698 = 2542