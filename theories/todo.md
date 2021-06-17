Done:
* (5 of 5) state the generic invariant lemmas
* (5 of 5) prove the generic invariant lemmas
* (5 of 5) prove preservation using generic invariant library
* (? of ?) prove connectivity graph lemmas
  - Prove in_labels lemmas [done]
  - Refactor exchange, alloc, and dealloc to use lemmas+existentials [done]
  - Do move_multi [done]
  - Do move_bidir [done]
  - Prove the exchange, alloc, and dealloc lemmas [done]
  - Update genericinv.v to use those new lemmas
    + inv_exchange [done]
    + inv_dealloc [done]
    + inv_alloc_l [done]
    + inv_alloc_r [done]
    + update invariant2.v [done]
  - Define cgraph_wf [done]
  - Prove insert_edge_wf and delete_edge_wf and empty_wf [done]
  - Prove no_triangle [done]
  - Setoidification [done]
  - Prove rtc_list [done]
  - Define to_uforest [done]
  - Prove elem_of_to_uforest [done]
  - State induction lemma for cgraphs [done]
  - Prove induction lemma for cgraphs [done]
  - Prove progress [done]
  - prove map_to_multiset lemmas [done]
  - Map excl setoids [done]

Todo:
* Preservation:
  - Remove remaining admits by replacing them with Robbert's std++ lemmas
      [done, except multiset & union inv]
* Progress:
  - Figure out adequacy statement for generic invariant
  - Prove progress using that adequacy statement.
* extensions
  - rec lambdas
  - recursive sessions
  - choice
  - async subtyping
  - locks
* write paper

Contributions:
- Methodology using connectivity graphs to separate deadlock reasoning from type system reasoning.
- Separation logic based approach.
- Large part of the proof is generic and does not know about the language.
- Mechanized.

VEST structure.
- Formal definition of connectivity graphs
- Definition of invariant based on generic invariant
- Preservation: separation logic based local reasoning lemmas to prove preservation of the invariant.
- Progress: wf induction principle based local reasoning

Related work