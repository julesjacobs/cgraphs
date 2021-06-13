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

Todo:
* Preservation:
  - Remove remaining admits by replacing them with Robbert's std++ lemmas
  - prove mset_σs lemmas
  - Map excl
* Progress:
  - Do proof by hand [done]
  - Figure out adequacy statement for generic invariant
  - Prove progress using that adequacy statement.
* extensions
  - rec lambdas
  - recursive sessions
  - async subtyping
  - locks
* write paper