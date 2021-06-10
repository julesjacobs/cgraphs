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
  - Define cgraph_wf
  - Prove insert_edge_wf and delete_edge_wf and empty_wf
  - State adequacy lemma for cgraphs
  - Prove adequacy lemma for cgraphs
  - Prove no_triangle [done]
  - Setoidification [done]
* (5 of 5) state the generic invariant lemmas
* (5 of 5) prove the generic invariant lemmas
* (5 of 5) prove preservation using generic invariant library
* (0 of ∞) figure out adequacy statement for generic invariant
* (0 of ∞) prove progress using that adequacy statement
* extensions
  - rec lambdas
  - recursive sessions
  - async subtyping
  - locks
* write paper