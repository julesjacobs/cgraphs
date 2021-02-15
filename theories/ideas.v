oProp := gmap endpoint chan_type
R := (gmap endpoint (chan_type * owner))
iProp := auth R -> Prop
M : owner -> oProp -> iProp
connected : owner -> owner -> iProp
own : endpoint -> chan_type -> oProp
val_typed : val -> type -> oProp

M_o P := ∃ h, ⌜⌜ P h ⌝⌝ ∗ own (◯ (λ x, (x,o)) <$> h)

M_o_(q1+q2) (P ∗ Q) ⊢ M_o_q1 P ∗ M_o_q2 Q


M_o (own e t)

M commutes with ∗ and ∃
M monotone

(* connected o o' ∗ M_o P ==∗ connected o o' ∗ M_o' P *)
own_auth Σ ∗ M_o (own c t) ∗ M_o P ==∗ own_auth Σ ∗ M_o (own c t) ∗ M_(Chan c.1) P

own_auth Σ ∗
  [∗] i, M_(Thread i)_1 (ptyped ...)
  [∗] i, M_(Chan i)_1 (bufs_typed ...)

Option 1:
- iProp and oProp both linear
- top-level adequacy statement for iProp

Option 2:
- iProp is the standard Iris iProp
- M_o_q fractional q


Definition bufs_typed (chans : heap) (Σ : heapT) (i : chan) : iProp :=
  ∃ rest, M_(Chan i) (buf_typed' (chans !! (i,true)) (Σ !! (i,true)) rest) ∗
          M_(Chan i) buf_typed' (chans !! (i,false)) (Σ !! (i,false)) (dual rest)).

Definition invariant (chans : heap) (threads : list expr) : iProp :=
  ∃ Σ, own_auth Σ ∗
       ([∗ list] id↦e∈threads, M_(Thread id) (ptyped0 e UnitT)) ∗
       ([∗ set] i∈dom_chans Σ ∪ dom_chans chans, bufs_typed chans Σ i).

Lemma own_dealloc Σ l t o :
  own_auth Σ ∗ M_o (own l t) ==∗ own_auth (delete l Σ).
Proof. Admitted.

Lemma own_alloc (i i' : nat) (l : endpoint) (Σ : heapT) (t t' : chan_type) :
  i ≠ i' →
  Σ !! l = None →
  Σ !! other l = None →
  own_auth Σ ==∗
    own_auth (<[l:=t]> $ <[other l:=t']> Σ) ∗
    M_(Thread i) (own l t) ∗ M_(Thread i') (own (other l) t').
Proof. Admitted.

Lemma own_mutate Σ l t t' o :
  own_auth Σ ∗ M_o (own l t) ==∗ own_auth (<[l:=t']> Σ) ∗ M_o (own l t').
Proof. Admitted.