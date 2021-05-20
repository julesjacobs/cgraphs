From stdpp Require Export gmap.
From iris.bi Require Export interface.
From iris.algebra Require Import excl gmap auth.
From iris.proofmode Require Export tactics.
Require Export diris.langdef.
Require Export diris.logic.bi.
Require Export diris.util.
Require Export diris.logic.bupd.


Inductive owner :=
  | Thread : nat -> owner
  | Chan : chan -> owner.

Instance owner_eqdecision : EqDecision owner.
Proof.
  intros [n|n] [m|m]; unfold Decision; destruct (decide (n = m));
  subst; eauto; right; intro; simplify_eq.
Qed.
Instance owner_countable : Countable owner.
Proof.
  refine (inj_countable' (λ l, match l with
  | Thread n => inl n
  | Chan n => inr n
  end) (λ l, match l with
  | inl n => Thread n
  | inr n => Chan n
  end) _); by intros [].
Qed.

(* Needs to be updated *)
Canonical Structure ownerO := leibnizO owner.
Canonical Structure chan_typeO := leibnizO chan_type.

Notation heapT := (gmap endpoint chan_type).
Notation heapO := (gmap endpoint owner).
Notation heapTO := (gmap endpoint (chan_type * owner)).
Notation heapT_UR := (gmapUR endpoint (exclR chan_typeO)).
Notation heapTO_UR := (gmapUR endpoint (exclR (prodO chan_typeO ownerO))).

Notation oProp := (uPred heapT_UR).
Notation iProp := (uPred (authUR heapTO_UR)).
(* End of needs to be updated *)

(*

G : gmap A (gmap A B) "things that are owned by the first A"
M : gmap A (gmap A B) "owners of the first A"

own_auth n Δ := ∃ M G, ownM (● G) ∗ rel G M ∗ acyclic G ∗
  ⌜ G = { Thread i ↦ ∅ : i < n } ∪ { Chan c ↦ {o ↦ (t,b)} : (c,b) ↦ (t,o) ∈ Δ } ⌝

own_auth n Δ := ∃ M, ownM (● M) ∗ pred M ∗ rel M n Δ

own_auth n Δ := ∃ M G, ownM (● M) ∗ rel n Δ M ∗ acyclic M

rel n Δ M :=

acyclic G := acyclic' (sc G) ∧ asymmetric G

A := owner
B := chan_type * bool

rel G M := dom G = dom M ∧ ∀ i j, (G !! i) !!? j = (M !! j) !!? i

M (Chan x) := {singleton or doubleton}
M (Thread x) := ∅

own_auth n Δ := ∃ M G, ownM (● M) ∗ rel G M ∗ acyclic G ∗
  ⌜ G = { Thread i ↦ ∅ : i < n } ∪ { Chan c ↦ {o ↦ (t,b)} : (c,b) ↦ (t,o) ∈ Δ } ⌝

Definition invariant es h := ∃ Δ : gmap endpoint (chan_type * owner),
  own_auth (length es) Δ ∗
  ([∗] i ↦ e ∈ es,
     ∃ os, own_vertex 1 (Thread i) os ∗ ⌜ ptyped0 e UnitT os ⌝) ∗
  ([∗] l ↦ vs; sts ∈ gmap_uncurry h; gmap_uncurry Δ,
     ∃ os, own_vertex 1 (Chan l) os ∗
       ⌜ (bufs_typed (vs !! false) (sts !! false) ∗
          bufs_typed (vs !! true) (sts !! true)) ⌝ os).



Properties:
  rel ∅ ∅
  ??

own_vertex (o : owner) (g : gmap owner B)





Different representations of the labeled tree:

Δ : gmap endpoint (chan_type * owner) "what's the type and owner of an endpoint"
Δ' : gmap chan (gmap bool (chan_type * owner)) "what are the types and owners of a channel"
Δ'' : gmap chan (gmap owner (chan_type * bool))

Π : gmap owner (gmap endpoint chan_type) "what does this owner own"

Restrictions:
1. Acyclicity
2. Each active endpoint is owned once
3. If a channel is in the range of Δ, then at least one of its endpoints is in the domain
    "if a channel owns something, then at least one of its endpoints is owned by something"

The Δ-representation:
#2: implicit
#3: ∀ ep x t, Δ !! ep = None -> Δ !! other ep = None -> Δ !! x = Some(t,Chan ep.1) -> False

The Π-representation has the right shape for the resource (⋅)-structure that we want.
#2: Π !! o = Some g -> is_Some (g !! ep) -> Π !! o' = Some g' -> is_Some (g' !! ep) -> o = o'.
#3: Π !! (Chan c) -> ∃ o g, Π !! o = Some g ∧ is_Some (g !! (c,true)) ∨ is_Some (g !! (c,false))


Do we want an abstract type that represents the tree?
  With (⋅) and ✓.
  With update operations.
*)


Definition rel `{Countable A} {B} (G M : gmap A (gmap A B)) :=
  dom (gset A) G = dom (gset A) M ∧
    ∀ i j,
      (λ x, x !! j) <$> (G !! i) =
      (λ x, x !! i) <$> (M !! j).

Lemma rel_sym `{Countable A} {B} (G M : gmap A (gmap A B)) :
  rel G M <-> rel M G.
Proof. Admitted.

Lemma rel_empty `{Countable A} {B} :
  rel (∅ : gmap A (gmap A B)) (∅ : gmap A (gmap A B)).
Proof. Admitted.

(* rel_delete? rel_insert? *)



Definition own_auth : gmap owner (chan_type * owner) → iProp. Admitted.
Definition own_vertex : frac → owner → gmap owner chan_type → iProp. Admitted.

(* Send (send channel y2 over channel y1) *)

Lemma restructure_send g p q (x : owner) (y1 y2 : chan) t1 t2 b :
  own_auth g -∗
  own_vertex p x ({[ Chan y1 := t1 ]} ∪ {[ Chan y2 := t2 ]}) -∗
  own_vertex q (Chan y1) ∅
    ==∗
  own_auth (<[y2 := (t2, Chan (y1))]> g) ∗
  own_vertex p x {[ Chan y1 := t1 ]} ∗
  own_vertex q (Chan y1) {[ Chan y2 := t1 ]}.
Proof. Admitted.

Lemma restructure_recv g p q x y1 y2 t1 t2 :
  own_auth g -∗
  own_vertex p x {[ y1 := t1 ]} -∗
  own_vertex q (Chan y1.1) {[ y2 := t1 ]}
    ==∗
  own_auth (<[y2 := (t2,x)]> g) ∗
  own_vertex p x ({[ y1 := t1 ]} ∪ {[ y2 := t2 ]}) ∗
  own_vertex q (Chan y1.1) ∅.
Proof. Admitted.

Lemma restructure_fork :
  g !! x' = None → g !! y = None → x' ≠ y →
  own_auth g -∗
  own_vertex p x ∅ ==∗
    own_graph (<[x':=∅]> $ <[y:={[x,x']}]> $ g) ∗
    own_vertex p x {[ y ]} ∗
    own_vertex 1 y ∅ ∗
    own_vertex 1 x' {[ y ]}

Lemma restructure_close :
  g !! y = None →
  own_auth g -∗
  own_vertex 1 y ∅ ==∗
    own_auth (<[y:=None]> g)

Lemma mutate_type :
  own_auth g -∗
  own_vertex p x {[ y ]} ==∗
    own_auth (alter (.∖ {[ x ]}) y g) ∗
    own_vertex p x ∅

(* Validity *)

Lemma auth_acyclic g :
  own_auth g -∗ ⌜ acyclic g ⌝.
Proof. Admitted.

Lemma auth_acyclic g :
  own_auth g -∗ own_vertex p x {[ y ]} -∗ ∃ X, g !! y = Some X ∧ x ∈ X
Proof. Admitted.

Lemma auth_acyclic g :
  ⌜ p1 + p2 ≤ 1 ∧ X1 ⊥ X2 ⌝ ∗ own_vertex (p1 + p2) (X1 ∪ X2) ⊣⊢ own_vertex p1 X1 ∗ own_vertex p2 X2
Proof. Admitted.

Lemma auth_acyclic g :
  own_vertex 1 x X ∗ own_vertex 1 y Y -∗ ⌜ x ≠ y ⌝
Proof. Admitted.

Lemma auth_acyclic g :
  own_auth g ∗ own_vertex 1 x Y -∗ ⌜ ∀ y X, g !! y = Some X → x ∈ X → y ∈ Y ⌝
Proof. Admitted.

Lemma auth_acyclic g :
  dom g = dom g' →
  own_auth g ∗ ([∗ set] x ∈ Y ∈ g', own_vertex 1 x Y) -∗ ⌜ g = g' ⌝
Proof. Admitted.

(**
- What's a sensible set of validity lemmas?
- How can you prove deadlock/leak freedom in the end?
- How does the modality work?
**)

Definition owned o P := ∃ os, P os ∧ own_vertex o os.

Lemma owned_split o P Q :
  owned o (P ∗ Q) ⊣⊢ owned o P ∗ owned o Q.
Proof. Admitted.

Definition invariant es h := ∃ Δ : gmap endpoint (chan_type * owner),
  own_auth (length es) Δ ∗
  ([∗] i ↦ e ∈ es,
     ∃ os, own_vertex 1 (Thread i) os ∗ ⌜ ptyped0 e UnitT os ⌝) ∗
  ([∗] l ↦ vs; sts ∈ gmap_uncurry h; gmap_uncurry Δ,
     ∃ os, own_vertex 1 (Chan l) os ∗
       ⌜ (bufs_typed (vs !! false) (sts !! false) ∗
          bufs_typed (vs !! true) (sts !! true)) ⌝ os).


Definition acyclic Λ :=
  map_disjoint os ∧
  ∀ o ↦ os in Δ,    o ↦ dom os ∈ g

Lemma 1.
  Forall (waiting_or_value h) es →
  invariant es h -∗ ∃ g, I g

Lemma 2:
  I g -∗ J

Lemma 3 (adequacy):
  (⊢ J) → something on the meta level


if Forall (waiting_or_value h) es then
  invariant es h -∗
    (* ... *)
    ([∗] i ↦ e ∈ es, own (◯ (Thread i, ∅)) ∨
                     ∃ ch t st os, own (◯ (Thread i, {[ ch ↦ ? t. st ]} ∪ os ))) ∗
    ([∗] l ↦ vs; sts ∈ gmap_uncurry h; gmap_uncurry Δ,
      own (◯ (Chan l, ∅))
