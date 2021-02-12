From stdpp Require Export gmap.
From iris.bi Require Export interface.
From iris.algebra Require Import excl gmap auth.
From iris.proofmode Require Import tactics.
Require Export diris.langdef.
Require Export diris.logic.bi.
Require Import diris.util.
Ltac inv H := inversion H; clear H; simpl in *; simplify_eq.

Inductive owner :=
  | Thread : nat -> owner
  | Chan : chan -> owner.

Canonical Structure chan_typeO := leibnizO (chan_type * owner).

Notation heapT := (gmap endpoint chan_type).
Notation heapTO := (gmap endpoint (chan_type * owner)).
Notation heapTUR := (gmapUR endpoint (exclR chan_typeO)).

Notation "⌜⌜ p ⌝⌝" := (<affine> ⌜ p ⌝)%I : bi_scope.

Notation hProp := (uPred heapTUR).

Definition own (l : endpoint) (t : chan_type) (o : owner) : hProp :=
  uPred_ownM (◯ {[ l := Excl (t,o) ]}).

Definition acyclic : heapTO -> Prop. Admitted.
Definition related : heapTO -> heapT -> Prop. Admitted.

Definition own_auth (h : heapT) : hProp :=
  ∃ Δ, ⌜⌜ acyclic Δ ∧ related Δ h ⌝⌝ ∗ uPred_ownM (● (Excl <$> Δ)).

Lemma own_lookup Σ l t o :
  own_auth Σ ∗ own l t o -∗ ⌜ Σ !! l = Some t ⌝.
Proof. Admitted.

Lemma own_dealloc Σ l t o :
  own_auth Σ ∗ own l t o ==∗ own_auth (delete l Σ).
Proof. Admitted.

Lemma own_alloc (i i' : nat) (l : endpoint) (Σ : heapT) (t t' : chan_type) :
  i ≠ i' →
  Σ !! l = None →
  Σ !! other l = None →
  own_auth Σ ==∗
     own_auth (<[l:=t]> $ <[other l:=t']> Σ) ∗
     own l t (Thread i) ∗ own (other l) t' (Thread i').
Proof. Admitted.

Lemma own_mutate Σ l t t' o :
  own_auth Σ ∗ own l t o ==∗ own_auth (<[l:=t']> Σ) ∗ own l t' o.
Proof. Admitted.

Lemma own_move_tc Σ c t i t' l :
  own_auth Σ ∗
  own c t (Thread i) ∗
  own l t' (Thread i)
  ==∗
  own_auth Σ ∗
  own c t (Thread i) ∗
  own l t' (Chan c.1).
Proof. Admitted.

Lemma own_move_ct Σ c t i t' l :
  own_auth Σ ∗
  own c t (Thread i) ∗
  own l t' (Chan c.1)
  ==∗
  own_auth Σ ∗
  own c t (Thread i) ∗
  own l t' (Thread i).
Proof. Admitted.


(*
Operations we need:
===================
Σ : gmap endpoint chan_type

own_auth Σ :=
  ∃ Δ : gmap endpoint (chan_type * owner), uPred_ownM (● Δ) ∗ acyclic (mk_graph Δ) ∗ related Σ Δ

own_auth Σ ∗ own l t o -∗ own_auth (delete l Σ)                               -- for close
own_auth Σ ∗ own l t o -∗ ⌜ Σ !! l = Some t ⌝                                 -- used many times in the proof

Σ !! l = None → Σ !! other l = None → own_auth Σ ⊢ |==> own_auth (<[l:=t]> Σ) ∗ own l t (Thread i)           -- for fork (alloc)

i ≠ i' → Σ !! other l = None → own_auth Σ ∗ own l t (Thread i) ⊢
  |==> own_auth (<[other l:=t]> Σ) ∗ own l t (Thread i) ∗ own (other l) t (Thread i')           -- for fork (alloc)


Σ !! l = None →
Σ !! other l = None →
i ≠ i' →
own_auth Σ ⊢
  |==> own_auth (<[l:=t]> <[other l:= t']> Σ) ∗
       own l t (Thread i) ∗ own (other l) t' (Thread i')



own_auth Σ ∗ own l t o ⊢ |==> own_auth (<[l:=t']> Σ) ∗ own l t' o             -- for send/recv (updating the type)


"connected o o'" ∗ own_auth Σ ∗ own l t o ⊢ |==> own_auth Σ ∗ own l t o'        -- for moving resources to a new owner (fork/send/recv)

SEND:

l
|
i --- c

      l
      |
i --- c

own_auth Σ
own (c,b) t (Thread i)
own l t' (Thread i)
==∗
own_auth Σ
own (c,b) t (Thread i)
own l t' (Chan c)

RECV:


      l
      |
i --- c

l
|
i --- c

own_auth Σ
own (c,b) t (Thread i)
own l t' (Chan c)
==∗
own_auth Σ
own (c,b) t (Thread i)
own l t' (Thread i)

FORK:

F
|
i -- c -- i'

          F
          |
i -- c -- i'

SEND+RECV



(own_auth ∅ ⊢ |==> ⌜ φ ⌝) → φ                                                 -- simple adequacy for safety
(own_auth ∅ ⊢ |==> ∃ Σ2, own_auth Σ2 ∧ ⌜ φ Σ2 ⌝) → φ ∅                        -- adequacy for leak freedom
adequacy for deadlocks??

Definition invariant (chans : heap) (threads : list expr) : hProp :=
  ∃ Σ, own_auth Σ ∗
       ([∗ list] id↦e∈threads, ptyped0 e UnitT (Thread id)) ∗
       heap_typed chans Σ.

Leak freedom:

Definition invariant (chans : heap) (threads : list expr) : hProp :=
  ∃ Σ, own_auth Σ ∗
       heap_typed chans Σ.

heap_typed chans Σ -∗ ∃ stuff, [∗ stuff'] s, own [..] (Chan c)

We want to have (only channels exist -> contradiction).

M(P) := λ x, global_valid x ∧ P x
G := λ x, global_valid x
M(P) := G ∧ P

M(own_auth ∅) ⊢ M(|==> ∃ Σ, own_auth Σ ∗ stuff(Σ))

Possibilities:
1) Use current adequacy lemma for uPred_ownM
  a) Find new adequacy lemma for uPred auth
2) Use more internal version (like Iron)
3) Use Iron

*)

Lemma strong_adequacy {A : ucmraT} (φ : A -> A -> Prop) :
  (uPred_ownM (● ε) ⊢ |==> ∃ x y, uPred_ownM (● x ⋅ ◯ y) ∧ ⌜ φ x y ⌝) → ∃ x, φ x x.
Proof.
Admitted.

Lemma P_to_own_frag {A : ucmraT} (x : A) (P : uPred A) :
  uPred_ownM (● x) ∗ P ⊢ ∃ y, uPred_ownM (● x ⋅ ◯ y).
Proof.
Admitted.


(* Lemma own_ownM Σ l t o : own_auth Σ ∗ own l t o ⊣⊢ uPred_ownM (● (Excl <$> Σ) ⋅ ◯ {[ l := Excl (t,o) ]}).
Proof.
  unfold own, own_auth.
  rewrite <- uPred.ownM_op. done.
Qed. *)

(* Lemma own_lookup l t o Σ :
  own_auth Σ ∗ own l t o ⊢ ⌜ Σ !! l = Some (t,o) ⌝.
Proof.
  rewrite own_ownM.
  rewrite uPred.ownM_valid.
  rewrite uPred.discrete_valid.
  iIntros "%". iPureIntro.
  apply auth_both_valid_discrete in H as [].
  Check singleton_included_exclusive_l.
Admitted. *)
  (* apply singleton_included_exclusive_l in H; last done; last apply _.
  rewrite lookup_fmap in H.
  destruct (Σ !! l) eqn:E; simpl in *; simplify_eq. done.
Qed. *)


Lemma auth_update {A:ucmraT} (a b a' b' : A) :
  Cancelable a →
  (a,b) ~l~> (a',b') → uPred_primitive.auth_global_update (● a ⋅ ◯ b) (● a' ⋅ ◯ b').
Proof.
  intros Hcancel Hl.
  rewrite ->local_update_unital in Hl.
  intros n [[[q z1]|] z2] [H1 H2].
  - rewrite view.view_validN_eq /= in H1.
    destruct H1 as [H _].
    apply Qp_not_add_le_l in H as [].
  - rewrite view.view_validN_eq /= in H1.
    destruct H1 as (_ & x & ?%(inj _) & [z3 ?] & ?).
    apply (inj Some) in H2 as [_ ?%(inj to_agree)]; simpl in *.
    ofe_subst x.
    assert (z3 ≡{n}≡ ε).
    {
      apply Hcancel; first by rewrite H3.
      by rewrite {1}H3 H0 right_id.
    }
    ofe_subst z3.
    rewrite-> !(left_id _ _) in H3, H0, H1.
    rewrite-> !(right_id _ _) in H0, H1.
    destruct (Hl n z2).
    { by rewrite H0. }
    { done. }
    split.
    + rewrite view.view_validN_eq /=.
      split; first done.
      exists a'.
      split; first done.
      split; last done.
      rewrite left_id. by rewrite H2.
    + simpl in *.
      do 2 constructor; simpl; first done.
      f_equiv.
      by rewrite left_id.
Qed.

Lemma auth_update_alloc {A:ucmraT} (a a' b' : A) :
  Cancelable a →
  (a,ε) ~l~> (a',b') → uPred_primitive.auth_global_update (● a) (● a' ⋅ ◯ b').
Proof.
  intros Hcancel Hl.
  eapply uPred_primitive.auth_global_update_proper, auth_update, Hl; auto.
  rewrite (_ : (◯ ε) = ε); last done.
  by rewrite right_id.
Qed.

(* Lemma allocate Σ l t o :
  Σ !! l = None →
  own_auth Σ ⊢ |==> own_auth (<[l:=(t,o)]> Σ) ∗ own l t o.
Proof.
  intros H.
  rewrite own_ownM.
  apply uPred.bupd_ownM_update.
  apply auth_update_alloc; first apply _.
  rewrite fmap_insert.
Admitted. *)
  (* Check alloc_singleton_local_update.
  apply alloc_singleton_local_update; last done.
  by rewrite lookup_fmap H.
Qed. *)

Lemma auth_update_dealloc {A:ucmraT} (a b a' : A) :
  Cancelable a →
  (a,b) ~l~> (a',ε) → uPred_primitive.auth_global_update (● a ⋅ ◯ b) (● a').
Proof.
  intros Hcancel Hl.
  eapply uPred_primitive.auth_global_update_proper, auth_update, Hl; auto.
  rewrite (_ : (◯ ε) = ε); last done.
  by rewrite right_id.
Qed.

(* Lemma deallocate Σ l t o :
  own_auth Σ ∗ own l t o ⊢ |==> own_auth (delete l Σ).
Proof.
  iIntros "H".
  iDestruct (own_lookup with "H") as "%".
  iStopProof.
  rewrite own_ownM.
  apply uPred.bupd_ownM_update.
  apply auth_update_dealloc; first apply _.
  rewrite fmap_delete.
Admitted.
  apply delete_singleton_local_update_cancelable; first apply _.
  rewrite lookup_fmap. rewrite H. done.
Qed. *)

(* Lemma update Σ l t t' :
  own_auth Σ ∗ own l t ⊢
  |==> own_auth (<[l:=t']> Σ) ∗ own l t'.
Proof.
  iIntros "[H1 H2]".
  iApply bupd_trans.
  replace (<[l:=t']> Σ) with (<[l := t']> (delete l Σ))
    by apply fin_maps.insert_delete.
  iApply allocate. { apply lookup_delete. }
  iApply deallocate. iFrame.
Qed. *)


(* Lemma adequacy φ :
  (own_auth ∅ ⊢ |==> ∃ Σ2, own_auth Σ2 ∧ ⌜ φ Σ2 ⌝) → φ ∅.
Proof.
  unfold own_auth.
  intros HH.
  destruct (uPred.ownM_soundness (M:= heapTUR) (● ε)
    (λ x, ∃ y, x ≡ ● (Excl <$> y) ∧ φ y)) as [x [H1 [y [H2 H3]]]].
  - apply _.
  - split; last done.
    by apply auth_auth_validN.
  - iIntros "H".
    iMod (HH with "[H]") as (Σ) "[H %]".
    + by rewrite fmap_empty.
    + iExists (● (Excl <$> Σ)). iFrame.
      iModIntro. iSplit; first done.
      iPureIntro.
      by exists Σ.
  - unfold uPred_primitive.auth_global_updateN in H1.
    destruct (H1 ε) as [R1 R2].
    { split. rewrite right_id. by apply auth_auth_validN.
      simpl. by rewrite !right_id. }
    simpl in *.
    rewrite right_id in R2.
    rewrite-> H2 in R2.
    simpl in *.
    apply (inj Some) in R2 as [_ R2]. simpl in *.
    apply (inj to_agree) in R2.
    rewrite-> (left_id _ _) in R2.
    apply (discrete _) in R2.
    apply leibniz_equiv_iff in R2.
    by apply (fmap_empty_inv Excl) in R2 as ->.
Qed. *)

Lemma auth_global_valid_auth {A : ucmraT} n :
  auth_global_valid n (● (ε : A)).
Proof.
  split; last done.
  apply auth_auth_validN. apply ucmra_unit_validN.
Qed.

Lemma simple_adequacy φ :
  (own_auth ∅ ⊢ |==> ⌜ φ ⌝) → φ.
Proof. Admitted.
  (* unfold own_auth.
  apply uPred.ownM_simple_soundness.
  rewrite fmap_empty.
  apply: auth_global_valid_auth.
Qed. *)

Fixpoint ptyped (Γ : envT) (e : expr) (t : type) (o : owner) : hProp :=
 match e with
  | Val v =>
      ⌜⌜ Γ = ∅ ⌝⌝ ∗ val_typed v t o
  | Var x =>
      ⌜⌜ Γ = {[ x := t ]} ⌝⌝
  | App e1 e2 => ∃ t' Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
      ptyped Γ1 e1 (FunT t' t) o ∗
      ptyped Γ2 e2 t' o
  | Lam x e => ∃ t1 t2,
      ⌜⌜ t = FunT t1 t2 ∧ Γ !! x = None ⌝⌝ ∗
      ptyped (Γ ∪ {[ x := t1 ]}) e t2 o
  | Send e1 e2 => ∃ r t' Γ1 Γ2,
      ⌜⌜ t = ChanT r ∧ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
      ptyped Γ1 e1 (ChanT (SendT t' r)) o ∗
      ptyped Γ2 e2 t' o
  | Recv e => ∃ t' r,
      ⌜⌜ t = PairT (ChanT r) t' ⌝⌝ ∗
      ptyped Γ e (ChanT (RecvT t' r)) o
  | Let x e1 e2 => ∃ (t' : type) (Γ1 Γ2 : envT),
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ∧ Γ2 !! x = None ⌝⌝ ∗
      ptyped Γ1 e1 t' o ∗
      ptyped (Γ2 ∪ {[ x := t' ]}) e2 t o
  | LetUnit e1 e2 => ∃ Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
      ptyped Γ1 e1 UnitT o ∗
      ptyped Γ2 e2 t o
  | LetProd x1 x2 e1 e2 => ∃ t1 t2 Γ1 Γ2,
      ⌜⌜ x1 ≠ x2 ∧ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ∧ Γ2 !! x1 = None ∧ Γ2 !! x2 = None  ⌝⌝ ∗
      ptyped Γ1 e1 (PairT t1 t2) o ∗
      ptyped (Γ2 ∪ {[ x1 := t1 ]} ∪ {[ x2 := t2 ]}) e2 t o
  | If e1 e2 e3 => ∃ Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
      ptyped Γ1 e1 NatT o ∗
      (ptyped Γ2 e2 t o ∧ ptyped Γ2 e3 t o)
  | Fork e => ∃ r,
      ⌜⌜ t = ChanT r ⌝⌝ ∗
      ptyped Γ e (FunT (ChanT (dual r)) UnitT) o
  | Close e =>
      ⌜⌜ t = UnitT ⌝⌝ ∗ ptyped Γ e (ChanT EndT) o
  end
with val_typed (v : val) (t : type) (o : owner) : hProp := (* extra argument: owner*)
  match v with
  | UnitV => ⌜⌜ t = UnitT ⌝⌝
  | NatV n => ⌜⌜ t = NatT ⌝⌝
  | PairV a b => ∃ t1 t2, ⌜⌜ t = PairT t1 t2 ⌝⌝ ∗ val_typed a t1 o ∗ val_typed b t2 o
  | FunV x e => ∃ t1 t2, ⌜⌜ t = FunT t1 t2 ⌝⌝ ∗ ptyped {[ x := t1 ]} e t2 o
  | ChanV c => ∃ r, ⌜⌜ t = ChanT r ⌝⌝ ∗ own c r o (* own c r owner *)
  end.

Lemma typed_ptyped Γ e t o : ⌜⌜ typed Γ e t ⌝⌝ -∗ ptyped Γ e t o.
Proof.
  iIntros "%".
  iInduction H as [] "IH"; simpl;
  repeat iExists _;
  repeat (iSplitL || iSplit);
  (by iPureIntro || iAssumption).
Qed.

Lemma union_lr_None `{Countable K} {V} (A B C : gmap K V) x :
  C = A ∪ B ∧ A ##ₘ B ->
  C !! x = None ->
  A !! x = None ∧ B !! x = None.
Proof.
  intros [-> Hdisj] Hl.
  by apply lookup_union_None in Hl.
Qed.

Lemma union_lr_Some `{Countable K} {V} (A B C : gmap K V) x v :
  C = A ∪ B ∧ A ##ₘ B ->
  C !! x = Some v ->
  (A !! x = Some v ∧ B !! x = None) ∨ (B !! x = Some v ∧ A !! x = None).
Proof.
  intros [-> Hdisj] Hl.
  apply lookup_union_Some in Hl as []; eauto; [left | right]; split; eauto;
  rewrite ->map_disjoint_alt in Hdisj; specialize (Hdisj x);
  destruct (A !! x); naive_solver.
Qed.

Ltac foo := simpl; repeat iMatchHyp (fun H P =>
  lazymatch P with
  | ⌜⌜ _ ⌝⌝%I => iDestruct H as %?
  end); simplify_map_eq.

Lemma typed_no_var_subst e Γ t x v o :
  Γ !! x = None ->
  ptyped Γ e t o -∗
  ⌜ subst x v e = e ⌝.
Proof.
  iIntros (Hx) "Ht".
  iInduction e as [] "IH" forall (Γ t Hx); foo.
  - done.
  - done.
  - iDestruct "Ht" as (t' Γ1 Γ2  [-> ?]) "[H1 H2]".
    iDestruct ("IH" with "[%] H1") as %?.
    { by apply lookup_union_None in Hx as []. }
    iDestruct ("IH1" with "[%] H2") as %?.
    { by apply lookup_union_None in Hx as []. }
    by rewrite H0 H1.
  - case_decide;[done|].
    iDestruct "Ht" as (t1 t2 [-> ?]) "H".
    iDestruct ("IH" with "[%] H") as %?.
    + rewrite lookup_union. rewrite Hx lookup_singleton_ne; eauto.
    + rewrite H1. done.
  - iDestruct "Ht" as (r t' Γ1 Γ2 (-> & -> & Hdisj)) "[H1 H2]".
    apply lookup_union_None in Hx as [].
    iDestruct ("IH" with "[%] H1") as %?; first done.
    iDestruct ("IH1" with "[%] H2") as %?; first done.
    by rewrite H1 H2.
  - iDestruct "Ht" as (t' r ->) "H".
    iDestruct ("IH" with "[%] H") as %?; eauto.
    by rewrite H.
  - iDestruct "Ht" as (t' Γ1 Γ2 (-> & Hdisj & Hnone)) "[H1 H2]".
    iDestruct ("IH" with "[%] H1") as %?.
    { by apply lookup_union_None in Hx as []. }
    rewrite H.
    case_decide;[done|].
    iDestruct ("IH1" with "[%] H2") as %?.
    { rewrite lookup_union. apply lookup_union_None in Hx as [].
      rewrite H2. rewrite lookup_singleton_ne; done. }
    by rewrite H1.
  - iDestruct "Ht" as (Γ1 Γ2 (-> & Hdisj)) "[H1 H2]".
    apply lookup_union_None in Hx as [].
    iDestruct ("IH" with "[%] H1") as %?; eauto.
    iDestruct ("IH1" with "[%] H2") as %?; eauto.
    by rewrite H1 H2.
  - iDestruct "Ht" as (t1 t2 Γ1 Γ2 (Hneq & -> & Hdisj & Hs1 & Hs2)) "[H1 H2]".
    apply lookup_union_None in Hx as [].
    iDestruct ("IH" with "[%] H1") as %?; eauto.
    rewrite H1.
    case_decide;[done|].
    iDestruct ("IH1" with "[%] H2") as %?.
    { rewrite !lookup_union H0 !lookup_singleton_ne; eauto. }
    by rewrite H3.
  - iDestruct "Ht" as (Γ1 Γ2 [-> Hdisj]) "[H1 H2]".
    apply lookup_union_None in Hx as [].
    iDestruct ("IH" with "[%] H1") as %?; eauto. rewrite H1.
    clear H.
    iDestruct ("IH1" with "[%] [H2]") as %?; eauto.
    { iDestruct "H2" as "[H2 _]". done. }
    iDestruct ("IH2" with "[%] [H2]") as %?; eauto.
    { iDestruct "H2" as "[_ H2]". done. }
    by rewrite H H2.
  - iDestruct "Ht" as (r ->) "H".
    iDestruct ("IH" with "[%] H") as %?; eauto.
    by rewrite H.
  - iDestruct "Ht" as "[_ Ht]".
    iDestruct ("IH" with "[%] Ht") as %?; eauto.
    by rewrite H.
Qed.

Lemma delete_union_l `{Countable K} {V} (a b : gmap K V) (x : K) :
  a ##ₘ b -> b !! x = None -> delete x (a ∪ b) = delete x a ∪ b ∧ delete x a ##ₘ b.
Proof.
  intros ??.
  rewrite delete_union.
  rewrite (delete_notin b x); solve_map_disjoint.
Qed.

Lemma delete_union_r `{Countable K} {V} (a b : gmap K V) (x : K) :
  a ##ₘ b -> a !! x = None -> delete x (a ∪ b) = a ∪ delete x b ∧ a ##ₘ delete x b.
Proof.
  intros ??.
  rewrite delete_union.
  rewrite (delete_notin a x); solve_map_disjoint.
Qed.

Lemma subst_ptyped (Γ : envT) (x : string) (v : val) (vT : type) (e : expr) (eT : type) (o : owner):
  Γ !! x = Some vT ->
  val_typed v vT o -∗
  ptyped Γ e eT o -∗
  ptyped (delete x Γ) (subst x v e) eT o.
Proof.
  iIntros (H) "Hv He".
  iInduction e as [?|?|?|?|?|?|?|?|?|?|?|?] "IH" forall (eT Γ H); simpl.
  - iDestruct "He" as "[% H']". simplify_map_eq.
  - iDestruct "He" as "%". simplify_map_eq. iFrame.
    iPureIntro. apply delete_singleton.
  - iDestruct "He" as (t' Γ1 Γ2 [-> ?]) "(He1 & He2)".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + iExists _,_,_. iSplit.
      { iPureIntro. by apply delete_union_l. }
      iSplitL "He1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { by iDestruct (typed_no_var_subst with "He2") as %->. }
    + iExists _,_,_. iSplit.
      { iPureIntro. by apply delete_union_r. }
      iSplitR "He2 Hv".
      { by iDestruct (typed_no_var_subst with "He1") as %->. }
      { by iApply ("IH1" with "[%] Hv"). }
  - iDestruct "He" as (t1 t2 (-> & Hs)) "H".
    case_decide.
    + simplify_eq.
    + simpl. iExists _,_. iSplit.
      { iPureIntro. split; eauto. rewrite lookup_delete_None. eauto. }
      { replace (delete x Γ ∪ {[s := t1]}) with (delete x (Γ ∪ {[s := t1]})).
        iApply ("IH" with "[%] Hv H").
        - rewrite lookup_union. rewrite H. rewrite lookup_singleton_ne; eauto.
        - rewrite delete_union. rewrite delete_singleton_ne; eauto. }
  - iDestruct "He" as (r t' Γ1 Γ2 (-> & -> & ?)) "[H1 H2]".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + iExists _,_,_,_. iSplit.
      { iPureIntro. split; eauto. by apply delete_union_l. }
      iSplitL "H1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { by iDestruct (typed_no_var_subst with "H2") as %->. }
    + iExists _,_,_,_. iSplit.
      { iPureIntro. split; eauto. by apply delete_union_r. }
      iSplitR "H2 Hv".
      { by iDestruct (typed_no_var_subst with "H1") as %->. }
      { by iApply ("IH1" with "[%] Hv"). }
  - iDestruct "He" as (t r ->) "H".
    iExists _,_. iSplit. done.
    iApply ("IH" with "[%] Hv H"). done.
  - iDestruct "He" as (t' Γ1 Γ2 (-> & ? & ?)) "[H1 H2]".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. split. by apply delete_union_l. split; eauto.
        solve_map_disjoint. }
      iSplitL "H1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { case_decide. done.
        iDestruct (typed_no_var_subst e2 _ _ _ v with "H2") as %?.
        - rewrite lookup_union.
          rewrite lookup_singleton_ne; last done.
          rewrite H2. done.
        - rewrite H4. done. }
    + iExists _,_,_. iSplit.
      { iPureIntro. split. by apply delete_union_r. split.
        + solve_map_disjoint.
        + rewrite lookup_delete_None. eauto. }
      iSplitR "H2 Hv".
      { by iDestruct (typed_no_var_subst with "H1") as %->. }
      { case_decide. simplify_eq.
        replace (delete x Γ2 ∪ {[s := t']}) with (delete x (Γ2 ∪ {[s := t']})).
        - iApply ("IH1" with "[%] Hv H2").
          rewrite lookup_union. rewrite H. rewrite lookup_singleton_ne; eauto.
        - rewrite delete_union. rewrite delete_singleton_ne; eauto. }
  - iDestruct "He" as (Γ1 Γ2 (-> & ?)) "[H1 H2]".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. apply delete_union_l; eauto. }
      iSplitL "H1 Hv".
      { iApply ("IH" with "[%] Hv H1"). done. }
      { iDestruct (typed_no_var_subst with "H2") as %->; eauto. }
    + repeat iExists _. iSplit.
      { iPureIntro. apply delete_union_r; eauto. }
      iSplitL "H1".
      { iDestruct (typed_no_var_subst with "H1") as %->; eauto. }
      { iApply ("IH1" with "[%] Hv H2"). done. }
  - iDestruct "He" as (t1 t2 Γ1 Γ2 (Hneq & -> & ? & ? & ?)) "[H1 H2]".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. split;eauto. split. apply delete_union_l; eauto.
        solve_map_disjoint. }
      iSplitL "H1 Hv".
      { iApply ("IH" with "[%] Hv H1"). done. }
      { case_decide.
        - done.
        - iDestruct (typed_no_var_subst with "H2") as %->; eauto.
          rewrite !lookup_union. rewrite H3.
          rewrite !lookup_singleton_ne; eauto. }
    + repeat iExists _. iSplit.
      { iPureIntro. split;eauto. split. apply delete_union_r; eauto.
        split. solve_map_disjoint.
        rewrite !lookup_delete_None. eauto. }
      iSplitL "H1".
      { iDestruct (typed_no_var_subst with "H1") as %->; eauto. }
      { case_decide.
        - destruct H4; subst; simplify_eq.
        - replace (delete x Γ2 ∪ {[s := t1]} ∪ {[s0 := t2]}) with
                  (delete x (Γ2 ∪ {[s := t1]} ∪ {[s0 := t2]})).
          { iApply ("IH1" with "[%] Hv H2").
            rewrite !lookup_union. rewrite H.
            rewrite !lookup_singleton_ne; eauto. }
          { rewrite !delete_union. rewrite !delete_singleton_ne; eauto. } }
  - iDestruct "He" as (Γ1 Γ2 (-> & ?)) "[H1 H2]".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. apply delete_union_l; eauto. }
      iSplitL "H1 Hv".
      { iApply ("IH" with "[%] Hv H1"). done. }
      { iDestruct (typed_no_var_subst e2 with "[H2]") as %->.
        - exact H1.
        - iDestruct "H2" as "[H _]". eauto.
        - iDestruct (typed_no_var_subst e3 with "[H2]") as %->.
          + exact H1.
          + iDestruct "H2" as "[_ H]". eauto.
          + done. }
    + repeat iExists _. iSplit.
      { iPureIntro. apply delete_union_r; eauto. }
      iSplitL "H1".
      { iDestruct (typed_no_var_subst with "H1") as %->; eauto. }
      { iSplit.
        - iDestruct "H2" as "[H _]".
          iApply ("IH1" with "[%] Hv H"). done.
        - iDestruct "H2" as "[_ H]".
          iApply ("IH2" with "[%] Hv H"). done. }
  - iDestruct "He" as (r ->) "H".
    iExists _. iSplit.
    { iPureIntro. done. }
    { iApply ("IH" with "[%] Hv H"). done. }
  - iDestruct "He" as "[% He]".
    iSplit; first done.
    iApply ("IH" with "[%] Hv He"). done.
Qed.

(* Definition ctx_typed (Γ : envT) (k : expr -> expr)
                     (A : type) (B : type) : hProp :=
    (∀ e Γ',
      ⌜⌜ Γ ##ₘ Γ' ⌝⌝ -∗
      ptyped Γ' e A -∗
      ptyped (Γ ∪ Γ') (k e) B)%I.

Lemma md1 (Γ : envT) :
  Γ = ∅ ∪ Γ ∧ ∅ ##ₘ Γ.
Proof.
  rewrite left_id. solve_map_disjoint.
Qed.

Lemma md2 (Γ1 Γ2 : envT) :
  Γ1 ##ₘ Γ2 ->
  Γ1 ∪ Γ2 = Γ2 ∪ Γ1 ∧ Γ2 ##ₘ Γ1.
Proof.
  intro. rewrite map_union_comm; solve_map_disjoint.
Qed.

Ltac smd := solve_map_disjoint || (rewrite map_union_comm; solve_map_disjoint).

Lemma ctx_subst Γ1 Γ2 k A B e :
  Γ1 ##ₘ Γ2 -> ctx_typed Γ1 k A B -∗ ptyped Γ2 e A -∗ ptyped (Γ1 ∪ Γ2) (k e) B.
Proof.
  intros Hdisj.
  iIntros "Hctx Htyped".
  unfold ctx_typed.
  iApply "Hctx".
  - iPureIntro. done.
  - iFrame.
Qed. *)

(* Lemma typed_ctx1_typed Γ B k e :
  ctx1 k -> ptyped Γ (k e) B -∗
  ∃ Γ1 Γ2 A,
    ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
    ctx_typed Γ1 k A B ∗ ptyped Γ2 e A.
Proof.
  intros [];
  simpl;
  iIntros "Htyped";
  repeat (iDestruct "Htyped" as (?) "Htyped");
  try iDestruct "Htyped" as "[H1 H2]";
  try iDestruct "H1" as (->) "H1"; subst;
  try destruct H; try destruct H0; subst;
  repeat iExists _; iFrame; iSplit;
  eauto using md1, md2;
  try solve [
    repeat iIntros (?); repeat iIntros "?";
    simpl; rewrite ?left_id;
    repeat iExists _; iSplit;
    iFrame; eauto using md1, md2; iPureIntro; smd
  ].
  repeat iIntros (?); repeat iIntros "?". rewrite left_id. simpl. iFrame.
Qed. *)

(* Lemma typed_ctx_typed Γ B k e :
  ctx k -> ptyped Γ (k e) B -∗
  ∃ Γ1 Γ2 A,
    ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
    ctx_typed Γ1 k A B ∗ ptyped Γ2 e A.
Proof.
  intros Hctx.
  iIntros "Htyped".
  iInduction Hctx as [] "IH" forall (Γ B).
  - repeat iExists _. iFrame.
    iSplit. eauto using md1.
    repeat iIntros (?). repeat iIntros "?".
    rewrite left_id. done.
  - iDestruct (typed_ctx1_typed with "Htyped") as "H"; eauto.
    iDestruct "H" as (Γ1 Γ2 A (-> & ?)) "[H1 H2]".
    iDestruct ("IH" with "H2") as (Γ0 Γ3 A0 (-> & ?)) "[H3 H4]".
    repeat iExists _. iFrame.
    iSplit.
    + iPureIntro. split.
      * rewrite assoc. reflexivity.
      * solve_map_disjoint.
    + repeat iIntros (?). iIntros "?". unfold ctx_typed.
      replace (Γ1 ∪ Γ0 ∪ Γ') with (Γ1 ∪ (Γ0 ∪ Γ')) by (by rewrite assoc).
      iApply "H1". iPureIntro. solve_map_disjoint.
      iApply "H3". solve_map_disjoint. done.
Qed. *)

(* ptyped with empty environment *)

Fixpoint ptyped0 (e : expr) (t : type) (o : owner): hProp :=
 match e with
  | Val v =>
      val_typed v t o
  | Var x =>
      False
  | App e1 e2 => ∃ t',
      ptyped0 e1 (FunT t' t) o ∗
      ptyped0 e2 t' o
  | Lam x e => ∃ t1 t2,
      ⌜⌜ t = FunT t1 t2 ⌝⌝ ∗
      ptyped {[ x := t1 ]} e t2 o
  | Send e1 e2 => ∃ r t',
      ⌜⌜ t = ChanT r⌝⌝ ∗
      ptyped0 e1 (ChanT (SendT t' r)) o ∗
      ptyped0 e2 t' o
  | Recv e => ∃ t' r,
      ⌜⌜ t = PairT (ChanT r) t' ⌝⌝ ∗
      ptyped0 e (ChanT (RecvT t' r)) o
  | Let x e1 e2 => ∃ (t' : type),
      ptyped0 e1 t' o ∗
      ptyped {[ x := t' ]} e2 t o
  | LetUnit e1 e2 =>
      ptyped0 e1 UnitT o ∗
      ptyped0 e2 t o
  | LetProd x1 x2 e1 e2 => ∃ t1 t2,
      ⌜⌜ x1 ≠ x2 ⌝⌝ ∗
      ptyped0 e1 (PairT t1 t2) o ∗
      ptyped ({[ x1 := t1 ]} ∪ {[ x2 := t2 ]}) e2 t o
  | If e1 e2 e3 =>
      ptyped0 e1 NatT o ∗
      (ptyped0 e2 t o ∧ ptyped0 e3 t o)
  | Fork e => ∃ r,
      ⌜⌜ t = ChanT r ⌝⌝ ∗
      ptyped0 e (FunT (ChanT (dual r)) UnitT) o
  | Close e =>
      ⌜⌜ t = UnitT ⌝⌝ ∗ ptyped0 e (ChanT EndT) o
 end.

Lemma both_emp (A B : envT) : ∅ = A ∪ B -> A = ∅ ∧ B = ∅.
Proof.
  intros H.
  symmetry in H.
  pose proof (map_positive_l _ _ H) as H'.
  subst.
  rewrite left_id in H.
  subst.
  done.
Qed.

Lemma ptyped_ptyped0 e t o :
  ptyped ∅ e t o -∗ ptyped0 e t o.
Proof.
  iIntros "H".
  iInduction e as [] "IH" forall (t); simpl.
  - iDestruct "H" as "[_ H]". done.
  - iDestruct "H" as "%". exfalso. symmetry in H.
    eapply (map_non_empty_singleton _ _ H).
  - iDestruct "H" as (t1 Γ1 Γ2 [H1 H2]) "[H1 H2]".
    iExists t1.
    apply both_emp in H1 as [-> ->].
    iSplitL "H1".
    + iApply "IH". done.
    + iApply "IH1". done.
  - iDestruct "H" as (t1 t2 [H1 H2]) "H".
    iExists t1,t2.
    iSplit. done.
    by rewrite left_id.
  - iDestruct "H" as (r t' Γ1 Γ2 (H1 & H2 & H3)) "[H1 H2]".
    iExists r,t'.
    iSplit. done.
    apply both_emp in H2 as [-> ->].
    iSplitL "H1".
    + iApply "IH". done.
    + iApply "IH1". done.
  - iDestruct "H" as (t' r H) "H".
    iExists t',r.
    iSplit. done.
    iApply "IH". done.
  - iDestruct "H" as (t' Γ1 Γ2 ([-> ->]%both_emp & H2 & H3)) "[H1 H2]".
    iExists t'.
    iSplitL "H1".
    + iApply "IH". done.
    + rewrite left_id. done.
  - iDestruct "H" as (Γ1 Γ2 ([-> ->]%both_emp & H2)) "[H1 H2]".
    iSplitL "H1".
    + iApply "IH". done.
    + iApply "IH1". done.
  - iDestruct "H" as (t1 t2 Γ1 Γ2 (Hneq & [-> ->]%both_emp & H2 & H3)) "[H1 H2]".
    iExists t1,t2.
    iSplitL ""; eauto.
    iSplitL "H1".
    + iApply "IH". done.
    + rewrite left_id. done.
  - iDestruct "H" as (Γ1 Γ2 ([-> ->]%both_emp & H2)) "[H1 H2]".
    iSplitL "H1".
    + iApply "IH". done.
    + iSplit.
      * iDestruct "H2" as "[H _]".
        iApply "IH1". done.
      * iDestruct "H2" as "[_ H]".
        iApply "IH2". done.
  - iDestruct "H" as (r H) "H".
    iExists r.
    iSplit. done.
    iApply "IH". done.
  - iDestruct "H" as "[? H]". iFrame. iApply "IH". done.
Qed.

Lemma ptyped0_ptyped e t o :
  ptyped0 e t o -∗ ptyped ∅ e t o.
Proof.
  iIntros "H".
  iInduction e as [] "IH" forall (t); simpl.
  - iSplit; done.
  - iDestruct "H" as "%". done.
  - iDestruct "H" as (t1) "[H1 H2]".
    iExists t1,∅,∅.
    iSplit. iPureIntro. rewrite left_id. solve_map_disjoint.
    iSplitL "H1".
    + iApply "IH". done.
    + iApply "IH1". done.
  - iDestruct "H" as (t1 t2 ->) "H".
    iExists t1,t2.
    iSplit. done.
    by rewrite left_id.
  - iDestruct "H" as (r t' ->) "[H1 H2]".
    iExists r,t',∅,∅.
    iSplit. iPureIntro. rewrite left_id. solve_map_disjoint.
    iSplitL "H1".
    + iApply "IH". done.
    + iApply "IH1". done.
  - iDestruct "H" as (t' r ->) "H".
    iExists t',r.
    iSplit. done.
    iApply "IH". done.
  - iDestruct "H" as (t') "[H1 H2]".
    iExists t',∅,∅.
    iSplit. iPureIntro. rewrite left_id. solve_map_disjoint.
    iSplitL "H1".
    + iApply "IH". done.
    + rewrite left_id. done.
  - iDestruct "H" as "[H1 H2]".
    iExists ∅,∅.
    iSplit. iPureIntro. rewrite left_id. solve_map_disjoint.
    iSplitL "H1".
    + iApply "IH". done.
    + iApply "IH1". done.
  - iDestruct "H" as (t1 t2 Hneq) "[H1 H2]".
    iExists t1,t2,∅,∅.
    iSplit. iPureIntro. rewrite left_id. solve_map_disjoint.
    iSplitL "H1".
    + iApply "IH". done.
    + rewrite left_id. done.
  - iDestruct "H" as "[H1 H2]".
    iExists ∅,∅.
    iSplit. iPureIntro. rewrite left_id. solve_map_disjoint.
    iSplitL "H1".
    + iApply "IH". done.
    + iSplit.
      * iDestruct "H2" as "[H _]".
        iApply "IH1". done.
      * iDestruct "H2" as "[_ H]".
        iApply "IH2". done.
  - iDestruct "H" as (r ->) "H".
    iExists r.
    iSplit. done.
    iApply "IH". done.
  - iDestruct "H" as "[? H]". iFrame. iApply "IH". done.
Qed.


Definition ctx_typed0 (k : expr -> expr)
                     (A : type) (B : type) (o : owner) : hProp :=
    ∀ e,
      ptyped0 e A o -∗
      ptyped0 (k e) B o.

Lemma ctx_subst0 k A B e o :
  ctx_typed0 k A B o -∗ ptyped0 e A o -∗ ptyped0 (k e) B o.
Proof.
  iIntros "Hctx Htyped".
  unfold ctx_typed0.
  iApply "Hctx". done.
Qed.

(* Lemma ctx_typed_ctx_typed0 k A B :
  ctx_typed ∅ k A B -∗ ctx_typed0 k A B.
Proof.
  iIntros "H" (e) "HH".
  iApply ptyped_ptyped0.
  unfold ctx_typed.
  replace (ptyped ∅ (k e) B) with (ptyped (∅ ∪ ∅) (k e) B) by (by rewrite left_id).
  iApply ("H" with "[%] [HH]"). solve_map_disjoint.
  iApply ptyped0_ptyped. done.
Qed. *)

Lemma typed0_ctx1_typed0 B k e o :
  ctx1 k -> ptyped0 (k e) B o -∗
  ∃ A, ctx_typed0 k A B o ∗ ptyped0 e A o.
Proof.
  iIntros (Hctx) "H".
  destruct Hctx; simpl;
  repeat iDestruct "H" as (?) "H";
  repeat iDestruct "H" as "[? H]";
  repeat iExists _; iFrame;
  try iIntros (e1) "H1"; simpl;
  repeat iExists _; iFrame;
  try iPureIntro; eauto.
Qed.

Lemma typed0_ctx_typed0 B k e o :
  ctx k -> ptyped0 (k e) B o -∗
  ∃ A, ctx_typed0 k A B o ∗ ptyped0 e A o.
Proof.
  iIntros (Hctx) "H".
  iInduction Hctx as [] "IH" forall (B).
  - iExists _. iFrame. iIntros (?) "H". iFrame.
  - iDestruct (typed0_ctx1_typed0 with "H") as (A) "[Hctx H]"; first done.
    iDestruct ("IH" with "H") as (A') "[Hctx' H]".
    iExists _. iFrame. iIntros (e') "H".
    iApply "Hctx". iApply "Hctx'". done.
Qed.

(*
  Asynchronous subtyping:
  -----------------------
  ?A.!B.R < !B.?A.R


  Nat < Int

  x : Nat ==> x : Int
*)

(*
       things that #1 sent             things that #2 sent
cT1    [v1,v2]                         [w1,w2,w3]               cT2
*)