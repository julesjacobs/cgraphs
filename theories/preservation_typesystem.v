From stdpp Require Import gmap.
From iris.bi Require Import interface.
From iris.proofmode Require Import tactics.
Require Import diris.langdef.
Require Import diris.hprop.
Require Import diris.util.

(* ⌜ . ⌝ : Prop -> hProp
   ⌜ p ⌝ := λ Σ, p
   ⌜⌜ p ⌝⌝ := λ Σ, Σ = ∅ ∧ p *)
Notation "⌜⌜ p ⌝⌝" := (<affine> ⌜ p ⌝)%I : bi_scope.

Fixpoint ptyped (Γ : envT) (e : expr) (t : type) : hProp :=
 (match e with
  | Val v =>
      ⌜⌜ Γ = ∅ ⌝⌝ ∗ val_typed v t
  | Var x =>
      ⌜⌜ Γ = {[ x := t ]} ⌝⌝
  | App e1 e2 => ∃ t' Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
      ptyped Γ1 e1 (FunT t' t) ∗
      ptyped Γ2 e2 t'
  | Lam x e => ∃ t1 t2,
      ⌜⌜ t = FunT t1 t2 ∧ Γ !! x = None ⌝⌝ ∗
      ptyped (Γ ∪ {[ x := t1 ]}) e t2
  | Send e1 e2 => ∃ r t' Γ1 Γ2,
      ⌜⌜ t = ChanT r ∧ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
      ptyped Γ1 e1 (ChanT (SendT t' r)) ∗
      ptyped Γ2 e2 t'
  | Recv e => ∃ t' r,
      ⌜⌜ t = PairT t' (ChanT r) ⌝⌝ ∗
      ptyped Γ e (ChanT (RecvT t' r))
  | Let x e1 e2 => ∃ (t' : type) (Γ1 Γ2 : envT),
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ∧ Γ2 !! x = None ⌝⌝ ∗
      ptyped Γ1 e1 t' ∗
      ptyped (Γ2 ∪ {[ x := t' ]}) e2 t
  | LetUnit e1 e2 => ∃ Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
      ptyped Γ1 e1 UnitT ∗
      ptyped Γ2 e2 t
  | LetProd x1 x2 e1 e2 => ∃ t1 t2 Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2  ∧ Γ2 !! x1 = None ∧ Γ2 !! x2 = None ⌝⌝ ∗
      ptyped Γ1 e1 (PairT t1 t2) ∗
      ptyped (Γ2 ∪ {[ x1 := t1 ]} ∪ {[ x2 := t2 ]}) e2 t
  | If e1 e2 e3 => ∃ Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
      ptyped Γ1 e1 NatT ∗
      (ptyped Γ2 e2 t ∧ ptyped Γ2 e3 t)
  | Fork e => ∃ r,
      ⌜⌜ t = ChanT r ⌝⌝ ∗
      ptyped Γ e (FunT (ChanT (dual r)) UnitT)
  | Close e =>
      ptyped Γ e (ChanT EndT)
  end)%I
with val_typed (v : val) (t : type) : hProp :=
 (match v with
  | Unit => ⌜⌜ t = UnitT ⌝⌝
  | Nat n => ⌜⌜ t = NatT ⌝⌝
  | Pair a b => ∃ t1 t2, ⌜⌜ t = PairT t1 t2 ⌝⌝ ∗ val_typed a t1 ∗ val_typed b t2
  | Fun x e => ∃ t1 t2, ⌜⌜ t = FunT t1 t2 ⌝⌝ ∗ ptyped {[ x := t1 ]} e t2
  | Chan c => ∃ r, ⌜⌜ t = ChanT r ⌝⌝ ∗ hProp_has_type c r
  end)%I.

Lemma typed_ptyped Γ e t : ⌜⌜ typed Γ e t ⌝⌝ -∗ ptyped Γ e t.
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

Lemma typed_no_var_subst e Γ t x v :
  Γ !! x = None ->
  ptyped Γ e t -∗
  ⌜ subst x v e = e ⌝.
Proof.
  iIntros (Hx) "Ht".
  iInduction e as [] "IH" forall (Γ t Hx); foo.
  - done.
  - done.
  - iDestruct "Ht" as (t' Γ1 Γ2  [-> ?]) "[H1 H2]".
    iDestruct ("IH" with "[%] H1") as %?. { admit. }
    iDestruct ("IH1" with "[%] H2") as %?. { admit. }
    by rewrite H0 H1.
  -
Admitted.

Lemma subst_ptyped (Γ : envT) (x : string) (v : val) (vT : type) (e : expr) (eT : type) :
  Γ !! x = Some vT ->
  val_typed v vT -∗
  ptyped Γ e eT -∗
  ptyped (delete x Γ) (subst x v e) eT.
Proof.
  iIntros (H) "Hv He".
  iInduction e as [?|?|?|?|?|?|?|?|?|?|?|?] "IH" forall (eT Γ H); simpl.
  - iDestruct "He" as "[% H']". simplify_map_eq.
  - iDestruct "He" as "%". simplify_map_eq. iFrame.
    iPureIntro. apply delete_singleton.
  - iDestruct "He" as (t' Γ1 Γ2 [-> ?]) "(He1 & He2)".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + iExists _,_,_. iSplit.
      { iPureIntro. admit. }
      iSplitL "He1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { by iDestruct (typed_no_var_subst with "He2") as %->. }
    + iExists _,_,_. iSplit.
      { iPureIntro. admit. }
      iSplitR "He2 Hv".
      { by iDestruct (typed_no_var_subst with "He1") as %->. }
      { by iApply ("IH1" with "[%] Hv"). }
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Definition ctx_typed (Γ : envT) (k : expr -> expr)
                     (A : type) (B : type) : hProp :=
    (∀ e Γ',
      ⌜⌜ Γ ##ₘ Γ' ⌝⌝ -∗
      ptyped Γ' e A -∗
      ptyped (Γ ∪ Γ') (k e) B)%I.

Lemma typed_ctx_typed Γ B k e :
  ⌜⌜ ctx k ⌝⌝ -∗ ptyped Γ (k e) B -∗
  ∃ Γ1 Γ2 A,
    ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
    ctx_typed Γ1 k A B ∗ ptyped Γ2 e A.
Proof.
Admitted.

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

Definition buf_typed (buf : list val) (tys : list type) (rest : chan_type) : hProp :=
  (⌜⌜ True ⌝⌝)%I.

Definition bufs_typed (bufs : list val * list val) (ct1 ct2 : chan_type) : hProp :=
    (∃ ct:chan_type, ⌜⌜ True ⌝⌝)%I.

Definition invariant (Σ : gmap endpoint chan_type) (threads : list expr) (chans : heap) : hProp :=
  (
    ([∗ list] e∈threads, ptyped ∅ e UnitT) ∗
    ([∗ list] i↦bufs∈chans,
        bufs_typed bufs (default EndT (Σ !! (i,true))) (default EndT (Σ !! (i,false))))
  )%I.

(*
invariant : list expr -> heap -> Prop
invariant' : list expr -> heap -> hProp
invariant es h := ∃ Σ, invariant' es h Σ

init : typed ∅ e UnitT -> invariant [e] []
preservation : step es1 h1 es2 h2 -> invariant es1 h1 -> invariant es2 h2
progress : invariant es1 h1 -> (final es1 h1) ∨ ∃ es2 h2, step es1 h1 es2 h2
final es h := (∀ e, e∈es -> is_value e) ∧ ∀ b, b∈h -> b = []

GOAL:
type_safety :
  typed ∅ e UnitT ->
  steps [e] [] es h ->
  (final es h) ∨ ∃ es2 h2, step es h es2 h2

1. Deadlock freedom for session types
2. Deadlock freedom for locks + session types
3. Program logic for deadlock freedom
   a) 1&2 als logical relation
   b) put forests in the hProp

Conferences: LICS, ICFP, POPL
*)