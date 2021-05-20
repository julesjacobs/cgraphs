From iris.algebra Require Export cmra auth.
From iris.bi Require Export updates.
From diris Require Import bi.

Definition auth_global_valid {A : ucmra} (r : auth A) :=
  ✓ r ∧
  view_auth_proj r ≡ Some (1%Qp, to_agree (view_frag_proj r)).
Instance: Params (@auth_global_valid) 1 := {}.
Instance auth_global_valid_proper {A} :
  Proper ((≡) ==> iff) (auth_global_valid (A:=A)).
Proof.
  intros r1 r2 Hr. rewrite /auth_global_valid.
  f_equiv; by rewrite Hr.
Qed.

Lemma auth_global_valid_valid {A : ucmra} (x : auth A) :
  auth_global_valid x → ✓ x.
Proof.
  unfold auth_global_valid; naive_solver.
Qed.

Definition auth_global_update {A : ucmra} (x y : auth A) := ∀ z,
  auth_global_valid (x ⋅ z) → auth_global_valid (y ⋅ z).

Instance : Params (@auth_global_update) 1 := {}.

Instance auth_global_update_proper {A : ucmra}
  : Proper ((≡) ==> (≡) ==> iff) (auth_global_update (A:=A)).
Proof.
  intros x1 x2 Hx y1 y2 Hy. unfold auth_global_update.
  setoid_rewrite Hx.
  setoid_rewrite Hy.
  done.
Qed.

Lemma auth_global_valid_epsilon {A : ucmra} (x y : auth A) :
  CmraDiscrete A →
  (∀ (x : A), Cancelable x) →
  auth_global_valid (x ⋅ y) →
  auth_global_valid x →
  y ≡ ε.
Proof.
  (*
  Since auth_global_valid k x, we have x = (Some Σ, Σ).
  So y must be of the form (None,Σ'), and Σ ##ₘ Σ',
    otherwise (x ⋅ y) is not valid.
  So (x⋅y) = (Some Σ, Σ ∪ Σ'), but since it's global valid, we must have
    Σ = Σ ∪ Σ', but this can only be the case if Σ' = ∅, since they are disjoint.
  So y = (None, ∅) = ε.
  *)
  intros Hdiscrete Hcancel.
  unfold auth_global_valid.
  intros [? H1] [? H2].
  destruct x.
  destruct y.
  destruct view_auth_proj; simpl in *; last first.
  { inversion H2. }
  destruct p. simpl in *.
  simpl in *.
  inversion H2. simplify_eq.
  destruct H5. simpl in *.
  inversion H3. subst.
  clear H3 H2.
  rewrite ->H4 in H1. simpl in *.
  destruct view_auth_proj0.
  - destruct p. inversion H1. simplify_eq.
    inversion H5. simpl in *.
    apply Qp_add_id_free in H2 as [].
  - inversion H1. clear H1. subst.
    inversion H5. clear H5. simpl in *.
    clear H1.
    assert (to_agree view_frag_proj ≼ to_agree (view_frag_proj ⋅ view_frag_proj0)).
    { rewrite H2. reflexivity. }
    rewrite-> to_agree_included in H1.
    symmetry in H1.
    assert (view_frag_proj ≡ view_frag_proj ⋅ ε).
    { rewrite right_id. reflexivity. }
    rewrite ->H3 in H1 at 2.
    assert (view_frag_proj0 ≡ ε).
    {
      eapply cancelable; try done.
      inversion H. simpl in *.
      destruct (H6 0) as [a0 [HH1 HH2]].
      destruct HH2.
      apply cmra_discrete_valid.
      eapply cmra_validN_includedN; done.
    }
    rewrite H5. reflexivity.
Qed.

Program Definition uPred_bupd_def {M : ucmra} (Q : uPred (authUR M)) : uPred (authUR M) :=
  {| uPred_holds x := ∀ yf,
      auth_global_valid (x ⋅ yf) →
        ∃ x', auth_global_valid (x' ⋅ yf) ∧ Q x' |}.
Next Obligation.
  intros ?????. setoid_subst. done.
Qed.
Definition uPred_bupd_aux : seal (@uPred_bupd_def). Proof. by eexists. Qed.
Definition uPred_bupd := uPred_bupd_aux.(unseal).
Arguments uPred_bupd {M}.
Definition uPred_bupd_eq :
  @uPred_bupd = @uPred_bupd_def := uPred_bupd_aux.(seal_eq).

Lemma bupd_ne M : NonExpansive (@uPred_bupd M).
Proof.
  intros n P Q HPQ. simpl. rewrite uPred_bupd_eq. split. intros ??.
   split; intros HP yf ?;
    destruct (HP yf) as (x'&?&?); auto;
    exists x'; split; auto; apply HPQ; eauto;
  eapply cmra_valid_op_l; eapply auth_global_valid_valid; done.
Qed.

Definition unseal_eqs :=
  (uPred_emp_eq, uPred_pure_eq, uPred_and_eq, uPred_or_eq, uPred_impl_eq, uPred_forall_eq,
  uPred_exist_eq, uPred_sep_eq, uPred_wand_eq,
  uPred_persistently_eq, uPred_ownM_eq,
  @uPred_bupd_eq).
Ltac unseal2 :=
  unfold uPred_emp, bi_pure,
    bi_and, bi_or, bi_impl, bi_forall, bi_exist,
    bi_sep, bi_wand, bi_persistently, bi_later; simpl;
  unfold uPred_later; simpl;
  unfold uPred_emp, bupd, bi_bupd_bupd, bi_pure,
  bi_and, bi_or, bi_impl, bi_forall, bi_exist,
  bi_sep, bi_wand, bi_persistently, bi_later; simpl;
  rewrite !unseal_eqs /=.

Lemma uPred_bupd_mixin M : BiBUpdMixin (uPredI (authUR M)) uPred_bupd.
Proof.
  split.
  - exact: bupd_ne.
  - unseal2. intros ?. split. intros ???. simpl. intros ??. eauto.
  - unseal2. intros HPQ; split=> x ? HP yf ?.
    destruct (HP yf) as (x'&?&?); eauto.
    exists x'. split; first done.
    eapply uPred_in_entails; eauto.
    eapply cmra_valid_op_l. eapply auth_global_valid_valid. done.
  - unseal2. intros ?. split. intros ?? H ??. edestruct H as [? []]; eauto.
  - unseal2; split; intros ??(?&?&?&H&?)??.
    setoid_subst.
    destruct (H  (x1 ⋅ yf)) as (? & ? & ?). { rewrite assoc. done. }
    eexists. split; last first.
    + do 2 eexists. split; last eauto. done.
    + rewrite <-(assoc _ _). done.
Qed.

Global Instance uPred_bi_bupd M : BiBUpd (uPredI (authUR M)) := {| bi_bupd_mixin := uPred_bupd_mixin M |}.

Local Arguments uPred_holds {_} !_ _ /.

Lemma bupd_ownM_update {M : ucmra} (x y : auth M) :
  auth_global_update x y →
  uPred_ownM x ⊢ |==> uPred_ownM y.
Proof.
  unseal2.
  unfold auth_global_update.
  intros H. constructor.
  intros z vz Ho.
  unfold uPred_bupd_def. simpl.
  intros yf Hgv.
  eexists.
  split.
  - apply H. unfold uPred_ownM_def in Ho. simpl in Ho. setoid_subst. done.
  - reflexivity.
Qed.

Lemma ownM_simple_soundness {M : ucmra} (x : auth M) (φ : Prop) :
  auth_global_valid x →
  (uPred_ownM x ⊢ |==> ⌜ φ ⌝) →
  φ.
Proof.
  unseal2=> Hgv [H]. simpl in *.
  edestruct (H x); try done.
  - apply auth_global_valid_valid. done.
  - assert (auth_global_valid (x ⋅ ε)); last done.
    by rewrite right_id.
  - destruct H0; done.
Qed.

Lemma ownM_soundness {M : ucmra} (x : auth M) (φ : auth M → Prop) :
  (∀ x : M, Cancelable x) →
  auth_global_valid x →
  (uPred_ownM x ⊢ |==> ∃ y, uPred_ownM y ∧ ⌜ φ y ⌝) →
  ∃ y, auth_global_valid y ∧ φ y.
Proof.
  intros Hcancel.
  unseal2=> Hgv [H]. simpl in *.
  unfold auth_global_update.
  edestruct (H x).
  - apply auth_global_valid_valid. done.
  - split; reflexivity.
  - assert (auth_global_valid (x ⋅ ε)); last done.
    by rewrite right_id.
  - destruct H0 as [Hgv1 [a [H1 H2]]].
    eexists. simpl in *. split.
    + setoid_subst. rewrite-> (right_id _ _) in Hgv1. done.
    + done.
Qed.