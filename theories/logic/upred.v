From iris.algebra Require Export auth.
From iris.bi Require Import notation.
Local Hint Extern 10 (_ ≤ _) => lia : core.

Definition auth_global_valid {A : ucmraT} (k : nat) (r : auth A) :=
  ✓{k} r ∧
  view_auth_proj r ≡{k}≡ Some (1%Qp, to_agree (view_frag_proj r)).
Instance: Params (@auth_global_valid) 2 := {}.
Instance auth_global_valid_ne {A} k :
  Proper (dist k ==> iff) (auth_global_valid (A:=A) k).
Proof.
  intros r1 r2 Hr. rewrite /auth_global_valid.
  f_equiv; by rewrite Hr.
Qed.
Instance auth_global_valid_proper {A} k :
  Proper ((≡) ==> iff) (auth_global_valid (A:=A) k).
Proof. intros r1 r2. rewrite equiv_dist=> Hr. by rewrite (Hr k). Qed.

Lemma auth_global_valid_valid {A : ucmraT} k (x : auth A) :
  auth_global_valid k x → ✓{k} x.
Proof.
  unfold auth_global_valid; naive_solver.
Qed.

Lemma auth_global_valid_epsilon {A : ucmraT} k (x y : auth A) :
  (∀ (x : A), Cancelable x) →
  auth_global_valid k (x ⋅ y) →
  auth_global_valid k x →
  y ≡{k}≡ ε.
Proof.
  (*
  Since auth_global_valid k x, we have x = (Some Σ, Σ).
  So y must be of the form (None,Σ'), and Σ ##ₘ Σ',
    otherwise (x ⋅ y) is not valid.
  So (x⋅y) = (Some Σ, Σ ∪ Σ'), but since it's global valid, we must have
    Σ = Σ ∪ Σ', but this can only be the case if Σ' = ∅, since they are disjoint.
  So y = (None, ∅) = ε.
  *)
  intros Hcancel.
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
    assert (to_agree view_frag_proj ≼{k} to_agree (view_frag_proj ⋅ view_frag_proj0)).
    { rewrite H2. reflexivity. }
    rewrite-> to_agree_includedN in H1.
    symmetry in H1.
    assert (view_frag_proj ≡{k}≡ view_frag_proj ⋅ ε).
    { rewrite right_id. reflexivity. }
    rewrite ->H3 in H1 at 2.
    assert (view_frag_proj0 ≡{k}≡ ε).
    {
      eapply cancelableN; try done.
      inversion H. simpl in *.
      destruct H6 as [a0 [HH1 HH2]].
      destruct HH2.
      eapply cmra_validN_includedN; done.
    }
    rewrite H5. reflexivity.
Qed.

Record uPred (M : ucmraT) : Type := UPred {
  uPred_holds :> nat → auth M → Prop;

  uPred_mono n1 n2 x1 x2 :
    uPred_holds n1 x1 → x1 ≡{n2}≡ x2 → n2 ≤ n1 → uPred_holds n2 x2
}.
Bind Scope bi_scope with uPred.
Arguments uPred_holds {_} _%I _ _ : simpl never.
Add Printing Constructor uPred.
Instance: Params (@uPred_holds) 3 := {}.

Section cofe.
  Context {M : ucmraT}.

  Inductive uPred_equiv' (P Q : uPred M) : Prop :=
    { uPred_in_equiv : ∀ n x, ✓{n} x → P n x ↔ Q n x }.
  Instance uPred_equiv : Equiv (uPred M) := uPred_equiv'.
  Inductive uPred_dist' (n : nat) (P Q : uPred M) : Prop :=
    { uPred_in_dist : ∀ n' x, n' ≤ n → ✓{n'} x → P n' x ↔ Q n' x }.
  Instance uPred_dist : Dist (uPred M) := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin (uPred M).
  Proof.
    split.
    - intros P Q; split.
      + by intros HPQ n; split=> i x ??; apply HPQ.
      + intros HPQ; split=> n x ?; apply HPQ with n; auto.
    - intros n; split.
      + by intros P; split=> x i.
      + by intros P Q HPQ; split=> x i ??; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i x ??.
        by trans (Q i x);[apply HP|apply HQ].
    - intros n P Q HPQ; split=> i x ??; apply HPQ; auto.
  Qed.
  Canonical Structure uPredO : ofeT := OfeT (uPred M) uPred_ofe_mixin.

  Program Definition uPred_compl : Compl uPredO := λ c,
    {| uPred_holds n x := ∀ n', n' ≤ n → ✓{n'} x → c n' n' x |}.
  Next Obligation.
    move=> /= c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv. eapply uPred_mono.
    - eapply HP; [lia|]. by rewrite (dist_le _ _ _ _ Hx12); last lia.
    - eapply dist_le; eauto with lia.
    - done.
  Qed.
  Global Program Instance uPred_cofe : Cofe uPredO := {| compl := uPred_compl |}.
  Next Obligation.
    intros n c; split=>i x Hin Hv.
    etrans; [|by symmetry; apply (chain_cauchy c i n)]. split=>H; [by apply H|].
    repeat intro. apply (chain_cauchy c _ i)=>//. by eapply uPred_mono.
  Qed.
End cofe.
Arguments uPredO : clear implicits.

Instance uPred_ne {M} (P : uPred M) n : Proper (dist n ==> iff) (P n).
Proof.
  intros x1 x2 Hx; split=> ?; eapply uPred_mono; eauto; by rewrite Hx.
Qed.
Instance uPred_proper {M} (P : uPred M) n : Proper ((≡) ==> iff) (P n).
Proof. by intros x1 x2 Hx; apply uPred_ne, equiv_dist. Qed.

Lemma uPred_holds_ne {M} (P Q : uPred M) n1 n2 x :
  P ≡{n2}≡ Q → n2 ≤ n1 → ✓{n2} x → Q n1 x → P n2 x.
Proof.
  intros [Hne] ???. eapply Hne; try done. eauto using uPred_mono, cmra_validN_le.
Qed.

(** logical entailement *)
Inductive uPred_entails {M} (P Q : uPred M) : Prop :=
  { uPred_in_entails : ∀ n x, ✓{n} x → P n x → Q n x }.
Global Hint Resolve uPred_mono : uPred_def.

(** logical connectives *)
Program Definition uPred_emp_def {M} : uPred M :=
  {| uPred_holds n x := x ≡{n}≡ ε |}.
Next Obligation.
  intros. simpl in *.
  rewrite -(dist_le _ _ _ _ H0); eauto with lia.
  rewrite -(dist_le _ _ _ _ H); eauto with lia.
Qed.
Definition uPred_emp_aux : seal (@uPred_emp_def). Proof. by eexists. Qed.
Definition uPred_emp := uPred_emp_aux.(unseal).
Arguments uPred_emp {M}.
Definition uPred_emp_eq :
  @uPred_emp = @uPred_emp_def := uPred_emp_aux.(seal_eq).

Program Definition uPred_pure_def {M} (φ : Prop) : uPred M :=
  {| uPred_holds n x := φ |}.
Solve Obligations with done.
Definition uPred_pure_aux : seal (@uPred_pure_def). Proof. by eexists. Qed.
Definition uPred_pure := uPred_pure_aux.(unseal).
Arguments uPred_pure {M}.
Definition uPred_pure_eq :
  @uPred_pure = @uPred_pure_def := uPred_pure_aux.(seal_eq).

Program Definition uPred_and_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_and_aux : seal (@uPred_and_def). Proof. by eexists. Qed.
Definition uPred_and := uPred_and_aux.(unseal).
Arguments uPred_and {M}.
Definition uPred_and_eq: @uPred_and = @uPred_and_def := uPred_and_aux.(seal_eq).

Program Definition uPred_or_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_or_aux : seal (@uPred_or_def). Proof. by eexists. Qed.
Definition uPred_or := uPred_or_aux.(unseal).
Arguments uPred_or {M}.
Definition uPred_or_eq: @uPred_or = @uPred_or_def := uPred_or_aux.(seal_eq).

Program Definition uPred_impl_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n',
       n' ≤ n → P n' x → Q n' x |}.
Next Obligation.
  intros M P Q n1 n1' x1 x1' HPQ Hx1 Hn1 n2 x3 Hx3; simpl in *.
  rewrite -(dist_le _ _ _ _ Hx1); last lia.
  eapply HPQ; first by auto. by rewrite (dist_le _ _ _ _ Hx1); last lia.
Qed.
Definition uPred_impl_aux : seal (@uPred_impl_def). Proof. by eexists. Qed.
Definition uPred_impl := uPred_impl_aux.(unseal).
Arguments uPred_impl {M}.
Definition uPred_impl_eq :
  @uPred_impl = @uPred_impl_def := uPred_impl_aux.(seal_eq).

Program Definition uPred_forall_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∀ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_forall_aux : seal (@uPred_forall_def). Proof. by eexists. Qed.
Definition uPred_forall := uPred_forall_aux.(unseal).
Arguments uPred_forall {M A}.
Definition uPred_forall_eq :
  @uPred_forall = @uPred_forall_def := uPred_forall_aux.(seal_eq).

Program Definition uPred_exist_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∃ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_exist_aux : seal (@uPred_exist_def). Proof. by eexists. Qed.
Definition uPred_exist := uPred_exist_aux.(unseal).
Arguments uPred_exist {M A}.
Definition uPred_exist_eq: @uPred_exist = @uPred_exist_def := uPred_exist_aux.(seal_eq).

Program Definition uPred_internal_eq_def {M} {A : ofeT} (a1 a2 : A) : uPred M :=
  {| uPred_holds n x := a1 ≡{n}≡ a2 |}.
Solve Obligations with naive_solver eauto 2 using dist_le.
Definition uPred_internal_eq_aux : seal (@uPred_internal_eq_def). Proof. by eexists. Qed.
Definition uPred_internal_eq := uPred_internal_eq_aux.(unseal).
Arguments uPred_internal_eq {M A}.
Definition uPred_internal_eq_eq:
  @uPred_internal_eq = @uPred_internal_eq_def := uPred_internal_eq_aux.(seal_eq).

Program Definition uPred_sep_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∃ x1 x2, x ≡{n}≡ x1 ⋅ x2 ∧ P n x1 ∧ Q n x2 |}.
Next Obligation.
  intros M P Q n1 n2 x y (x1&x2&Hx&?&?) Hx' Hn.
  exists x1, x2. rewrite -Hx'. split_and?; eauto using uPred_mono, dist_le.
Qed.
Definition uPred_sep_aux : seal (@uPred_sep_def). Proof. by eexists. Qed.
Definition uPred_sep := uPred_sep_aux.(unseal).
Arguments uPred_sep {M}.
Definition uPred_sep_eq: @uPred_sep = @uPred_sep_def := uPred_sep_aux.(seal_eq).

Program Definition uPred_wand_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       n' ≤ n → ✓{n'} (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Next Obligation.
  intros M P Q n1 n1' x1 x1' HPQ Hx1 Hn n3 x3 ???; simpl in *.
  eapply uPred_mono with n3 (x1 ⋅ x3); [..|done].
  - apply HPQ; [lia| |done]. by rewrite (dist_le _ _ _ _ Hx1).
  - by rewrite (dist_le _ _ _ _ Hx1).
Qed.
Definition uPred_wand_aux : seal (@uPred_wand_def). Proof. by eexists. Qed.
Definition uPred_wand := uPred_wand_aux.(unseal).
Arguments uPred_wand {M}.
Definition uPred_wand_eq :
  @uPred_wand = @uPred_wand_def := uPred_wand_aux.(seal_eq).

(* Equivalently, this could be `∀ y, P n y`.  That's closer to the intuition
   of "embedding the step-indexed logic in Iris", but the two are equivalent
   because Iris is afine.  The following is easier to work with. *)
(* Program Definition uPred_plainly_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n ε |}.
Solve Obligations with naive_solver eauto using uPred_mono, ucmra_unit_validN.
Definition uPred_plainly_aux : seal (@uPred_plainly_def). Proof. by eexists. Qed.
Definition uPred_plainly := uPred_plainly_aux.(unseal).
Arguments uPred_plainly {M}.
Definition uPred_plainly_eq :
  @uPred_plainly = @uPred_plainly_def := uPred_plainly_aux.(seal_eq). *)

(* Core is strange in a linear setting,
    so we have substituted core x ↦ ε in the following definition.
    This is essentially plainly. *)
Program Definition uPred_persistently_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n ε |}.
Solve Obligations with naive_solver eauto using uPred_mono, ucmra_unit_validN.
Definition uPred_persistently_aux : seal (@uPred_persistently_def). Proof. by eexists. Qed.
Definition uPred_persistently := uPred_persistently_aux.(unseal).
Arguments uPred_persistently {M}.
Definition uPred_persistently_eq :
  @uPred_persistently = @uPred_persistently_def := uPred_persistently_aux.(seal_eq).

Program Definition uPred_later_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := match n return _ with 0 => True | S n' => P n' x end |}.
Next Obligation.
  intros M P [|n1] [|n2] x1 x2 HP Hx Hn; eauto with lia.
  rewrite -(dist_le _ _ _ _ Hx); last lia.
  eapply uPred_mono with n1 _; eauto.
Qed.
Definition uPred_later_aux : seal (@uPred_later_def). Proof. by eexists. Qed.
Definition uPred_later := uPred_later_aux.(unseal).
Arguments uPred_later {M}.
Definition uPred_later_eq :
  @uPred_later = @uPred_later_def := uPred_later_aux.(seal_eq).

Program Definition uPred_ownM_def {M : ucmraT} (a : auth M) : uPred M :=
  {| uPred_holds n x := a ≡{n}≡ x |}.
Next Obligation.
  intros M a n1 n2 x1 x Hx1 Hx Hn; simpl in *.
  by rewrite -Hx (dist_le _ _ _ _ Hx1); last lia.
Qed.
Definition uPred_ownM_aux : seal (@uPred_ownM_def). Proof. by eexists. Qed.
Definition uPred_ownM := uPred_ownM_aux.(unseal).
Arguments uPred_ownM {M}.
Definition uPred_ownM_eq :
  @uPred_ownM = @uPred_ownM_def := uPred_ownM_aux.(seal_eq).

Program Definition uPred_cmra_valid_def {M} {A : cmraT} (a : A) : uPred M :=
  {| uPred_holds n x := ✓{n} a |}.
Solve Obligations with naive_solver eauto 2 using cmra_validN_le.
Definition uPred_cmra_valid_aux : seal (@uPred_cmra_valid_def). Proof. by eexists. Qed.
Definition uPred_cmra_valid := uPred_cmra_valid_aux.(unseal).
Arguments uPred_cmra_valid {M A}.
Definition uPred_cmra_valid_eq :
  @uPred_cmra_valid = @uPred_cmra_valid_def := uPred_cmra_valid_aux.(seal_eq).

Program Definition uPred_bupd_def {M} (Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ k yf,
      k ≤ n → auth_global_valid k (x ⋅ yf) →
              ∃ x', auth_global_valid k (x' ⋅ yf) ∧ Q k x' |}.
Next Obligation.
  intros M Q n1 n2 x1 x2 HQ Hx Hn k yf Hk Hvalid. apply HQ; first lia.
  by rewrite (dist_le _ _ _ _ Hx); last lia.
Qed.
Definition uPred_bupd_aux : seal (@uPred_bupd_def). Proof. by eexists. Qed.
Definition uPred_bupd := uPred_bupd_aux.(unseal).
Arguments uPred_bupd {M}.
Definition uPred_bupd_eq :
  @uPred_bupd = @uPred_bupd_def := uPred_bupd_aux.(seal_eq).

(** Global uPred-specific Notation *)
Notation "✓ x" := (uPred_cmra_valid x) (at level 20) : bi_scope.

(** Primitive logical rules.
    These are not directly usable later because they do not refer to the BI
    connectives. *)
Module uPred_primitive.
Definition unseal_eqs :=
  (uPred_emp_eq, uPred_pure_eq, uPred_and_eq, uPred_or_eq, uPred_impl_eq, uPred_forall_eq,
  uPred_exist_eq, uPred_internal_eq_eq, uPred_sep_eq, uPred_wand_eq,
  uPred_persistently_eq, uPred_later_eq, uPred_ownM_eq,
  uPred_cmra_valid_eq, @uPred_bupd_eq).
Ltac unseal :=
  rewrite !unseal_eqs /=.

Section primitive.
Context {M : ucmraT}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.
Arguments uPred_holds {_} !_ _ _ /.
Local Hint Immediate uPred_in_entails : core.

Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.
Notation "P ⊣⊢ Q" := (@uPred_equiv M P%I Q%I) : stdpp_scope.
Notation "(⊣⊢)" := (@uPred_equiv M) (only parsing) : stdpp_scope.

Notation "'emp'" := uPred_emp : bi_scope.
Notation "'True'" := (uPred_pure True) : bi_scope.
Notation "'False'" := (uPred_pure False) : bi_scope.
Notation "'⌜' φ '⌝'" := (uPred_pure φ%type%stdpp) : bi_scope.
Infix "∧" := uPred_and : bi_scope.
Infix "∨" := uPred_or : bi_scope.
Infix "→" := uPred_impl : bi_scope.
Notation "∀ x .. y , P" :=
  (uPred_forall (λ x, .. (uPred_forall (λ y, P)) ..)) : bi_scope.
Notation "∃ x .. y , P" :=
  (uPred_exist (λ x, .. (uPred_exist (λ y, P)) ..)) : bi_scope.
Infix "∗" := uPred_sep : bi_scope.
Infix "-∗" := uPred_wand : bi_scope.
Notation "<pers> P" := (uPred_persistently P) : bi_scope.
Notation "x ≡ y" := (uPred_internal_eq x y) : bi_scope.
Notation "▷ P" := (uPred_later P) : bi_scope.
Notation "|==> P" := (uPred_bupd P) : bi_scope.

(** Entailment *)
Lemma entails_po : PreOrder (⊢).
Proof.
  split.
  - by intros P; split=> x i.
  - by intros P Q Q' HP HQ; split=> x i ??; apply HQ, HP.
Qed.
Lemma entails_anti_sym : AntiSymm (⊣⊢) (⊢).
Proof. intros P Q HPQ HQP; split=> x n; by split; [apply HPQ|apply HQP]. Qed.
Lemma equiv_spec P Q : (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
Proof.
  split.
  - intros HPQ; split; split=> x i; apply HPQ.
  - intros [??]. exact: entails_anti_sym.
Qed.
Lemma entails_lim (cP cQ : chain (uPredO M)) :
  (∀ n, cP n ⊢ cQ n) → compl cP ⊢ compl cQ.
Proof.
  intros Hlim; split=> n m ? HP.
  eapply uPred_holds_ne, Hlim, HP; rewrite ?conv_compl; eauto.
Qed.

(** Non-expansiveness and setoid morphisms *)
Lemma pure_ne n : Proper (iff ==> dist n) (@uPred_pure M).
Proof. intros φ1 φ2 Hφ. by unseal; split=> -[|m] ?; try apply Hφ. Qed.

Lemma and_ne : NonExpansive2 (@uPred_and M).
Proof.
  intros n P P' HP Q Q' HQ; unseal; split=> x n' ??.
  split; (intros [??]; split; [by apply HP|by apply HQ]).
Qed.

Lemma or_ne : NonExpansive2 (@uPred_or M).
Proof.
  intros n P P' HP Q Q' HQ; split=> x n' ??.
  unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
Qed.

Lemma impl_ne :
  NonExpansive2 (@uPred_impl M).
Proof.
  intros n P P' HP Q Q' HQ; split=> n' x ??.
  unseal; split; intros HPQ n'' ??; apply HQ, HPQ, HP; eauto using cmra_validN_le.
Qed.

Lemma sep_ne : NonExpansive2 (@uPred_sep M).
Proof.
  intros n P P' HP Q Q' HQ; split=> n' x ??.
  unseal; split; intros (x1&x2&?&?&?); ofe_subst x;
    exists x1, x2; split_and!; try (apply HP || apply HQ);
    eauto using cmra_validN_op_l, cmra_validN_op_r.
Qed.

Lemma wand_ne :
  NonExpansive2 (@uPred_wand M).
Proof.
  intros n P P' HP Q Q' HQ; split=> n' x ??; unseal; split; intros HPQ x' n'' ???;
    apply HQ, HPQ, HP; eauto using cmra_validN_op_r.
Qed.

Lemma internal_eq_ne (A : ofeT) :
  NonExpansive2 (@uPred_internal_eq M A).
Proof.
  intros n x x' Hx y y' Hy; split=> n' z; unseal; split; intros; simpl in *.
  - by rewrite -(dist_le _ _ _ _ Hx) -?(dist_le _ _ _ _ Hy); auto.
  - by rewrite (dist_le _ _ _ _ Hx) ?(dist_le _ _ _ _ Hy); auto.
Qed.

Lemma forall_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_forall M A).
Proof.
  by intros Ψ1 Ψ2 HΨ; unseal; split=> n' x; split; intros HP a; apply HΨ.
Qed.

Lemma exist_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_exist M A).
Proof.
  intros Ψ1 Ψ2 HΨ.
  unseal; split=> n' x ??; split; intros [a ?]; exists a; by apply HΨ.
Qed.

Lemma later_contractive : Contractive (@uPred_later M).
Proof.
  unseal; intros [|n] P Q HPQ; split=> -[|n'] x ?? //=; try lia.
  apply HPQ; eauto using cmra_validN_S.
Qed.

Lemma persistently_ne : NonExpansive (@uPred_persistently M).
Proof.
  intros n P1 P2 Hp.
  unseal; split=> n' x; split; apply Hp; eauto using ucmra_unit_validN.
Qed.

Lemma ownM_ne : NonExpansive (@uPred_ownM M).
Proof.
  intros n a b Ha.
  unseal; split=> n' x ? /=. by rewrite (dist_le _ _ _ _ Ha); last lia.
Qed.

Lemma cmra_valid_ne {A : cmraT} :
  NonExpansive (@uPred_cmra_valid M A).
Proof.
  intros n a b Ha; unseal; split=> n' x ? /=.
  by rewrite (dist_le _ _ _ _ Ha); last lia.
Qed.

Lemma bupd_ne : NonExpansive (@uPred_bupd M).
Proof.
  intros n P Q HPQ.
  unseal; split=> n' x; split; intros HP k yf ??;
    destruct (HP k yf) as (x'&?&?); auto;
    exists x'; split; auto; apply HPQ; eauto using cmra_validN_op_l, auth_global_valid_valid.
Qed.

(** Introduction and elimination rules *)
Lemma pure_intro φ P : φ → P ⊢ ⌜φ⌝.
Proof. by intros ?; unseal; split. Qed.
Lemma pure_elim' φ P : (φ → True ⊢ P) → ⌜φ⌝ ⊢ P.
Proof. unseal; intros HP; split=> n x ??. by apply HP. Qed.
Lemma pure_forall_2 {A} (φ : A → Prop) : (∀ x : A, ⌜φ x⌝) ⊢ ⌜∀ x : A, φ x⌝.
Proof. by unseal. Qed.

Lemma and_elim_l P Q : P ∧ Q ⊢ P.
Proof. by unseal; split=> n x ? [??]. Qed.
Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
Proof. by unseal; split=> n x ? [??]. Qed.
Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
Proof. intros HQ HR; unseal; split=> n x ??; by split; [apply HQ|apply HR]. Qed.

Lemma or_intro_l P Q : P ⊢ P ∨ Q.
Proof. unseal; split=> n x ??; left; auto. Qed.
Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
Proof. unseal; split=> n x ??; right; auto. Qed.
Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
Proof.
  intros HP HQ; unseal; split=> n x ? [?|?].
  - by apply HP.
  - by apply HQ.
Qed.

Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
Proof.
  unseal; intros HQ; split=> n x ?? n' x' ?.
  apply HQ; naive_solver eauto using uPred_mono, cmra_included_includedN, cmra_validN_le.
Qed.
Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
Proof.
  unseal; intros HP ; split=> n x ? [??].
  apply HP with n; auto.
Qed.

Lemma forall_intro {A} P (Ψ : A → uPred M): (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
Proof. unseal; intros HPΨ; split=> n x ?? a; by apply HPΨ. Qed.
Lemma forall_elim {A} {Ψ : A → uPred M} a : (∀ a, Ψ a) ⊢ Ψ a.
Proof. unseal; split=> n x ? HP; apply HP. Qed.

Lemma exist_intro {A} {Ψ : A → uPred M} a : Ψ a ⊢ ∃ a, Ψ a.
Proof. unseal; split=> n x ??; by exists a. Qed.
Lemma exist_elim {A} (Φ : A → uPred M) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
Proof. unseal; intros HΦΨ; split=> n x ? [a ?]; by apply HΦΨ with a. Qed.

(** BI connectives *)
Lemma sep_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
Proof.
  intros HQ HQ'; unseal.
  split; intros n' x ? (x1&x2&?&?&?); exists x1,x2; ofe_subst x;
    eauto 7 using cmra_validN_op_l, cmra_validN_op_r, uPred_in_entails.
Qed.
Lemma emp_sep_1 P : P ⊢ emp ∗ P.
Proof.
  unseal; split; intros n x ??. exists ε, x. by rewrite left_id.
Qed.
Lemma emp_sep_2 P : emp ∗ P ⊢ P.
Proof.
  unseal; split; intros n x ? (x1&x2&?&?&?); ofe_subst.
  by rewrite left_id.
Qed.
Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
Proof.
  unseal; split; intros n x ? (x1&x2&?&?&?); exists x2, x1; by rewrite (comm op).
Qed.
Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
Proof.
  unseal; split; intros n x ? (x1&x2&Hx&(y1&y2&Hy&?&?)&?).
  exists y1, (y2 ⋅ x2); split_and?; auto.
  + by rewrite (assoc op) -Hy -Hx.
  + by exists y2, x2.
Qed.
Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
Proof.
  unseal=> HPQR; split=> n x ?? n' x' ???; apply HPQR; auto.
  exists x, x'; split_and?; auto.
  eapply uPred_mono with n x; eauto using cmra_validN_op_l.
Qed.
Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
Proof.
  unseal =>HPQR. split; intros n x ? (?&?&?&?&?). ofe_subst.
  eapply HPQR; eauto using cmra_validN_op_l.
Qed.

(** Persistently *)
Lemma persistently_mono P Q : (P ⊢ Q) → <pers> P ⊢ <pers> Q.
Proof. intros HP; unseal; split=> n x ? /=. apply HP, ucmra_unit_validN. Qed.

Lemma persistently_idemp_2 P : <pers> P ⊢ <pers> <pers> P.
Proof. unseal; split=> n x ?? //. Qed.

Lemma persistently_emp_2 : emp ⊢ <pers> emp.
Proof. unseal; by split => n x ? /=. Qed.

Lemma persistently_forall_2 {A} (Ψ : A → uPred M) : (∀ a, <pers> Ψ a) ⊢ (<pers> ∀ a, Ψ a).
Proof. by unseal. Qed.
Lemma persistently_exist_1 {A} (Ψ : A → uPred M) : (<pers> ∃ a, Ψ a) ⊢ (∃ a, <pers> Ψ a).
Proof. by unseal. Qed.

Lemma persistently_absorbing P Q : <pers> P ∗ Q ⊢ <pers> P.
Proof. unseal; split=> n x ? /=. naive_solver. Qed.

Lemma persistently_and_sep_elim P Q : <pers> P ∧ Q ⊢ P ∗ Q.
Proof.
  unseal; split=> n x ? [??]; exists ε, x; simpl in *. by rewrite left_id.
Qed.

Lemma prop_ext_2 P Q : <pers> ((P -∗ Q) ∧ (Q -∗ P)) ⊢ P ≡ Q.
Proof.
  unseal; split=> n x ? /=. setoid_rewrite (left_id ε op). split; naive_solver.
Qed.

Lemma persistently_impl_persistently P Q : (<pers> P → <pers> Q) ⊢ <pers> (<pers> P → Q).
Proof.
  unseal; split=> /= n x ? HPQ n' x' ?. naive_solver.
Qed.

(** Later *)
Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
Proof.
  unseal=> HP; split=>-[|n] x ??; [done|apply HP; eauto using cmra_validN_S].
Qed.
Lemma later_intro P : P ⊢ ▷ P.
Proof.
  unseal; split=> -[|n] /= x ? HP; first done.
  apply uPred_mono with (S n) x; eauto using cmra_validN_S.
Qed.
Lemma later_forall_2 {A} (Φ : A → uPred M) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
Proof. unseal; by split=> -[|n] x. Qed.
Lemma later_exist_false {A} (Φ : A → uPred M) :
  (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
Proof. unseal; split=> -[|[|n]] x /=; eauto. Qed.
Lemma later_sep_1 P Q : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q.
Proof.
  unseal; split=> n x ?.
  destruct n as [|n]; simpl.
  { by exists x, (core x); rewrite cmra_core_r. }
  intros (x1&x2&Hx&?&?); destruct (cmra_extend n x x1 x2)
    as (y1&y2&Hx'&Hy1&Hy2); eauto using cmra_validN_S; simpl in *.
  exists y1, y2; split; [by rewrite Hx'|by rewrite Hy1 Hy2].
Qed.
Lemma later_sep_2 P Q : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q).
Proof.
  unseal; split=> n x ?.
  destruct n as [|n]; simpl; [done|intros (x1&x2&Hx&?&?)].
  exists x1, x2; eauto using dist_S.
Qed.

Lemma later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
Proof.
  unseal; split=> -[|n] x ? /= HP; [by left|right].
  intros [|n'] ??; eauto using uPred_mono, cmra_included_includedN.
Qed.

Lemma later_persistently_1 P : ▷ <pers> P ⊢ <pers> ▷ P.
Proof. by unseal. Qed.
Lemma later_persistently_2 P : <pers> ▷ P ⊢ ▷ <pers> P.
Proof. by unseal. Qed.

(** Internal equality *)
Lemma internal_eq_refl {A : ofeT} P (a : A) : P ⊢ (a ≡ a).
Proof. unseal; by split=> n x ??; simpl. Qed.
Lemma internal_eq_rewrite {A : ofeT} a b (Ψ : A → uPred M) :
  NonExpansive Ψ → a ≡ b ⊢ Ψ a → Ψ b.
Proof.
  intros HΨ.
  unseal; split=> n x ?? /= n' ??. apply HΨ with n a; eauto using cmra_validN_le.
Qed.

Lemma fun_ext {A} {B : A → ofeT} (g1 g2 : discrete_fun B) :
  (∀ i, g1 i ≡ g2 i) ⊢ g1 ≡ g2.
Proof. by unseal. Qed.
Lemma sig_eq {A : ofeT} (P : A → Prop) (x y : sigO P) :
  proj1_sig x ≡ proj1_sig y ⊢ x ≡ y.
Proof. by unseal. Qed.

Lemma later_eq_1 {A : ofeT} (x y : A) : Next x ≡ Next y ⊢ ▷ (x ≡ y).
Proof. by unseal. Qed.
Lemma later_eq_2 {A : ofeT} (x y : A) : ▷ (x ≡ y) ⊢ Next x ≡ Next y.
Proof. by unseal. Qed.

Lemma discrete_eq_1 {A : ofeT} (a b : A) : Discrete a → a ≡ b ⊢ ⌜a ≡ b⌝.
Proof.
  unseal=> ?. split=> n x ?. by apply (discrete_iff n).
Qed.

(** This is really just a special case of an entailment
between two [siProp], but we do not have the infrastructure
to express the more general case. This temporary proof rule will
be replaced by the proper one eventually. *)
Lemma internal_eq_entails {A B : ofeT} (a1 a2 : A) (b1 b2 : B) :
  (∀ n, a1 ≡{n}≡ a2 → b1 ≡{n}≡ b2) → a1 ≡ a2 ⊢ b1 ≡ b2.
Proof. unseal=>Hsi. split=>n x ?. apply Hsi. Qed.

(** Basic update modality *)
Lemma bupd_intro P : P ⊢ |==> P.
Proof.
  unseal. split=> n x ? HP k yf ?; exists x; split; first done.
  apply uPred_mono with n x; eauto using cmra_validN_op_l.
Qed.
Lemma bupd_mono P Q : (P ⊢ Q) → (|==> P) ⊢ |==> Q.
Proof.
  unseal. intros HPQ; split=> n x ? HP k yf ??.
  destruct (HP k yf) as (x'&?&?); eauto.
  exists x'. split; first done.
  eauto using uPred_in_entails, cmra_validN_op_l, cmra_validN_le, auth_global_valid_valid.
Qed.
Lemma bupd_trans P : (|==> |==> P) ⊢ |==> P.
Proof. unseal; split; naive_solver. Qed.
Lemma bupd_frame_r P R : (|==> P) ∗ R ⊢ |==> P ∗ R.
Proof.
  unseal; split; intros n x ? (x1&x2&Hx&HP&?) k yf ??.
  destruct (HP k (x2 ⋅ yf)) as (x'&?&?); eauto.
  { by rewrite assoc -(dist_le _ _ _ _ Hx); last lia. }
  exists (x' ⋅ x2); split; first by rewrite -assoc.
  exists x', x2. eauto using uPred_mono, cmra_validN_op_l, cmra_validN_op_r.
Qed.
(* Lemma bupd_plainly P : (|==> ■ P) ⊢ P.
Proof.
  unseal; split => n x Hnx /= Hng.
  destruct (Hng n ε) as [? [_ Hng']]; try rewrite right_id; auto.
  eapply uPred_mono; eauto using ucmra_unit_leastN.
Qed. *)

(** Own *)
Lemma ownM_op (a1 a2 : auth M) :
  uPred_ownM (a1 ⋅ a2) ⊣⊢ uPred_ownM a1 ∗ uPred_ownM a2.
Proof.
  unseal; split=> n x ?; split.
  - intros H. exists a1, a2. simpl in H.
    split. { by rewrite H. }
    split; by simpl.
  - simpl. by intros (x1&x2 & -> & -> & ->).
Qed.

Lemma ownM_unit : emp ⊢ uPred_ownM ε.
Proof. unseal; split=> /= n x ??. done. Qed.

Lemma later_ownM a : ▷ uPred_ownM a ⊢ ∃ b, uPred_ownM b ∧ ▷ (a ≡ b).
Proof.
  unseal; split=> -[|n] x /= ? Hax; eauto using ucmra_unit_leastN.
Qed.

Definition auth_global_updateN {A : ucmraT} (n : nat) (x y : auth A) := ∀ z,
  auth_global_valid n (x ⋅ z) → auth_global_valid n (y ⋅ z).

Definition auth_global_update {A : ucmraT} (x y : auth A) := ∀ n z,
  auth_global_valid n (x ⋅ z) → auth_global_valid n (y ⋅ z).

Instance : Params (@auth_global_update) 1 := {}.

Instance auth_global_update_proper {A : ucmraT}
  : Proper ((≡) ==> (≡) ==> iff) (auth_global_update (A:=A)).
Proof.
  intros x1 x2 Hx y1 y2 Hy. unfold auth_global_update.
  setoid_rewrite Hx.
  setoid_rewrite Hy.
  done.
Qed.

Lemma bupd_ownM_update (x y : auth M) :
  auth_global_update x y →
  uPred_ownM x ⊢ |==> uPred_ownM y.
Proof.
  unseal.
  unfold auth_global_update.
  intros H. constructor.
  intros n z vz Ho.
  unfold uPred_bupd_def. simpl.
  intros k yf Kleq Hgv.
  eexists.
  split.
  - apply H. unfold uPred_ownM_def in Ho. simpl in Ho.
    rewrite (dist_le _ _ _ _ Ho); done.
  - reflexivity.
Qed.

(** Valid *)
Lemma ownM_valid (a : auth M) : uPred_ownM a ⊢ ✓ a.
Proof.
  unseal. split=> n x Hv /= -> //.
Qed.
Lemma cmra_valid_intro {A : cmraT} P (a : A) : ✓ a → P ⊢ (✓ a).
Proof. unseal=> ?; split=> n x ? _ /=; by apply cmra_valid_validN. Qed.
Lemma cmra_valid_elim {A : cmraT} (a : A) : ¬ ✓{0} a → ✓ a ⊢ False.
Proof. unseal=> Ha; split=> n x ??; apply Ha, cmra_validN_le with n; auto. Qed.
Lemma plainly_cmra_valid_1 {A : cmraT} (a : A) : ✓ a ⊢ <pers> ✓ a.
Proof. by unseal. Qed.
Lemma cmra_valid_weaken {A : cmraT} (a b : A) : ✓ (a ⋅ b) ⊢ ✓ a.
Proof. unseal; split=> n x _; apply cmra_validN_op_l. Qed.

Lemma discrete_valid {A : cmraT} `{!CmraDiscrete A} (a : A) : ✓ a ⊣⊢ ⌜✓ a⌝.
Proof. unseal; split=> n x _. by rewrite /= -cmra_discrete_valid_iff. Qed.

(** This is really just a special case of an entailment
between two [siProp], but we do not have the infrastructure
to express the more general case. This temporary proof rule will
be replaced by the proper one eventually. *)
Lemma valid_entails {A B : cmraT} (a : A) (b : B) :
  (∀ n, ✓{n} a → ✓{n} b) → ✓ a ⊢ ✓ b.
Proof. unseal=> Hval. split=>n x ?. apply Hval. Qed.

(** Consistency/soundness statement *)
(** The lemmas [pure_soundness] and [internal_eq_soundness] should become an
instance of [siProp] soundness in the future. *)
Lemma pure_soundness φ : (emp ⊢ ⌜ φ ⌝) → φ.
Proof. unseal=> -[H]. by apply (H 0 ε); eauto using ucmra_unit_validN. Qed.

Lemma internal_eq_soundness {A : ofeT} (x y : A) : (emp ⊢ x ≡ y) → x ≡ y.
Proof.
  unseal=> -[H]. apply equiv_dist=> n.
  by apply (H n ε); eauto using ucmra_unit_validN.
Qed.

Lemma later_soundness P : (emp ⊢ ▷ P) → (emp ⊢ P).
Proof.
  unseal=> -[HP]; split=> n x Hx ?. simpl in *.
  apply uPred_mono with n ε; eauto using ucmra_unit_leastN.
  by apply (HP (S n)); eauto using ucmra_unit_validN.
Qed.

Lemma ownM_simple_soundness (x : auth M) (φ : Prop) :
  auth_global_valid 0 x →
  (uPred_ownM x ⊢ |==> ⌜ φ ⌝) →
  φ.
Proof.
  unseal=> Hgv [H]. simpl in *.
  edestruct (H 0 x); try done.
  - apply auth_global_valid_valid. done.
  - assert (auth_global_valid 0 (x ⋅ ε)); last done.
    by rewrite right_id.
  - destruct H0; done.
Qed.

Lemma ownM_soundness (x : auth M) (φ : auth M → Prop) :
  (∀ x : M, Cancelable x) →
  auth_global_valid 0 x →
  (uPred_ownM x ⊢ |==> ∃ y, uPred_ownM y ∧ ⌜ φ y ⌝) →
  ∃ y, auth_global_updateN 0 x y ∧ φ y.
Proof.
  intros Hcancel.
  unseal=> Hgv [H]. simpl in *.
  unfold auth_global_update.
  edestruct (H 0 x).
  - apply auth_global_valid_valid. done.
  - reflexivity.
  - reflexivity.
  - assert (auth_global_valid 0 (x ⋅ ε)); last done.
    by rewrite right_id.
  - destruct H0 as [Hgv1 [a [H1 H2]]].
    eexists. split; last done.
    intros z Hgv2.
    assert (auth_global_valid 0 x) by done.
    epose proof (auth_global_valid_epsilon _ _ _ Hcancel Hgv2 H0).
    rewrite H3 right_id.
    rewrite H1.
    assert (x0 ≡{0}≡ x0 ⋅ ε) as -> by (by rewrite right_id).
    done.
Qed.
End primitive.
End uPred_primitive.
