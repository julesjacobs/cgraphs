From iris.algebra Require Export cmra.
From iris.bi Require Import notation.

Record uPred (M : ucmra) : Type := UPred {
  uPred_holds :> M → Prop;
  uPred_proper : Proper ((≡) ==> iff) uPred_holds
}.
Bind Scope bi_scope with uPred.
Arguments uPred_holds {_} _%I _ : simpl never.
Add Printing Constructor uPred.
Global Instance: Params (@uPred_holds) 2 := {}.
Global Existing Instance uPred_proper.

Section ofe.
  Context {M : ucmra}.

  Inductive uPred_equiv' (P Q : uPred M) : Prop :=
    { uPred_in_equiv : ∀ x, ✓ x → P x ↔ Q x }.
  Instance uPred_equiv : Equiv (uPred M) := uPred_equiv'.

  Instance uPred_equivalence : Equivalence uPred_equiv.
  Proof.
    split.
    + by intros P; split=> x ?.
    + by intros P Q HPQ; split=> x ?; symmetry; apply HPQ.
    + intros P Q Q' HP HQ; split=> x ?.
      by trans (Q x);[apply HP|apply HQ].
  Qed.

  Canonical Structure uPredO : ofe := discreteO (uPred M).
End ofe.
Arguments uPredO : clear implicits.

(** logical entailement *)
Inductive uPred_entails {M} (P Q : uPred M) : Prop :=
  { uPred_in_entails : ∀ x, ✓ x → P x → Q x }.

(** logical connectives *)
Program Definition uPred_emp_def {M} : uPred M :=
  {| uPred_holds x := x ≡ ε |}.
Solve Obligations with solve_proper.

Definition uPred_emp_aux : seal (@uPred_emp_def). Proof. by eexists. Qed.
Definition uPred_emp := uPred_emp_aux.(unseal).
Arguments uPred_emp {M}.
Definition uPred_emp_eq :
  @uPred_emp = @uPred_emp_def := uPred_emp_aux.(seal_eq).

Definition uPred_pure_def {M} (φ : Prop) : uPred M :=
  {| uPred_holds x := φ |}.
Definition uPred_pure_aux : seal (@uPred_pure_def). Proof. by eexists. Qed.
Definition uPred_pure := uPred_pure_aux.(unseal).
Arguments uPred_pure {M}.
Definition uPred_pure_eq :
  @uPred_pure = @uPred_pure_def := uPred_pure_aux.(seal_eq).

Program Definition uPred_and_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds x := P x ∧ Q x |}.
Solve Obligations with solve_proper.
Definition uPred_and_aux : seal (@uPred_and_def). Proof. by eexists. Qed.
Definition uPred_and := uPred_and_aux.(unseal).
Arguments uPred_and {M}.
Definition uPred_and_eq: @uPred_and = @uPred_and_def := uPred_and_aux.(seal_eq).

Program Definition uPred_or_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds x := P x ∨ Q x |}.
Solve Obligations with solve_proper.
Definition uPred_or_aux : seal (@uPred_or_def). Proof. by eexists. Qed.
Definition uPred_or := uPred_or_aux.(unseal).
Arguments uPred_or {M}.
Definition uPred_or_eq: @uPred_or = @uPred_or_def := uPred_or_aux.(seal_eq).

Program Definition uPred_impl_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds x := P x → Q x |}.
Next Obligation.
  intros M P Q x1 x2 Hx. by rewrite Hx.
Qed.
Definition uPred_impl_aux : seal (@uPred_impl_def). Proof. by eexists. Qed.
Definition uPred_impl := uPred_impl_aux.(unseal).
Arguments uPred_impl {M}.
Definition uPred_impl_eq :
  @uPred_impl = @uPred_impl_def := uPred_impl_aux.(seal_eq).

Program Definition uPred_forall_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds x := ∀ a, Ψ a x |}.
Next Obligation.
  intros M P Q x1 x2 Hx. by setoid_rewrite Hx.
Qed.
Definition uPred_forall_aux : seal (@uPred_forall_def). Proof. by eexists. Qed.
Definition uPred_forall := uPred_forall_aux.(unseal).
Arguments uPred_forall {M A}.
Definition uPred_forall_eq :
  @uPred_forall = @uPred_forall_def := uPred_forall_aux.(seal_eq).

Program Definition uPred_exist_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds x := ∃ a, Ψ a x |}.
Next Obligation.
  intros M P Q x1 x2 Hx. by setoid_rewrite Hx.
Qed.
Definition uPred_exist_aux : seal (@uPred_exist_def). Proof. by eexists. Qed.
Definition uPred_exist := uPred_exist_aux.(unseal).
Arguments uPred_exist {M A}.
Definition uPred_exist_eq: @uPred_exist = @uPred_exist_def := uPred_exist_aux.(seal_eq).

Program Definition uPred_sep_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds x := ∃ x1 x2, x ≡ x1 ⋅ x2 ∧ P x1 ∧ Q x2 |}.
Solve Obligations with solve_proper.
Definition uPred_sep_aux : seal (@uPred_sep_def). Proof. by eexists. Qed.
Definition uPred_sep := uPred_sep_aux.(unseal).
Arguments uPred_sep {M}.
Definition uPred_sep_eq: @uPred_sep = @uPred_sep_def := uPred_sep_aux.(seal_eq).

Program Definition uPred_wand_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds x := ∀ x',
       ✓ (x ⋅ x') → P x' → Q (x ⋅ x') |}.
Next Obligation.
  intros M P Q x1 x2 Hx. by setoid_rewrite Hx.
Qed.
Definition uPred_wand_aux : seal (@uPred_wand_def). Proof. by eexists. Qed.
Definition uPred_wand := uPred_wand_aux.(unseal).
Arguments uPred_wand {M}.
Definition uPred_wand_eq :
  @uPred_wand = @uPred_wand_def := uPred_wand_aux.(seal_eq).

(* Core is strange in a linear setting,
    so we have substituted core x ↦ ε in the following definition.
    This is essentially plainly. *)
Definition uPred_persistently_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds x := P ε |}.
Definition uPred_persistently_aux : seal (@uPred_persistently_def). Proof. by eexists. Qed.
Definition uPred_persistently := uPred_persistently_aux.(unseal).
Arguments uPred_persistently {M}.
Definition uPred_persistently_eq :
  @uPred_persistently = @uPred_persistently_def := uPred_persistently_aux.(seal_eq).

Program Definition uPred_ownM_def {M : ucmra} (a : M) : uPred M :=
  {| uPred_holds x := a ≡ x |}.
Solve Obligations with solve_proper.
Definition uPred_ownM_aux : seal (@uPred_ownM_def). Proof. by eexists. Qed.
Definition uPred_ownM := uPred_ownM_aux.(unseal).
Arguments uPred_ownM {M}.
Definition uPred_ownM_eq :
  @uPred_ownM = @uPred_ownM_def := uPred_ownM_aux.(seal_eq).

(** Primitive logical rules.
    These are not directly usable later because they do not refer to the BI
    connectives. *)
Module uPred_primitive.
Definition unseal_eqs :=
  (uPred_emp_eq, uPred_pure_eq, uPred_and_eq, uPred_or_eq, uPred_impl_eq, uPred_forall_eq,
  uPred_exist_eq, uPred_sep_eq, uPred_wand_eq,
  uPred_persistently_eq, uPred_ownM_eq).
Ltac unseal :=
  rewrite !unseal_eqs /=.

Section primitive.
Context {M : ucmra}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.
Arguments uPred_holds {_} !_ _ /.
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

(** Entailment *)
Lemma entails_po : PreOrder (⊢).
Proof.
  split.
  - by intros P; split=> x ?.
  - intros P Q Q' HP HQ. split=> x ? ?. by apply HQ, HP.
Qed.
Lemma entails_anti_sym : AntiSymm (⊣⊢) (⊢).
Proof. intros P Q HPQ HQP; split=> x n; by split; [apply HPQ|apply HQP]. Qed.
Lemma equiv_spec P Q : (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
Proof.
  split.
  - intros HPQ; split; split=> x i; apply HPQ; done.
  - intros [??]. exact: entails_anti_sym.
Qed.
Lemma equiv_entails P Q : (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
Proof.
  split.
  - intros HPQ; split; split=> x i; by apply HPQ.
  - intros [??]. exact: entails_anti_sym.
Qed.

(** Non-expansiveness and setoid morphisms *)
Lemma pure_ne n : Proper (iff ==> dist n) (@uPred_pure M).
Proof. intros φ1 φ2 Hφ. unseal. split. intros ??. simpl. done. Qed.

Lemma and_ne : NonExpansive2 (@uPred_and M).
Proof.
  intros n P P' HP Q Q' HQ; unseal; split=> x ?.
  split; (intros [??]; split; [by apply HP|by apply HQ]).
Qed.

Lemma or_ne : NonExpansive2 (@uPred_or M).
Proof.
  intros n P P' HP Q Q' HQ; split=> x ?.
  unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
Qed.

Lemma impl_ne :
  NonExpansive2 (@uPred_impl M).
Proof.
  intros n P P' HP Q Q' HQ; split=> x ?.
  unseal; split; intros HPQ ?; apply HQ, HPQ, HP; eauto using cmra_validN_le.
Qed.

Lemma sep_ne : NonExpansive2 (@uPred_sep M).
Proof.
  intros n P P' HP Q Q' HQ; split=> x ?.
  unseal; split; intros (x1&x2&?&?&?); ofe_subst x;
    exists x1, x2; split_and!; try (apply HP || apply HQ); setoid_subst;
    eauto using cmra_valid_op_l, cmra_valid_op_r.
Qed.

Lemma wand_ne :
  NonExpansive2 (@uPred_wand M).
Proof.
  intros n P P' HP Q Q' HQ; split=> x ?; unseal; split; intros HPQ x' ??;
    apply HQ, HPQ, HP; eauto using cmra_valid_op_r.
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
  unseal; split=> x ?; split; intros [a ?]; exists a; by apply HΨ.
Qed.

Lemma persistently_ne : NonExpansive (@uPred_persistently M).
Proof.
  intros P1 P2 Hp H.
  unseal. split=> x?. simpl. split; apply H; eauto using ucmra_unit_valid.
Qed.

Lemma pure_proper : Proper (iff ==> (≡)) (@uPred_pure M).
Proof. unseal. done. Qed.

Lemma and_proper : Proper ((≡) ==> (≡) ==> (≡)) (@uPred_and M).
Proof.
  unseal. intros ?? [] ?? []. split. naive_solver.
Qed.

Lemma or_proper : Proper ((≡) ==> (≡) ==> (≡)) (@uPred_or M).
Proof.
  unseal. intros ?? [] ?? []. split. naive_solver.
Qed.

Lemma impl_proper : Proper ((≡) ==> (≡) ==> (≡)) (@uPred_impl M).
Proof.
  unseal. intros ?? [] ?? []. split. naive_solver.
Qed.

Lemma sep_proper : Proper ((≡) ==> (≡) ==> (≡)) (@uPred_sep M).
Proof.
  unseal. intros ?? [] ?? []. split. simpl.
  intros ??. split; intros (? & ? & ? & ? & ?).
  - setoid_subst. naive_solver (eauto using cmra_valid_op_l, cmra_valid_op_r).
  - setoid_subst. naive_solver (eauto using cmra_valid_op_l, cmra_valid_op_r).
Qed.

Lemma wand_proper : Proper ((≡) ==> (≡) ==> (≡)) (@uPred_wand M).
Proof.
  unseal. intros ?? [] ?? []. split. naive_solver (eauto using cmra_valid_op_l, cmra_valid_op_r).
Qed.

Lemma forall_proper A :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@uPred_forall M A).
Proof.
  by intros Ψ1 Ψ2 HΨ; unseal; split=> n' x; split; intros HP a; apply HΨ.
Qed.

Lemma exist_proper A :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@uPred_exist M A).
Proof.
  intros Ψ1 Ψ2 HΨ.
  unseal; split=> x ?; split; intros [a ?]; exists a; by apply HΨ.
Qed.

Lemma persistently_proper : Proper ((≡) ==> (≡)) (@uPred_persistently M).
Proof.
  intros ???. unseal. split. intros ??. simpl. destruct H as [H].
  eauto using ucmra_unit_valid.
Qed.

Lemma ownM_proper : Proper ((≡) ==> (≡)) (@uPred_ownM M).
Proof.
  intros ???. unseal. split=> ??. setoid_subst. done.
Qed.


(** Introduction and elimination rules *)
Lemma pure_intro φ P : φ → P ⊢ ⌜φ⌝.
Proof. by intros ?; unseal; split. Qed.
Lemma pure_elim' φ P : (φ → True ⊢ P) → ⌜φ⌝ ⊢ P.
Proof. unseal; intros HP; split=> x ??. by apply HP. Qed.
Lemma pure_forall_2 {A} (φ : A → Prop) : (∀ x : A, ⌜φ x⌝) ⊢ ⌜∀ x : A, φ x⌝.
Proof. by unseal. Qed.

Lemma and_elim_l P Q : P ∧ Q ⊢ P.
Proof. by unseal; split=> x ? [??]. Qed.
Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
Proof. by unseal; split=> x ? [??]. Qed.
Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
Proof. intros HQ HR; unseal; split=> x ??; by split; [apply HQ|apply HR]. Qed.

Lemma or_intro_l P Q : P ⊢ P ∨ Q.
Proof. unseal; split=> x ??; left; auto. Qed.
Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
Proof. unseal; split=> x ??; right; auto. Qed.
Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
Proof.
  intros HP HQ; unseal; split=> x ? [?|?].
  - by apply HP.
  - by apply HQ.
Qed.

Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
Proof.
  unseal; intros HQ; split=> ????.
  apply HQ; naive_solver eauto using uPred_mono, cmra_included_includedN, cmra_validN_le.
Qed.
Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
Proof.
  unseal; intros HP ; split=> x ? [??].
  apply HP; auto.
Qed.

Lemma forall_intro {A} P (Ψ : A → uPred M): (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
Proof. unseal; intros HPΨ; split=> x ?? a; by apply HPΨ. Qed.
Lemma forall_elim {A} {Ψ : A → uPred M} a : (∀ a, Ψ a) ⊢ Ψ a.
Proof. unseal; split=> x ? HP; apply HP. Qed.

Lemma exist_intro {A} {Ψ : A → uPred M} a : Ψ a ⊢ ∃ a, Ψ a.
Proof. unseal; split=> x ??; by exists a. Qed.
Lemma exist_elim {A} (Φ : A → uPred M) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
Proof. unseal; intros HΦΨ; split=> x ? [a ?]; by apply HΦΨ with a. Qed.

(** BI connectives *)
Lemma sep_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
Proof.
  intros HQ HQ'; unseal.
  split; intros x ? (x1&x2&?&?&?); exists x1,x2; setoid_subst; split;
    eauto 7 using cmra_valid_op_l, cmra_valid_op_r, uPred_in_entails.
Qed.
Lemma emp_sep_1 P : P ⊢ emp ∗ P.
Proof.
  unseal; split; intros x ??. exists ε, x. rewrite left_id; simpl; eauto.
Qed.
Lemma emp_sep_2 P : emp ∗ P ⊢ P.
Proof.
  unseal; split; intros x ? (x1&x2&?&?&?); setoid_subst.
  by rewrite left_id.
Qed.
Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
Proof.
  unseal; split; intros x ? (x1&x2&?&?&?); exists x2, x1; by rewrite (comm op).
Qed.
Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
Proof.
  unseal; split; intros x ? (x1&x2&Hx&(y1&y2&Hy&?&?)&?).
  exists y1, (y2 ⋅ x2); split_and?; auto.
  + by rewrite (assoc op) -Hy -Hx.
  + by exists y2, x2.
Qed.
Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
Proof.
  unseal=> HPQR; split=> x ?? x' ??; apply HPQR; auto.
  exists x, x'; split_and?; auto.
Qed.
Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
Proof.
  unseal =>HPQR. split; intros x ? (?&?&?&?&?). setoid_subst.
  eapply HPQR; eauto using cmra_valid_op_l.
Qed.

(** Persistently *)
Lemma persistently_mono P Q : (P ⊢ Q) → <pers> P ⊢ <pers> Q.
Proof. intros HP; unseal; split=> x ? /=. apply HP, ucmra_unit_valid. Qed.

Lemma persistently_idemp_2 P : <pers> P ⊢ <pers> <pers> P.
Proof. unseal; split=> x ?? //. Qed.

Lemma persistently_emp_2 : emp ⊢ <pers> emp.
Proof. unseal; by split => n x ? /=. Qed.

Lemma persistently_and_2 (P Q : uPred M) : (<pers> P ∧ <pers> Q) ⊢ (<pers> (P ∧ Q)).
Proof. by unseal. Qed.


Lemma persistently_forall_2 {A} (Ψ : A → uPred M) : (∀ a, <pers> Ψ a) ⊢ (<pers> ∀ a, Ψ a).
Proof. by unseal. Qed.
Lemma persistently_exist_1 {A} (Ψ : A → uPred M) : (<pers> ∃ a, Ψ a) ⊢ (∃ a, <pers> Ψ a).
Proof. by unseal. Qed.

Lemma persistently_absorbing P Q : <pers> P ∗ Q ⊢ <pers> P.
Proof. unseal; split=> n x ? /=. naive_solver. Qed.

Lemma persistently_and_sep_elim P Q : <pers> P ∧ Q ⊢ P ∗ Q.
Proof.
  unseal; split=> x ? [??]; exists ε, x; simpl in *. by rewrite left_id.
Qed.


Lemma persistently_impl_persistently P Q : (<pers> P → <pers> Q) ⊢ <pers> (<pers> P → Q).
Proof.
  unseal; split=> /= x ? HPQ x'. naive_solver.
Qed.

(** Own *)
Lemma ownM_op (a1 a2 : M) :
  uPred_ownM (a1 ⋅ a2) ⊣⊢ uPred_ownM a1 ∗ uPred_ownM a2.
Proof.
  unseal; split=> x ?; split.
  - intros H. exists a1, a2. simpl in H.
    split. { by rewrite H. }
    split; by simpl.
  - simpl. by intros (x1&x2 & -> & -> & ->).
Qed.

Lemma ownM_unit : uPred_ownM ε ⊣⊢ emp.
Proof. unseal. split; naive_solver. Qed.

Lemma ownM_valid x : uPred_ownM x ⊢ ⌜ ✓ x ⌝.
Proof.
  unseal. split. simpl. intros. setoid_subst. done.
Qed.

(** Consistency/soundness statement *)
(** The lemmas [pure_soundness] and [internal_eq_soundness] should become an
instance of [siProp] soundness in the future. *)
Lemma pure_soundness φ : (emp ⊢ ⌜ φ ⌝) → φ.
Proof. unseal=> -[H]. by apply (H ε); simpl; eauto using ucmra_unit_valid. Qed.

End primitive.
End uPred_primitive.