From iris.algebra Require Export ofe.
From iris.bi Require Import notation.

Record clProp := ClProp {
  clProp_holds :> Prop;
  clProp_stable : ¬¬clProp_holds → clProp_holds
}.
Arguments clProp_holds : simpl never.
Local Arguments clProp_holds !_ /.
Add Printing Constructor clProp.

Declare Scope clProp_scope.
Delimit Scope clProp_scope with CL.
Bind Scope clProp_scope with clProp.

Section cofe.
  Record clProp_equiv' (P Q : clProp) :=  ClProp_equiv { _ : P ↔ Q }.
  Instance clProp_equiv : Equiv clProp := clProp_equiv'.
  Instance clProp_equivalence : Equivalence (≡@{clProp}).
  Proof. split; repeat destruct 1; constructor; tauto. Qed.
  Canonical Structure clPropO : ofeT := discreteO clProp.
  Global Instance clProp_cofe : Cofe clPropO := discrete_cofe _.
End cofe.

(** logical entailement *)
Record clProp_entails (P Q : clProp) : Prop := { clProp_in_entails : P → Q }.

(** logical connectives *)
Program Definition clProp_pure_def (φ : Prop) : clProp :=
  {| clProp_holds := ¬¬φ |}.
Next Obligation. tauto. Qed.
Definition clProp_pure_aux : seal (@clProp_pure_def). Proof. by eexists. Qed.
Definition clProp_pure := unseal clProp_pure_aux.
Definition clProp_pure_eq :
  @clProp_pure = @clProp_pure_def := seal_eq clProp_pure_aux.

Program Definition clProp_and_def (P Q : clProp) : clProp :=
  {| clProp_holds := P ∧ Q |}.
Next Obligation. intros [P ?] [Q ?]; simpl in *; tauto. Qed.
Definition clProp_and_aux : seal (@clProp_and_def). Proof. by eexists. Qed.
Definition clProp_and := unseal clProp_and_aux.
Definition clProp_and_eq: @clProp_and = @clProp_and_def := seal_eq clProp_and_aux.

Program Definition clProp_or_def (P Q : clProp) : clProp :=
  {| clProp_holds := ¬¬(P ∨ Q) |}.
Next Obligation. tauto. Qed.
Definition clProp_or_aux : seal (@clProp_or_def). Proof. by eexists. Qed.
Definition clProp_or := unseal clProp_or_aux.
Definition clProp_or_eq: @clProp_or = @clProp_or_def := seal_eq clProp_or_aux.

Program Definition clProp_impl_def (P Q : clProp) : clProp :=
  {| clProp_holds := P → Q |}.
Next Obligation. intros [P ?] [Q ?]; simpl in *; tauto. Qed.
Definition clProp_impl_aux : seal (@clProp_impl_def). Proof. by eexists. Qed.
Definition clProp_impl := unseal clProp_impl_aux.
Definition clProp_impl_eq :
  @clProp_impl = @clProp_impl_def := seal_eq clProp_impl_aux.

Program Definition clProp_forall_def {A} (Ψ : A → clProp) : clProp :=
  {| clProp_holds := ∀ a, Ψ a |}.
Next Obligation. intros A Ψ ? a. apply clProp_stable. naive_solver. Qed.
Definition clProp_forall_aux : seal (@clProp_forall_def). Proof. by eexists. Qed.
Definition clProp_forall {A} := unseal clProp_forall_aux A.
Definition clProp_forall_eq :
  @clProp_forall = @clProp_forall_def := seal_eq clProp_forall_aux.

Program Definition clProp_exist_def {A} (Ψ : A → clProp) : clProp :=
  {| clProp_holds := ¬¬∃ a, Ψ a |}.
Next Obligation. tauto. Qed.
Definition clProp_exist_aux : seal (@clProp_exist_def). Proof. by eexists. Qed.
Definition clProp_exist {A} := unseal clProp_exist_aux A.
Definition clProp_exist_eq: @clProp_exist = @clProp_exist_def := seal_eq clProp_exist_aux.

(** Primitive logical rules.
    These are not directly usable later because they do not refer to the BI
    connectives. *)
Module clProp_primitive.
Definition unseal_eqs :=
  (clProp_pure_eq, clProp_and_eq, clProp_or_eq, clProp_impl_eq, clProp_forall_eq,
  clProp_exist_eq).
Ltac unseal := rewrite !unseal_eqs /=.

Section primitive.
Arguments clProp_holds !_ /.

Notation "P ⊢ Q" := (clProp_entails P Q)
  (at level 99, Q at level 200, right associativity).
Notation "'True'" := (clProp_pure True) : clProp_scope.
Notation "'False'" := (clProp_pure False) : clProp_scope.
Notation "'⌜' φ '⌝'" := (clProp_pure φ%type%stdpp) : clProp_scope.
Infix "∧" := clProp_and : clProp_scope.
Infix "∨" := clProp_or : clProp_scope.
Infix "→" := clProp_impl : clProp_scope.
Notation "¬ P" := (clProp_impl P False) : clProp_scope.
Notation "∀ x .. y , P" := (clProp_forall (λ x, .. (clProp_forall (λ y, P%CL)) ..)) : clProp_scope.
Notation "∃ x .. y , P" := (clProp_exist (λ x, .. (clProp_exist (λ y, P%CL)) ..)) : clProp_scope.

(** Below there follow the primitive laws for [clProp]. There are no derived laws
in this file. *)

(** Entailment *)
Lemma entails_po : PreOrder clProp_entails.
Proof.
  split.
  - intros P. constructor. tauto.
  - intros P Q Q' [HP] [HQ]. constructor. tauto.
Qed.
Lemma entails_anti_symm : AntiSymm (≡) clProp_entails.
Proof. repeat destruct 1; constructor; tauto.  Qed.
Lemma equiv_spec P Q : (P ≡ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
Proof.
  split.
  - intros [HPQ]. split; constructor; tauto.
  - intros [??]. by apply entails_anti_symm.
Qed.

(** Non-expanclveness and setoid morphisms *)
Lemma pure_ne n : Proper (iff ==> dist n) clProp_pure.
Proof. unseal; constructor; simpl; tauto. Qed.
Lemma and_ne : NonExpansive2 clProp_and.
Proof. unseal; repeat destruct 1; constructor; simpl; tauto. Qed.
Lemma or_ne : NonExpansive2 clProp_or.
Proof. unseal; repeat destruct 1; constructor; simpl; tauto. Qed.
Lemma impl_ne : NonExpansive2 clProp_impl.
Proof. unseal; repeat destruct 1; constructor; simpl; tauto. Qed.
Lemma forall_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@clProp_forall A).
Proof.
   unseal=> Ψ1 Ψ2 HΨ; constructor; split=> ? a; destruct (HΨ a); naive_solver.
Qed.
Lemma exist_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@clProp_exist A).
Proof.
   unseal=> Ψ1 Ψ2 HΨ; constructor; split=> H1 ?;
     destruct H1=> -[a ?]; destruct (HΨ a); naive_solver.
Qed.

(** Introduction and elimination rules *)
Lemma pure_intro (φ : Prop) P : φ → P ⊢ ⌜ φ ⌝.
Proof. unseal=> ?. split; simpl; tauto. Qed.
Lemma pure_elim' (φ : Prop) P : (φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P.
Proof.
  unseal=> HP. constructor=> /= Hφ. apply clProp_stable=> ?.
  destruct Hφ=> ?. destruct HP; naive_solver.
Qed.
Lemma pure_forall_2 {A} (φ : A → Prop) : (∀ a, ⌜ φ a ⌝) ⊢ ⌜ ∀ a, φ a ⌝.
Proof.
  unseal; constructor=> /= Hφ. (* FAILS *) Admitted.

Lemma and_elim_l P Q : P ∧ Q ⊢ P.
Proof. unseal; constructor; simpl; tauto. Qed.
Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
Proof. unseal; constructor; simpl; tauto. Qed.
Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
Proof. unseal; intros [?] [?]; constructor; simpl in *; tauto. Qed.

Lemma or_intro_l P Q : P ⊢ P ∨ Q.
Proof. unseal; constructor; simpl; tauto. Qed.
Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
Proof. unseal; constructor; simpl; tauto. Qed.
Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
Proof. unseal; intros [?] [?]; constructor=> /= ?. apply clProp_stable; tauto. Qed.

Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
Proof. unseal; intros [?]; constructor; simpl in *; tauto. Qed.
Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
Proof. unseal; intros [?]; constructor; simpl in *; tauto. Qed.

Lemma forall_intro {A} P (Ψ : A → clProp) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
Proof. unseal; intros HPΨ; constructor=> ? a. by apply (HPΨ a). Qed.
Lemma forall_elim {A} {Ψ : A → clProp} a : (∀ a, Ψ a) ⊢ Ψ a.
Proof. unseal; by constructor. Qed.

Lemma exist_intro {A} {Ψ : A → clProp} a : Ψ a ⊢ ∃ a, Ψ a.
Proof. unseal; constructor; naive_solver. Qed.
Lemma exist_elim {A} (Φ : A → clProp) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
Proof.
   unseal; intros HPΨ; constructor=> HΨ. apply clProp_stable=> HQ.
   destruct HΨ=> -[a ?]. destruct (HPΨ a). naive_solver.
Qed.

Lemma dn (P : clProp) : ¬¬P ⊢ P.
Proof. unseal; constructor=> /= ?. apply clProp_stable. tauto. Qed.

Lemma lem : True ⊢ ∀ P, P ∨ ¬ P.
Proof. unseal; constructor=> /= ?. naive_solver. Qed.

Lemma foo (P Q : Prop) : (¬ ¬ (P -> Q)) <-> (P -> ¬ ¬ Q).
Proof.
  tauto.
Qed.

(** Conclstency/soundness statement *)
Lemma pure_soundness φ : (True ⊢ ⌜ φ ⌝) → ¬¬ φ.
Proof. unseal=> [Hφ]. apply Hφ; simpl; tauto. Qed.

Lemma pure_soundness_dec φ `{!Decision φ} : (True ⊢ ⌜ φ ⌝) → φ.
Proof. intros. by apply dec_stable, pure_soundness. Qed.
End primitive.
End clProp_primitive.
