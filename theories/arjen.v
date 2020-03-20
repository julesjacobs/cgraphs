Require Coq.Lists.List.
From iris.proofmode Require Import tactics.
Open Scope type_scope.

Definition Associative {T : Type} (R : T -> T -> T -> Type) : Type :=
  forall a b ab c abc, R a b ab -> R ab c abc -> sigT (fun bc => (R a bc abc) * (R b c bc)).

Section ListSplit.
  Context {T : Type}.
  Context (Tsplit : T -> T -> T -> Type).

  Inductive listsplit : list T -> list T -> list T -> Type :=
  | divide : forall x x1 x2 xs ys zs , listsplit xs ys zs -> Tsplit x1 x2 x -> listsplit (x1 :: xs) (x2 :: ys) (x :: zs)
  | consl   : forall x xs ys zs , listsplit xs ys zs -> listsplit (x :: xs) ys (x :: zs)
  | consr  : forall x xs ys zs , listsplit xs ys zs -> listsplit xs (x :: ys) (x :: zs)
  | nill : listsplit nil nil nil.


  Hint Resolve divide consl consr nill : listsplit.
  Ltac inv H := inversion H; clear H; subst.

  Lemma listsplit_assoc : Associative Tsplit -> Associative listsplit.
  Proof.
    intros A ????? L1 L2.
    revert a b L1.
    induction L2; intros;[
        inv L1; destruct (IHL2 _ _ X) as [? []]; eauto with listsplit;
        destruct (A _ _ _ _ _ X0 t) as [? []]
      | inv L1; destruct (IHL2 _ _ X) as [? []]
      | destruct (IHL2 _ _ L1) as [? []]
      | inv L1
    ]; eauto with listsplit.
  Qed.
End ListSplit.

Section ListSplit.
  Context (S : Type).

  Inductive semptiness : S -> S -> S -> Type :=.
  Inductive scopy : S -> S -> S -> Type :=
    | copy : forall x, scopy x x x.

  Definition disjoint : list S -> list S -> list S -> Type :=
    listsplit semptiness.

  Definition overlaps : list S -> list S -> list S -> Type :=
    listsplit scopy.

  Inductive permute : list S -> list S -> Type :=
    | refl : forall xs, permute xs xs
    | prep : forall x xs ys, permute xs ys -> permute (x :: xs) (x :: ys)
    | swap : forall x y xs ys, permute xs ys -> permute (x :: y :: xs) (y :: x :: ys)
    | trans : forall xs ys zs, permute xs ys -> permute ys zs -> permute xs zs.

  Definition module := list S * list S.

  Definition exchange : list S -> list S -> module -> Type := fun d u m =>
      sigT (fun e => sigT (fun e' =>
      (disjoint (snd m) e d) *
      (overlaps (fst m) e' u) *
      permute e e')).

  Inductive modulesplit : module -> module -> module -> Type :=
    | msplit : forall {u1 d1 u2 d2 u1' d1' u2' d2' u d},
        exchange d1 u2 (u2' , d2') ->
        exchange d2 u1 (u1' , d1') ->
        disjoint u1' u2' u ->
        overlaps d1' d2' d ->
        modulesplit (u1 , d1) (u2 , d2) (u , d).

  Ltac inv H := inversion H; clear H; subst.
  Hint Resolve divide consl consr nill copy refl prep swap trans : listsplit.
  Ltac simpl_rel := repeat match goal with
    | H : semptiness _ _ _ |- _ => inv H
    | H : scopy _ _ _ |- _ => inv H
    end.

  Lemma xsplit a b c d zs :
    overlaps a b zs -> disjoint c d zs ->
    {ac & {ad & {bc & {bd &
      overlaps ac bc c * overlaps ad bd d *
      disjoint ac ad a * disjoint bc bd b }}}}.
  Proof.
    revert a b c d. induction zs as [|z zs]; intros ???? O D.
    { inv O. inv D. do 4 eexists; repeat split; constructor. }
    inv O; inv D; simpl_rel;
    match goal with
    | H : listsplit scopy _ _ _, H' : listsplit semptiness _ _ _ |- _ =>
      destruct (IHzs _ _ _ _ H H') as [? [? [? [? [[[] ?] ?]]]]]
    end; simpl_rel; do 4 eexists; repeat split;
    try eassumption; constructor; eauto with listsplit.
  Qed.

  Lemma same {T} {x} {r : T -> T -> T -> Type} : listsplit r [] x x.
  Proof. induction x; eauto with listsplit. Qed.

  Lemma same' {T} {x} {r : T -> T -> T -> Type} : listsplit r x [] x.
  Proof. induction x; eauto with listsplit. Qed.

  Lemma is_same {T} {x y} {r : T -> T -> T -> Type} : listsplit r [] x y -> x = y.
  Proof.
    revert y.
    induction x.
    - intros. inv X. reflexivity.
    - intros. inv X. specialize (IHx _ X0). subst. reflexivity.
  Qed.

  Lemma is_same' {T} {x y} {r : T -> T -> T -> Type} : listsplit r x [] y -> x = y.
  Proof.
    revert y.
    induction x.
    - intros. inv X. reflexivity.
    - intros. inv X. specialize (IHx _ X0). subst. reflexivity.
  Qed.

  Fixpoint xup a b ab c bc :
    disjoint a b ab → overlaps b c bc →
    sigT (fun abc => disjoint a bc abc * overlaps ab c abc).
  Proof.
    intros D O.
    inversion D; inversion O; subst; simpl_rel; fold overlaps disjoint in *.
    - destruct (xup _ _ _ _ _ X O) as [? []].
      eexists. split; constructor; eassumption.
    - destruct (xup _ _ _ _ _ X O) as [? []].
      eexists. split; constructor; eassumption.
    - destruct (xup _ _ _ _ _ D X0) as [? []].
      eexists. split; constructor; eassumption.
    - rewrite (is_same' X). eexists. split; apply same'.
    - injection H2 as -> ->.
      destruct (xup _ _ _ _ _ X X0) as [? []].
      eexists. split; constructor; eassumption || constructor.
    - injection H2 as -> ->.
      destruct (xup _ _ _ _ _ X X0) as [? []].
      eexists. split; constructor; eassumption || constructor.
    - destruct (xup _ _ _ _ _ D X0) as [? []].
      eexists. split; constructor; eassumption || constructor.
    - inv H2.
    - inv H2.
    - inv H2. 
    - pose proof (is_same O). inv H.
      eexists. split; constructor; try eassumption. apply same.
    - exists []. split; constructor.
  Qed.

  Lemma modulesplit_assoc : Associative modulesplit.
  Proof.
    unfold Associative.
    intros.
    inv X.
    inv X0.
    destruct X1,X2,X,X5.
    destruct s,s0,s1,s2. simpl in *.
    repeat match goal with
    H : _ * _ |- _ => destruct H
    end.
    eexists.
    split; econstructor; unfold exchange in *; simpl in *;
    repeat eexists; repeat split.
  Qed.