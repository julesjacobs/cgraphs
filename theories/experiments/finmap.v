From iris Require Import bi.

Definition finmap A := list (nat * A).

Fixpoint lookup {A} (m : finmap A) (x : nat) : option A :=
  match m with
  | [] => None
  | (x',y) :: m =>
      if decide (x < x') then None
      else if decide (x = x') then Some y
      else lookup m (x - S x')
  end.

Ltac simp := simpl in *; repeat case_decide; (lia || simplify_eq); eauto.

Lemma map_eq {A} (m1 m2 : finmap A) :
  (∀ x, lookup m1 x = lookup m2 x) -> m1 = m2.
Proof.
  revert m2; induction m1 as [|[x1' y1] m1 IH]; intros [|[x2' y2] m2] H;
  try pose proof (H x1'); try pose proof (H x2'); simp.
  f_equal. apply IH. intros x. specialize (H (x + S x1')).
  replace (x + S x1' - S x1') with x in H by lia. simp.
Qed.

Definition empty A : finmap A := [].
Definition singleton {A} (x : nat) (y : A) := [(x,y)].

Lemma lookup_empty {A} x : lookup (empty A) x = None.
Proof. simp. Qed.

Lemma lookup_singleton {A} x x' (y : A) :
  lookup (singleton x y) x' = if decide (x = x') then Some y else None.
Proof. simp. Qed.

Fixpoint insert {A} (m : finmap A) x y :=
  match m with
  | [] => [(x,y)]
  | (x',y') :: m =>
      if decide (x < x') then (x,y)::(x' - S x,y')::m
      else if decide (x = x') then (x,y)::m
      else (x',y')::insert m (x - S x') y
  end.

Lemma lookup_insert {A} (m : finmap A) x y x' :
  lookup (insert m x y) x' = if decide (x = x') then Some y else lookup m x'.
Proof.
  revert x x'; induction m as [|[x1 y1] m IH]; intros x x';
  simp; simp; [f_equal|rewrite IH..]; simp.
Qed.