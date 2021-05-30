From iris.bi Require Import bi.

Definition inv (f : nat → nat) :=
  ∃ g : nat → nat,
    (∀ x, f (g x) = x) ∧ (∀ x, g (f x) = x).

Lemma inv_exists f y : inv f → ∃ x, f x = y.
Proof.
  intros (g & Hg1 & Hg2). exists (g y). rewrite Hg1 //.
Qed.

Definition swap n m : nat → nat :=
  λ i, if decide (i = n) then m else
       if decide (i = m) then n else i.

Lemma swap_swap n m i : swap n m (swap n m i) = i.
Proof.
  unfold swap. repeat case_decide; by subst.
Qed.

Lemma inv_swap n m : inv (swap n m).
Proof.
  exists (swap n m). by setoid_rewrite swap_swap.
Qed.

Lemma inv_comp f g :
  inv f → inv g → inv (f ∘ g).
Proof.
  intros (f' & Hf1 & Hf2) (g' & Hg1 & Hg2).
Proof.
  exists (g' ∘ f'); split; intro; rewrite /= ?Hg1 ?Hf1 ?Hf2 ?Hg2 //.
Qed.

Definition perm {A} (f : nat → nat) (xs : list A) (ys : list A) := ∀ i, xs !! i = ys !! f i.

Lemma swap_lookup {A} i j k (xs : list A) :
  xs !! i = xs !! j → xs !! (swap i j k) = xs !! k.
Proof.
  rewrite /swap. repeat case_decide; subst; eauto.
Qed.

Lemma perm_swap {A} f (xs ys : list A) i j :
  ys !! i = ys !! j → perm f xs ys → perm (swap i j ∘ f) xs ys.
Proof.
  intros Heq Hperm k. simpl. rewrite swap_lookup //.
Qed.

Require Import diris.util.

Definition lift f i := f (S i) - 1.

Lemma perm_app_inv_eq {A} (xs ys : list A) a f :
  (∀ i, f (S i) > 0) → perm f (a :: xs) (a :: ys) -> perm (lift f) xs ys.
Proof.
  intros Hf Hperm k. specialize (Hperm (S k)). specialize (Hf k). unfold lift.
  destruct (f (S k)); first lia. simpl in *. rewrite Hperm. f_equal. lia.
Qed.

Definition Perm {A} (xs ys : list A) := ∃ f, inv f ∧ perm f xs ys.

Lemma inv_gt f :
  inv f → f 0 = 0 → ∀ i, f (S i) > 0.
Proof.
  intros Hf H0 i.
  destruct (f (S i)) eqn:E; try lia.
  destruct Hf as (g & Hg1 & Hg2).
  rewrite -H0 in E.
  apply (f_equal g) in E.
  rewrite !Hg2 in E. simplify_eq.
Qed.

Lemma swap_eq i j : swap i j j = i.
Proof.
  rewrite /swap. by repeat case_decide.
Qed.

Lemma inv_lift f :
  f 0 = 0 → inv f → inv (lift f).
Proof.
  intros Hf (g & Hg1 & Hg2).
  exists (lift g).
  split; intro; rewrite /lift.
Admitted.

Theorem Perm_cons_inv {A} (xs ys : list A) a :
  Perm (a :: xs) (a :: ys) -> Perm xs ys.
Proof.
  intros (f & Hf & Hperm).
  exists (lift (swap 0 (f 0) ∘ f)).
  split.
  - eapply inv_lift; simpl; eauto using swap_eq, inv_swap, inv_comp.
  - eapply perm_app_inv_eq.
    + eapply inv_gt; simpl; eauto using inv_comp, inv_swap, swap_eq.
    + eapply perm_swap; eauto. by specialize (Hperm 0).
Qed.