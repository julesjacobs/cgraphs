From cgraphs.locks.lambdalockpp Require Export langdef definitions.

Notation vertex := nat.
Inductive label : Type :=
  | BarrierLabel (b : bool) (t1 t2 : type)
  | LockLabel (ls : list (nat * (lockcap * type))).

(*
runtime state          type of lock group reference
<n|i1,i2,i3> : LockGT [(cap1,t1), (cap2,t2), (cap3,t3)]

label: [(i1,cap1,t1), (i2,cap2,t2), (i3,cap3,t3)]
*)

Canonical Structure typeO := leibnizO type.
Canonical Structure labelO := leibnizO label.

Notation rProp := (hProp vertex labelO).

Definition linbox l (P : rProp) : rProp :=
  match l with
  | Lin => P
  | Unr => □ P
  end.

Fixpoint rtyped (Γ : env) e t : rProp :=
  match e with
  | Val v => ⌜⌜ env_unr Γ ⌝⌝ ∗ vtyped v t
  | Var x => ⌜⌜ env_var Γ x t ⌝⌝
  | Fun x e =>
      ∃ l t1 t2, ⌜⌜ t = FunT l t1 t2 ⌝⌝  ∗
      ∃ Γ', ⌜⌜ env_bind Γ' x t1 Γ ∧ (l = Unr -> env_unr Γ) ⌝⌝ ∗
      linbox l (rtyped Γ' e t2)
  | App e1 e2 =>
      ∃ Γ1 Γ2, ⌜⌜ env_split Γ Γ1 Γ2 ⌝⌝ ∗
      ∃ t1 l,
      rtyped Γ1 e1 (FunT l t1 t) ∗
      rtyped Γ2 e2 t1
  | Unit => ⌜⌜ t = UnitT ∧ env_unr Γ ⌝⌝
  | Pair e1 e2 =>
      ∃ Γ1 Γ2, ⌜⌜ env_split Γ Γ1 Γ2 ⌝⌝ ∗
      ∃ t1 t2, ⌜⌜ t = PairT t1 t2 ⌝⌝ ∗
      rtyped Γ1 e1 t1 ∗ rtyped Γ2 e2 t2
  | LetPair e1 e2 =>
      ∃ Γ1 Γ2, ⌜⌜ env_split Γ Γ1 Γ2 ⌝⌝ ∗
      ∃ t1 t2,
      rtyped Γ1 e1 (PairT t1 t2) ∗
      rtyped Γ2 e2 (FunT Lin t1 (FunT Lin t2 t))
  | Sum i e =>
      ∃ n (ts : fin n -> type) (i' : fin n), ⌜⌜ t = SumT n ts ⌝⌝ ∗ ⌜⌜ i = i' ⌝⌝ ∗
      rtyped Γ e (ts i')
  | MatchSum n e es =>
      ∃ Γ1 Γ2, ⌜⌜ env_split Γ Γ1 Γ2 ∧ (n = 0 -> env_unr Γ2)⌝⌝ ∗
      ∃ ts,
      rtyped Γ1 e (SumT n ts) ∗
      if decide (n=0) then ⌜⌜ env_unr Γ2 ⌝⌝ else (∀ i, rtyped Γ2 (es i) (FunT Lin (ts i) t))
  (* Barriers *)
  | ForkBarrier e =>
      ∃ t1 t2, ⌜⌜ t = FunT Lin t1 t2 ⌝⌝ ∗
      rtyped Γ e (FunT Lin (FunT Lin t2 t1) UnitT)
  (* Locks *)
  | NewGroup => ⌜⌜ t = LockGT [] ∧ env_unr Γ ⌝⌝
  | DropGroup e =>
      ⌜⌜ t = UnitT ⌝⌝ ∗ rtyped Γ e (LockGT [])
  | NewLock i e =>
      ∃ t' (xs : list (lockcap * type)), ⌜⌜ t = LockGT (insert2 i ((Owner,Opened),t') xs) ⌝⌝ ∗
      rtyped Γ e (LockGT xs)
  | DropLock i e =>
      ∃ t' (xs : list (lockcap * type)), ⌜⌜ t = (LockGT (delete i xs)) ∧ xs !! i = Some ((Client,Closed),t')⌝⌝ ∗
      rtyped Γ e (LockGT xs)
  | Wait i e =>
      ∃ (t' : type) (xs : list (lockcap * type)), ⌜⌜ t = (PairT (LockGT (delete i xs)) t') ∧ xs !! i = Some ((Owner,Closed),t') ∧
        (∀ j ownership state t', xs !! j = Some ((ownership,state),t') ->
          (state = Closed) ∧ (j < i -> ownership = Owner)) ⌝⌝ ∗
      rtyped Γ e (LockGT xs)
  | Acquire i e =>
      ∃ (t':type) (a:lockownership) (xs : list (lockcap * type)),
      ⌜⌜ t = (PairT (LockGT (<[ i := ((a,Opened),t') ]> xs)) t') ∧ xs !! i = Some ((a,Closed),t') ∧
        (∀ j ownership state t', j < i -> xs !! j = Some ((ownership,state),t') -> state = Closed) ⌝⌝ ∗
      rtyped Γ e (LockGT xs)
  | Release i e1 e2 =>
      ∃ Γ1 Γ2, ⌜⌜ env_split Γ Γ1 Γ2 ⌝⌝ ∗
      ∃ a t' (xs : list (lockcap * type)), ⌜⌜ t = (LockGT (<[ i := ((a,Closed),t') ]> xs)) ∧ xs !! i = Some ((a,Opened),t') ⌝⌝ ∗
      rtyped Γ1 e1 (LockGT xs) ∗
      rtyped Γ2 e2 t'
  | ForkLock e1 e2 =>
      ∃ Γ1 Γ2, ⌜⌜ env_split Γ Γ1 Γ2 ⌝⌝ ∗
      ∃ xs1 xs2 xs3 : list (lockcap * type), ⌜⌜ t = LockGT xs3 ∧ lockcaps_split xs1 xs2 xs3 ⌝⌝ ∗
      rtyped Γ1 e1 (LockGT xs1) ∗
      rtyped Γ2 e2 (FunT Lin (LockGT xs2) UnitT)
  end
with vtyped v t :=
  match v with
  | FunV x e =>
      ∃ l t1 t2, ⌜⌜ t = FunT l t1 t2 ⌝⌝ ∗ linbox l (rtyped {[ x := t1 ]} e t2)
  | UnitV => ⌜⌜ t = UnitT ⌝⌝
  | PairV v1 v2 =>
      ∃ t1 t2, ⌜⌜ t = PairT t1 t2 ⌝⌝ ∗
      vtyped v1 t1 ∗ vtyped v2 t2
  | SumV i v =>
      ∃ n ts (i' : fin n), ⌜⌜ t = SumT n ts ∧ i = i' ⌝⌝ ∗
      vtyped v (ts i')
  | BarrierV k =>
      ∃ t1 t2, ⌜⌜ t = FunT Lin t1 t2 ⌝⌝ ∗
      own_out k ((BarrierLabel false t1 t2) : labelO)
  | LockGV k ls =>
      ∃ (xs : list (lockcap * type)), ⌜⌜ t = LockGT xs ∧ length xs = length ls ⌝⌝ ∗
      own_out k ((LockLabel (zip ls xs)) : labelO)
  end.

Lemma typed_rtyped Γ e t :
  ⌜⌜ typed Γ e t ⌝⌝ -∗ rtyped Γ e t.
Proof.
  iIntros (H).
  iInduction e as [] "IH" forall (t Γ H);
  inv H; simpl; eauto; repeat iExists _; try iSplitL; eauto;
  repeat iExists _; try iSplitL; eauto; try iSplitL;
  try destruct l; try case_decide; repeat iIntros (?); subst; eauto;
  try solve [ iApply ("IH" with "[%]") || iApply ("IH1" with "[%]"); eauto].
Qed.

(* From stdpp's naive_solver *)
Ltac simp :=
  repeat match goal with
  (**i solve the goal *)
  | |- _ => fast_done
  (**i intros *)
  | |- ∀ _, _ => intro
  (**i simplification of assumptions *)
  | H : False |- _ => destruct H
  | H : _ ∧ _ |- _ =>
     (* Work around bug https://coq.inria.fr/bugs/show_bug.cgi?id=2901 *)
     let H1 := fresh in let H2 := fresh in
     destruct H as [H1 H2]; try clear H
  | H : ∃ _, _  |- _ =>
     let x := fresh in let Hx := fresh in
     destruct H as [x Hx]; try clear H
  | H : ?P → ?Q, H2 : ?P |- _ => specialize (H H2)
  | H : Is_true (bool_decide _) |- _ => apply (bool_decide_unpack _) in H
  | H : Is_true (_ && _) |- _ => apply andb_True in H; destruct H
  (**i simplify and solve equalities *)
  | |- _ => progress simplify_eq/=
  (**i operations that generate more subgoals *)
  (* | |- _ ∧ _ => split *)
  (* | |- Is_true (bool_decide _) => apply (bool_decide_pack _) *)
  (* | |- Is_true (_ && _) => apply andb_True; split *)
  (* | H : _ ∨ _ |- _ => *)
     (* let H1 := fresh in destruct H as [H1|H1]; try clear H *)
  (* | H : Is_true (_ || _) |- _ => *)
     (* apply orb_True in H; let H1 := fresh in destruct H as [H1|H1]; try clear H *)
  (**i solve the goal using the user supplied tactic *)
  end.

Ltac iDestr H := repeat (iDestruct "H" as %? || iDestruct H as (?) H).
Ltac iSpl := repeat (iExists _ || iSplit || iIntros (?)).

Lemma unrestricted_box v t :
  unr t -> vtyped v t -∗ □ vtyped v t.
Proof.
  iIntros (H) "H".
  iInduction v as [] "IH" forall (t H); simpl;
  iDestr "H"; simp; inv H; simp; eauto.
  - iDestruct "H" as "#H". iModIntro. eauto.
  - iDestruct "H" as "[H1 H2]".
    iDestruct ("IH" with "[%] H1") as "H1"; first done.
    iDestruct ("IH1" with "[%] H2") as "H2"; first done.
    iDestruct "H1" as "#H1".
    iDestruct "H2" as "#H2".
    iModIntro. repeat (iExists _ || iSplitL); eauto.
  - iDestruct ("IH" with "[%] H") as "H"; first done.
    iDestruct "H" as "#H". iModIntro. eauto.
Qed.


Definition substR (Γ : env) x v := from_option (vtyped v) emp%I (Γ !! x).

Ltac sdec := repeat case_decide; simplify_eq; simpl in *; eauto; try done.
Ltac smap := repeat (rewrite lookup_alter_spec || rewrite lookup_union || rewrite lookup_insert_spec || rewrite lookup_delete_spec || sdec).

Lemma env_unr_substR Γ x v :
  env_unr Γ -> substR Γ x v ⊢ emp.
Proof.
  rewrite /env_unr /substR.
  destruct (Γ !! x) eqn:E; simp.
  rewrite unrestricted_box; eauto.
Qed.

Lemma env_split_substR Γ Γ1 Γ2 x v :
  env_split Γ Γ1 Γ2 -> substR Γ x v ⊢ substR Γ1 x v ∗ substR Γ2 x v.
Proof.
  rewrite /env_split /substR. simp.
  rewrite lookup_union.
  destruct (Γ1 !! x) eqn:E;
  destruct (Γ2 !! x) eqn:F; rewrite ?E ?F; simpl; eauto.
  edestruct (H1 x); eauto. simp.
  iIntros "H".
  iDestruct (unrestricted_box with "H") as "H"; eauto.
  iDestruct "H" as "#H". iSplitL; eauto.
Qed.

Lemma env_var_substR Γ x y v t :
  env_var Γ y t ->
  substR Γ x v ⊢ if decide (x = y) then vtyped v t else emp.
Proof.
  rewrite /env_var /substR. simp. smap.
  destruct (_!!_) eqn:E; simp.
  rewrite unrestricted_box; eauto.
Qed.

Lemma env_bind_substR Γ Γ' l x y v t :
  (l = Unr -> env_unr Γ) -> env_bind Γ' y t Γ ->
  substR Γ x v ⊢ if decide (x = y) then emp else linbox l (substR Γ' x v).
Proof.
  rewrite /env_bind /substR. simp. smap.
  - destruct (Γ !! y) eqn:E; simpl; eauto.
    rewrite unrestricted_box; eauto.
  - destruct (Γ !! x) eqn:E; rewrite ?E; destruct l; eauto; simpl.
    rewrite {1}unrestricted_box; eauto.
    eapply H; eauto.
Qed.

Lemma env_unr_delete Γ x :
  env_unr Γ -> env_unr (delete x Γ).
Proof.
  rewrite /env_unr. intros ???. smap.
Qed.

Lemma env_split_delete Γ Γ1 Γ2 x :
  env_split Γ Γ1 Γ2 -> env_split (delete x Γ) (delete x Γ1) (delete x Γ2).
Proof.
  rewrite /env_split /disj. simp.
  split; [apply delete_union|].
  intros ???. smap.
Qed.

Lemma env_var_delete y x Γ t :
  env_var Γ x t -> if decide (y = x) then env_unr (delete y Γ) else env_var (delete y Γ) x t.
Proof.
  rewrite /env_var /env_unr. simp. smap.
  - simp. revert H. smap.
  - exists (delete y H0). split.
    + apply map_eq. intro. smap.
    + intros ??. smap.
Qed.

Lemma env_bind_delete x y t Γ Γ' :
  env_bind Γ' x t Γ ->
  env_bind (if decide (y = x) then Γ' else delete y Γ') x t (delete y Γ).
Proof.
  rewrite /env_bind. simp.
  split.
  - apply map_eq. intro. smap.
  - intro. smap.
Qed.

Lemma env_unr_empty :
  env_unr ∅.
Proof.
  rewrite /env_unr. intros ??. smap.
Qed.

Lemma env_split_empty Γ1 Γ2 :
  env_split ∅ Γ1 Γ2 <-> Γ1 = ∅ ∧ Γ2 = ∅.
Proof.
  rewrite /env_split.
  split. simp.
  - symmetry in H0.
    pose proof (map_positive_l _ _ H0). subst.
    rewrite left_id in H0. subst. eauto.
  - simp. rewrite left_id. split; eauto.
    rewrite /disj. intros ??. smap.
Qed.

Lemma env_var_empty x t :
  env_var ∅ x t <-> False.
Proof.
  rewrite /env_var. split; simp.
  rewrite map_eq_iff in H. specialize (H x). revert H. smap.
Qed.

Lemma env_bind_empty Γ x t1 :
  env_bind Γ x t1 ∅ <-> Γ = {[ x := t1 ]}.
Proof.
  rewrite /env_bind. repeat split; simp.
Qed.


Lemma linbox_mono P Q l :
  □ (P -∗ Q) -∗ linbox l P -∗ linbox l Q.
Proof.
  iIntros "#H P".
  destruct l; simpl; [|iDestruct "P" as "#P"; iModIntro];
  iApply "H"; done.
Qed.

Lemma linbox_sep P Q l :
  linbox l P ∗ linbox l Q ⊢ linbox l (P ∗ Q).
Proof.
  destruct l; simpl; eauto.
  iIntros "[#H #R]". iModIntro.
  iSplitL; eauto.
Qed.


Lemma substitution Γ x v e t :
  substR Γ x v ∗
  rtyped Γ e t -∗
  rtyped (delete x Γ) (subst x v e) t.
Proof.
  iIntros "RH".
  iInduction e as [] "IH" forall (Γ t); simpl;
  iDestruct "RH" as "[R H]"; iDestr "H"; try iDestruct "H" as "[H Q]"; simp.
  - rewrite env_unr_substR //. iSpl; eauto using env_unr_delete.
  - rewrite env_var_substR //.
    eapply (env_var_delete x) in H.
    case_decide; subst; simpl; iFrame; iPureIntro; eauto.
  - iExists _,_,_. iSplit; first done.
    iExists _. iSplit; eauto 6 using env_bind_delete, env_unr_delete.
    rewrite env_bind_substR; eauto.
    case_decide; subst; iFrame.
    iApply linbox_mono; eauto.
    iApply linbox_sep. iFrame.
  - iDestruct (env_split_substR with "R") as "[R1 R2]"; eauto.
    iSpl; eauto using env_split_delete.
    iSplitL "H R1"; (iApply "IH" || iApply "IH1"); eauto with iFrame.
  - rewrite env_unr_substR //.
    eauto using env_unr_delete.
  - iDestruct (env_split_substR with "R") as "[R1 R2]"; eauto.
    iSpl; eauto using env_split_delete.
    iSplitL "H R1"; (iApply "IH" || iApply "IH1"); eauto with iFrame.
  - iDestruct (env_split_substR with "R") as "[R1 R2]"; eauto.
    iSpl; eauto using env_split_delete.
    iSplitL "H R1"; (iApply "IH" || iApply "IH1"); eauto with iFrame.
  - iSpl; eauto. iApply "IH". iFrame.
  - iDestruct (env_split_substR with "R") as "[R1 R2]"; eauto.
    iSpl; first iPureIntro; eauto using env_split_delete, env_unr_delete.
    case_decide; subst.
    { iDestruct "Q" as "%". iSplit; eauto using env_unr_delete.
      eapply env_unr_substR in H. rewrite H.
      iApply "IH1". iFrame. }
    iSplitL "H R1"; iSpl; (iApply "IH" || iApply "IH1"); eauto with iFrame.
  - iSpl; eauto. (iApply "IH" || iApply "IH1"); eauto with iFrame.
  - rewrite env_unr_substR //. iPureIntro. split; eauto using env_unr_delete.
  - iSpl; eauto. iApply "IH". iFrame.
  - iSpl; eauto. iApply "IH". iFrame.
  - iSpl; eauto. iApply "IH". iFrame.
  - iSpl; eauto using env_split_delete.
    iDestruct (env_split_substR with "R") as "[R1 R2]"; eauto.
    iSplitL "H R1"; (iApply "IH" || iApply "IH1"); iFrame.
  - iSpl; eauto. iApply "IH". iFrame.
  - iSpl; eauto using env_split_delete.
    iDestruct (env_split_substR with "R") as "[R1 R2]"; eauto.
    iSplitL "H R1"; (iApply "IH" || iApply "IH1"); iFrame.
  - iSpl; eauto. iApply "IH". iFrame.
Qed.

Fixpoint rtyped0 e t : rProp :=
  match e with
  | Val v => vtyped v t
  | Var x => False
  | Fun x e =>
      ∃ l t1 t2, ⌜⌜ t = FunT l t1 t2 ⌝⌝ ∗
      ∃ Γ, ⌜⌜ env_bind Γ x t1 ∅ ⌝⌝ ∗
      linbox l (rtyped Γ e t2)
  | App e1 e2 =>
      ∃ t1 l,
      rtyped0 e1 (FunT l t1 t) ∗
      rtyped0 e2 t1
  | Unit => ⌜⌜ t = UnitT ⌝⌝
  | Pair e1 e2 =>
      ∃ t1 t2, ⌜⌜ t = PairT t1 t2 ⌝⌝ ∗
      rtyped0 e1 t1 ∗ rtyped0 e2 t2
  | LetPair e1 e2 =>
      ∃ t1 t2,
      rtyped0 e1 (PairT t1 t2) ∗
      rtyped0 e2 (FunT Lin t1 (FunT Lin t2 t))
  | Sum i e =>
      ∃ n (ts : fin n -> type) (i' : fin n), ⌜⌜ t = SumT n ts ⌝⌝ ∗ ⌜⌜ i = i' ⌝⌝ ∗
      rtyped0 e (ts i')
  | MatchSum n e es =>
      ∃ ts,
      rtyped0 e (SumT n ts) ∗
      if decide (n=0) then emp else (∀ i, rtyped0 (es i) (FunT Lin (ts i) t))
  (* Barriers *)
  | ForkBarrier e =>
      ∃ t1 t2, ⌜⌜ t = FunT Lin t1 t2 ⌝⌝ ∗
      rtyped0 e (FunT Lin (FunT Lin t2 t1) UnitT)
  (* Locks *)
  | NewGroup => ⌜⌜ t = LockGT [] ⌝⌝
  | DropGroup e =>
      ⌜⌜ t = UnitT ⌝⌝ ∗ rtyped0 e (LockGT [])
  | NewLock i e =>
      ∃ t' (xs : list (lockcap * type)), ⌜⌜ t = LockGT (insert2 i ((Owner,Opened),t') xs) ⌝⌝ ∗
      rtyped0 e (LockGT xs)
  | DropLock i e =>
      ∃ t' (xs : list (lockcap * type)), ⌜⌜ t = (LockGT (delete i xs)) ∧ xs !! i = Some ((Client,Closed),t')⌝⌝ ∗
      rtyped0 e (LockGT xs)
  | Wait i e =>
      ∃ (t' : type) (xs : list (lockcap * type)), ⌜⌜ t = PairT (LockGT (delete i xs)) t' ∧ xs !! i = Some ((Owner,Closed),t') ∧
        (∀ j ownership state t', xs !! j = Some ((ownership,state),t') ->
          (state = Closed) ∧ (j < i -> ownership = Owner)) ⌝⌝ ∗
      rtyped0 e (LockGT xs)
  | Acquire i e =>
      ∃ (t':type) (a:lockownership) (xs : list (lockcap * type)),
      ⌜⌜ t = (PairT (LockGT (<[ i := ((a,Opened),t') ]> xs)) t') ∧ xs !! i = Some ((a,Closed),t') ∧
        (∀ j ownership state t', j < i -> xs !! j = Some ((ownership,state),t') -> state = Closed) ⌝⌝ ∗
      rtyped0 e (LockGT xs)
  | Release i e1 e2 =>
      ∃ a t' (xs : list (lockcap * type)), ⌜⌜ t = (LockGT (<[ i := ((a,Closed),t') ]> xs)) ∧ xs !! i = Some ((a,Opened),t') ⌝⌝ ∗
      rtyped0 e1 (LockGT xs) ∗
      rtyped0 e2 t'
  | ForkLock e1 e2 =>
      ∃ xs1 xs2 xs3 : list (lockcap * type), ⌜⌜ t = LockGT xs3 ∧ lockcaps_split xs1 xs2 xs3 ⌝⌝ ∗
      rtyped0 e1 (LockGT xs1) ∗
      rtyped0 e2 (FunT Lin (LockGT xs2) UnitT)
  end.


Lemma rtyped_rtyped0 e t :
  rtyped ∅ e t ⊣⊢ rtyped0 e t.
Proof.
  revert t. induction e; intros; simpl;
  iSplit; iIntros "H";
  try setoid_rewrite env_split_empty;
  try setoid_rewrite env_var_empty;
  try setoid_rewrite env_bind_empty;
  iDestr "H"; simp; eauto using env_unr_empty;
  try iDestruct "H" as "[H Q]";
  repeat (iExists _ || iSplit); eauto using env_unr_empty;
  rewrite ?H ?IHe ?IHe1 ?IHe2; try case_decide; iFrame; eauto using env_unr_empty;
  iIntros (?); setoid_rewrite H; eauto.
Qed.

Lemma substitution0 v t1 t2 x e :
  vtyped v t1 ∗
  rtyped {[ x := t1 ]} e t2 -∗
  rtyped0 (subst x v e) t2.
Proof.
  rewrite -rtyped_rtyped0.
  iIntros "[H Q]".
  iDestruct (substitution _ x v e t2 with "[H Q]") as "H"; iFrame.
  - rewrite /substR lookup_singleton //.
  - rewrite delete_singleton //.
Qed.

Lemma pure_preservation e e' t :
  pure_step e e' ->
  rtyped0 e t -∗ rtyped0 e' t.
Proof.
  intros []; simpl;
  iIntros "H";
  try setoid_rewrite env_bind_empty;
  repeat (iDestr "H" || iDestruct "H" as "[H ?]"); simp;
  repeat (iExists _ || iSplit || case_decide); eauto with iFrame.
  - iApply substitution0. iFrame. by destruct l0.
  - subst. inv_fin i'.
Qed.

Lemma replacement1 k e B :
  ctx1 k ->
  rtyped0 (k e) B -∗ ∃ t, rtyped0 e t ∗ ∀ e', rtyped0 e' t -∗ rtyped0 (k e') B.
Proof.
  destruct 1; simpl; iIntros "H";
  iDestr "H"; try iDestruct "H" as "[H Q]";
  eauto 9 with iFrame.
Qed.

Lemma replacement k e B :
  ctx k ->
  rtyped0 (k e) B ⊣⊢ ∃ t, rtyped0 e t ∗ ∀ e', rtyped0 e' t -∗ rtyped0 (k e') B.
Proof.
  intros Hk.
  iSplit; iIntros "H"; last first.
  { iDestruct "H" as (t) "[H Q]". by iApply "Q". }
  iInduction Hk as [] "IH" forall (B e); simpl.
  { iExists _. iFrame. eauto. } subst.
  iDestruct (replacement1 with "H") as (?) "[H R]"; eauto.
  iDestruct ("IH" with "H") as (?) "[Q H]".
  iExists _. iFrame. iIntros (?) "?".
  iApply "R". iApply "H". done.
Qed.


Ltac solve_ctx := solve [iPureIntro; do 2 eexists; split; last done; eauto using ctx, ctx1].
Ltac solve_step := solve [iPureIntro; do 2 eexists; split; eauto using Ctx_id; simp; eauto using pure_step].

Ltac solve_pr := simp; solve [solve_ctx || solve_step].

Inductive impure : expr -> Prop :=
  | imp_ForkBarrier v : impure (ForkBarrier (Val v))
  | imp_NewGroup : impure NewGroup
  | imp_Waiting e i : expr_head_waiting e i -> impure e.

Definition step_or_impure e := ∃ k e0,
  ctx k ∧ e = k e0 ∧ ((∃ e', pure_step e0 e') ∨ impure e0).

Lemma step_or_impure_ctx1 e e0 k :
  ctx1 k -> e0 = k e -> step_or_impure e -> step_or_impure e0.
Proof.
  intros Hctx -> (k' & e' & Hctx' & -> & D).
  unfold step_or_impure. eexists (k ∘ k'),_.
  eauto using Ctx_comp.
Qed.

Lemma pure_step_or_impure e e' :
  pure_step e e' -> step_or_impure e.
Proof.
  intros Hs. eexists id,_;
  eauto using Ctx_id.
Qed.

Lemma impure_or_impure e :
  impure e -> step_or_impure e.
Proof.
  intros Hi. eexists id,_;
  eauto using Ctx_id.
Qed.

Definition is_Val e := ∃ v, e = Val v.

Ltac into_val H1 H2 :=
  iDestruct (H1 with H2) as %[[? ->]|?];
  last by eauto using step_or_impure_ctx1, ctx1.

Ltac ppdone := simp; eauto using pure_step_or_impure, pure_step, impure_or_impure, impure, expr_head_waiting.

Lemma pure_progress e t :
  rtyped0 e t -∗ ⌜ is_Val e ∨ step_or_impure e ⌝.
Proof.
  iIntros "H".
  iInduction e as [] "IH" forall (t); simpl; eauto;
  first (iLeft; unfold is_Val; by eauto); iRight.
  (* Base language *)
  - ppdone.
  - iDestr "H". iDestruct "H" as "[H H1]".
    into_val "IH" "H".
    into_val "IH1" "H1".
    destruct x; simpl; iDestr "H"; ppdone.
  - ppdone.
  - iDestr "H". iDestruct "H" as "[H H1]".
    into_val "IH" "H".
    into_val "IH1" "H1".
    ppdone.
  - iDestr "H". iDestruct "H" as "[H H1]".
    into_val "IH" "H". simpl.
    destruct x; simpl; iDestr "H"; ppdone.
  - iDestr "H"; simp.
    into_val "IH" "H". simpl.
    ppdone.
  - iDestr "H". iDestruct "H" as "[H H1]".
    into_val "IH1" "H". simpl.
    destruct x; simpl; iDestr "H";
    ppdone.
  (* Barriers *)
  - iDestr "H".
    into_val "IH" "H". ppdone.
  (* Locks *)
  - iDestr "H". ppdone.
  - iDestr "H". into_val "IH" "H". simpl.
    destruct x; simpl; iDestr "H"; simp.
    ppdone.
  - iDestr "H".
    into_val "IH" "H".
    destruct x; simpl; iDestr "H"; simp.
    ppdone.
  - iDestr "H".
    into_val "IH" "H".
    destruct x; simpl; iDestr "H"; simp.
    ppdone.
  - iDestr "H". iDestruct "H" as "[H H1]".
    into_val "IH" "H".
    into_val "IH1" "H1".
    destruct x; simpl; iDestr "H"; simp.
    ppdone.
  - iDestr "H".
    into_val "IH" "H".
    destruct x; simpl; iDestr "H"; simp.
    ppdone.
  - iDestr "H". iDestruct "H" as "[H H1]".
    into_val "IH" "H".
    into_val "IH1" "H1".
    destruct x; simpl; iDestr "H"; simp.
    ppdone.
  - iDestr "H".
    into_val "IH" "H".
    destruct x; simpl; iDestr "H"; simp.
    ppdone.
Qed.