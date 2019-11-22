From iris.program_logic Require Export adequacy.
From iris.heap_lang Require Export lang notation tactics.

(** This file contains the proof that prophecies can be safely erased
from programs. We erase a program by replacing prophecy identifiers
with the unit values and respectively adapt the [NewProph] and [Resolve]
expressions. We prove that if a program [e] is safe with respect to a (pure)
postcondition [φ], then program [erase e] is also safe with respect to [φ]. *)

Implicit Types e : expr.
Implicit Types v w : val.
Implicit Types l : loc.
Implicit Types n m : Z.
Implicit Types i : nat.

Definition erase_base_lit (l : base_lit) : base_lit :=
  match l with
  | LitProphecy p => LitPoison
  | _ => l
  end.

Definition erase_resolve (e0 e1 e2 : expr) : expr := Fst (Fst (e0, e1, e2)).

Definition erased_new_proph : expr := (λ: <>, #LitPoison)%V #().

Fixpoint erase_expr (e : expr) : expr :=
  match e with
  | Val v => Val (erase_val v)
  | Var x => Var x
  | Rec f x e => Rec f x (erase_expr e)
  | App e1 e2 => App (erase_expr e1) (erase_expr e2)
  | UnOp op e => UnOp op (erase_expr e)
  | BinOp op e1 e2 => BinOp op (erase_expr e1) (erase_expr e2)
  | If e0 e1 e2 => If (erase_expr e0) (erase_expr e1) (erase_expr e2)
  | Pair e1 e2 => Pair (erase_expr e1) (erase_expr e2)
  | Fst e => Fst (erase_expr e)
  | Snd e => Snd (erase_expr e)
  | InjL e => InjL (erase_expr e)
  | InjR e => InjR (erase_expr e)
  | Case e0 e1 e2 => Case (erase_expr e0) (erase_expr e1) (erase_expr e2)
  | Fork e => Fork (erase_expr e)
  | AllocN e1 e2 => AllocN (erase_expr e1) (erase_expr e2)
  | Load e => Load (erase_expr e)
  | Store e1 e2 => Store (erase_expr e1) (erase_expr e2)
  | CmpXchg e0 e1 e2 => CmpXchg (erase_expr e0) (erase_expr e1) (erase_expr e2)
  | FAA e1 e2 => FAA (erase_expr e1) (erase_expr e2)
  | NewProph => erased_new_proph
  | Resolve e0 e1 e2 =>
    erase_resolve (erase_expr e0) (erase_expr e1) (erase_expr e2)
  end
with
erase_val (v : val) : val :=
  match v with
  | LitV l => LitV (erase_base_lit l)
  | RecV f x e => RecV f x (erase_expr e)
  | PairV v1 v2 => PairV (erase_val v1) (erase_val v2)
  | InjLV v => InjLV (erase_val v)
  | InjRV v => InjRV (erase_val v)
  end.

Lemma erase_expr_subst x v e :
  erase_expr (subst x v e) = subst x (erase_val v) (erase_expr e)
with
erase_val_subst x v (w : val) :
  erase_expr (subst x v w) = subst x (erase_val v) (erase_val w).
Proof.
  - destruct e; simpl; try case_decide;
      rewrite ?erase_expr_subst ?erase_val_subst; auto.
  - by destruct v.
Qed.

Lemma erase_expr_subst' x v e :
  erase_expr (subst' x v e) = subst' x (erase_val v) (erase_expr e).
Proof. destruct x; eauto using erase_expr_subst. Qed.
Lemma erase_val_subst' x v (w : val) :
  erase_expr (subst x v w) = subst x (erase_val v) (erase_val w).
Proof. destruct x; eauto using erase_val_subst. Qed.

Fixpoint erase_ectx_item (Ki : ectx_item) : list ectx_item :=
  match Ki with
  | AppLCtx v2 => [AppLCtx (erase_val v2)]
  | AppRCtx e1 => [AppRCtx (erase_expr e1)]
  | UnOpCtx op => [UnOpCtx op]
  | BinOpLCtx op v2 => [BinOpLCtx op (erase_val v2)]
  | BinOpRCtx op e1 => [BinOpRCtx op (erase_expr e1)]
  | IfCtx e1 e2 => [IfCtx (erase_expr e1) (erase_expr e2)]
  | PairLCtx v2 => [PairLCtx (erase_val v2)]
  | PairRCtx e1 => [PairRCtx (erase_expr e1)]
  | FstCtx => [FstCtx]
  | SndCtx => [SndCtx]
  | InjLCtx => [InjLCtx]
  | InjRCtx => [InjRCtx]
  | CaseCtx e1 e2 => [CaseCtx (erase_expr e1) (erase_expr e2)]
  | AllocNLCtx v2 => [AllocNLCtx (erase_val v2)]
  | AllocNRCtx e1 => [AllocNRCtx (erase_expr e1)]
  | LoadCtx => [LoadCtx]
  | StoreLCtx v2 => [StoreLCtx (erase_val v2)]
  | StoreRCtx e1 => [StoreRCtx (erase_expr e1)]
  | CmpXchgLCtx v1 v2 => [CmpXchgLCtx (erase_val v1) (erase_val v2)]
  | CmpXchgMCtx e0 v2 => [CmpXchgMCtx (erase_expr e0) (erase_val v2)]
  | CmpXchgRCtx e0 e1 => [CmpXchgRCtx (erase_expr e0) (erase_expr e1)]
  | FaaLCtx v2 => [FaaLCtx (erase_val v2)]
  | FaaRCtx e1 => [FaaRCtx (erase_expr e1)]
  | ResolveLCtx ctx v1 v2 =>
    erase_ectx_item ctx ++
    [PairLCtx (erase_val v1); PairLCtx (erase_val v2); FstCtx; FstCtx]
  | ResolveMCtx e0 v2 =>
    [PairRCtx (erase_expr e0); PairLCtx (erase_val v2); FstCtx; FstCtx]
  | ResolveRCtx e0 e1 =>
    [PairRCtx (erase_expr e0, erase_expr e1); FstCtx; FstCtx]
  end.

Definition erase_ectx (K : ectx heap_ectx_lang) : ectx heap_ectx_lang :=
  mbind erase_ectx_item K.

Definition erase_tp (tp : list expr) : list expr := erase_expr <$> tp.

Definition erase_heap (h : gmap loc val) : gmap loc val := erase_val <$> h.

Definition erase_state (σ : state) : state :=
  {| heap := erase_heap (heap σ); used_proph_id := ∅ |}.

Definition erase_cfg (ρ : cfg heap_lang) : cfg heap_lang :=
  (erase_tp ρ.1, erase_state ρ.2).

Lemma erase_to_val e v :
  to_val (erase_expr e) = Some v → ∃ v', to_val e = Some v' ∧ erase_val v' = v.
Proof. destruct e; naive_solver. Qed.

Lemma erase_not_val e : to_val e = None → to_val (erase_expr e) = None.
Proof. by destruct e. Qed.

Lemma erase_ectx_app K K' : erase_ectx (K ++ K') = erase_ectx K ++ erase_ectx K'.
Proof. by rewrite /erase_ectx bind_app. Qed.

Lemma erase_ectx_expr K e :
  erase_expr (fill K e) = fill (erase_ectx K) (erase_expr e).
Proof.
  revert e.
  induction K as [|Ki K IHK] using rev_ind; simplify_eq/=; first done.
  intros e.
  rewrite !erase_ectx_app !fill_app /= -IHK {IHK}.
  induction Ki; rewrite /= ?fill_app /= /erase_resolve; eauto with f_equal.
Qed.

Lemma val_is_unboxed_erased v :
  val_is_unboxed (erase_val v) ↔ val_is_unboxed v.
Proof.
  destruct v; rewrite /= /lit_is_unboxed; repeat (done || simpl; case_match).
Qed.
Lemma vals_compare_safe_erase v1 v2 :
  vals_compare_safe (erase_val v1) (erase_val v2) ↔
  vals_compare_safe v1 v2.
Proof. rewrite /vals_compare_safe !val_is_unboxed_erased. done. Qed.
Lemma erase_val_inj_iff v1 v2 :
  vals_compare_safe v1 v2 → erase_val v1 = erase_val v2 ↔ v1 = v2.
Proof.
  destruct v1, v2; rewrite /= /lit_is_unboxed;
    repeat (done || (by intros [[] | []]) || simpl; case_match).
Qed.

(** if [un_op_eval] succeeds on erased value,
    the so should it on the original value. *)
Lemma un_op_eval_erase op v v' :
  un_op_eval op (erase_val v) = Some v' ↔
  ∃ w, un_op_eval op v = Some w ∧ erase_val w = v'.
Proof.
  destruct op; simpl; repeat case_match; naive_solver.
Qed.

(** if [bin_op_eval] succeeds on erased value,
    then so should it on the original value. *)
Lemma bin_op_eval_erase op v1 v2 v' :
  bin_op_eval op (erase_val v1) (erase_val v2) = Some v' ↔
  ∃ w, bin_op_eval op v1 v2 = Some w ∧ erase_val w = v'.
Proof.
  rewrite /bin_op_eval /bin_op_eval_int /bin_op_eval_bool;
    split; [intros ?|intros (?&?&?)];
      repeat (case_match; simplify_eq/=); eauto.
  - eexists _; split; eauto; simpl.
    erewrite bool_decide_iff; first by eauto.
    rewrite erase_val_inj_iff; done.
  - by assert (vals_compare_safe v1 v2) by by apply vals_compare_safe_erase.
  - by erewrite bool_decide_iff; last apply erase_val_inj_iff.
  - by assert (vals_compare_safe (erase_val v1) (erase_val v2))
      by by apply vals_compare_safe_erase.
Qed.

Lemma lookup_erase_heap_None h l : erase_heap h !! l = None ↔ h !! l = None.
Proof. rewrite lookup_fmap; by destruct (h !! l). Qed.

Lemma lookup_erase_heap h l : erase_heap h !! l = erase_val <$> h !! l.
Proof. by rewrite lookup_fmap. Qed.

Lemma erase_heap_insert h l v :
  erase_heap (<[l := v]> h) = <[l := erase_val v]> (erase_heap h).
Proof.
  by rewrite /erase_heap fmap_insert.
Qed.

Lemma fmap_heap_array f l vs :
  f <$> heap_array l vs = heap_array l (f <$> vs).
Proof.
  revert l; induction vs as [|v vs IHvs]; intros l;
    first by rewrite /= fmap_empty.
  by rewrite /= -!insert_union_singleton_l !fmap_insert IHvs.
Qed.

Lemma erase_heap_array l i v h :
  erase_heap (heap_array l (replicate i v) ∪ h) =
  heap_array l (replicate i (erase_val v)) ∪ erase_heap h.
Proof.
  apply map_eq => l'.
  rewrite /erase_heap lookup_fmap !lookup_union -fmap_replicate
  - fmap_heap_array !lookup_fmap.
    by destruct (heap_array l (replicate i v) !! l'); destruct (h !! l').
Qed.

Lemma erase_state_init l n v σ:
  erase_state (state_init_heap l n v σ) =
  state_init_heap l n (erase_val v) (erase_state σ).
Proof. by rewrite /erase_state /state_init_heap /= erase_heap_array. Qed.

Definition head_steps_to_erasure_of (e1 : expr) (σ1 : state) (e2 : expr)
           (σ2 : state) (efs : list expr) :=
  ∃ κ' e2' σ2' efs',
    head_step e1 σ1 κ' e2' σ2' efs' ∧
    erase_expr e2' = e2 ∧ erase_state σ2' = σ2 ∧ erase_tp efs' = efs.

Lemma erased_head_step_head_step_rec f x e v σ :
  head_steps_to_erasure_of ((rec: f x := e)%V v) σ
    (subst' x (erase_val v)
            (subst' f (rec: f x := erase_expr e) (erase_expr e)))
    (erase_state σ) [].
Proof. by repeat econstructor; rewrite !erase_expr_subst'. Qed.
Lemma erased_head_step_head_step_NewProph σ :
  head_steps_to_erasure_of NewProph σ #LitPoison (erase_state σ) [].
Proof. eexists _, _, _, _; split; first eapply new_proph_id_fresh; done. Qed.
Lemma erased_head_step_head_step_AllocN n v σ l :
  0 < n →
  (∀ i : Z, 0 ≤ i → i < n → erase_heap (heap σ) !! (l +ₗ i) = None) →
  head_steps_to_erasure_of
    (AllocN #n v) σ #l (state_init_heap l n (erase_val v) (erase_state σ)) [].
Proof.
  eexists _, _, _, _; simpl; split;
    first econstructor; try setoid_rewrite <- lookup_erase_heap_None;
      rewrite ?erase_heap_insert /=; eauto using erase_state_init.
Qed.
Lemma erased_head_step_head_step_Load l σ v :
  erase_heap (heap σ) !! l = Some v →
  head_steps_to_erasure_of (! #l) σ v (erase_state σ) [].
Proof.
  intros Hl.
  rewrite lookup_erase_heap in Hl.
  destruct (heap σ !! l) eqn:?; simplify_eq/=.
  eexists _, _, _, _; simpl; split; first econstructor; eauto.
Qed.

Lemma erased_head_step_head_step_Store l v σ :
  is_Some (erase_heap (heap σ) !! l) →
  head_steps_to_erasure_of (#l <- v) σ #()
   {| heap := <[l:=erase_val v]> (erase_heap (heap σ)); used_proph_id := ∅ |} [].
Proof.
  intros Hl.
  rewrite lookup_erase_heap in Hl.
  destruct (heap σ !! l) eqn:?; simplify_eq/=;
           last by apply is_Some_None in Hl.
  eexists _, _, _, _; simpl; split; first econstructor; repeat split; eauto.
    by rewrite /state_upd_heap /erase_state /= erase_heap_insert.
Qed.
Lemma erased_head_step_head_step_CmpXchg l v w σ vl :
  erase_heap (heap σ) !! l = Some vl →
  vals_compare_safe vl (erase_val v) →
  head_steps_to_erasure_of
    (CmpXchg #l v w) σ
    (vl, #(bool_decide (vl = erase_val v)))%V
    (if bool_decide (vl = erase_val v)
     then {| heap := <[l:=erase_val w]> (erase_heap (heap σ));
             used_proph_id := ∅ |}
     else erase_state σ) [].
Proof.
  intros Hl Hvl.
  rewrite lookup_erase_heap in Hl.
  destruct (heap σ !! l) as [u|] eqn:?; simplify_eq/=.
  rewrite -> vals_compare_safe_erase in Hvl.
  destruct (decide (u = v)) as [->|Hneq].
  - eexists _, _, _, _; simpl; split.
    { econstructor; eauto. }
    rewrite !bool_decide_eq_true_2; eauto using erase_val_inj_iff; [].
    rewrite -?erase_heap_insert.
    split_and!; auto.
  - eexists _, _, _, _; simpl; split.
    { econstructor; eauto. }
    rewrite !bool_decide_eq_false_2; eauto; [].
    by rewrite erase_val_inj_iff.
Qed.
Lemma erased_head_step_head_step_FAA l n m σ :
  erase_heap (heap σ) !! l = Some #n →
  head_steps_to_erasure_of
    (FAA #l #m) σ #n
    {| heap := <[l:= #(n + m)]> (erase_heap (heap σ));
       used_proph_id := ∅ |} [].
Proof.
  intros Hl.
  rewrite lookup_erase_heap in Hl.
  destruct (heap σ !! l) as [[[]| | | |]|] eqn:?; simplify_eq/=.
  repeat econstructor; first by eauto.
  by rewrite /state_upd_heap /erase_state /= erase_heap_insert.
Qed.

(** When the erased program makes a head step, so does the original program. *)
Lemma erased_head_step_head_step e1 σ1 κ e2 σ2 efs:
  head_step (erase_expr e1) (erase_state σ1) κ e2 σ2 efs →
  head_steps_to_erasure_of e1 σ1 e2 σ2 efs.
Proof.
  intros Hhstep.
  inversion Hhstep; simplify_eq/=;
    repeat match goal with
           | H : _ = erase_expr ?e |- _ => destruct e; simplify_eq/=
           | H : _ = erase_val ?v |- _ => destruct v; simplify_eq/=
           | H : _ = erase_base_lit ?l |- _ => destruct l; simplify_eq/=
           | H : context [erased_new_proph] |- _ => unfold erased_new_proph in H
           | H : un_op_eval _ (erase_val _) = Some _ |- _ =>
             apply un_op_eval_erase in H as [? [? ?]]
           | H : bin_op_eval _ (erase_val _) (erase_val _) = Some _ |- _ =>
             apply bin_op_eval_erase in H as [? [? ?]]
           end; simplify_eq/=;
    try (by repeat econstructor);
  eauto using erased_head_step_head_step_rec,
    erased_head_step_head_step_NewProph,
    erased_head_step_head_step_AllocN,
    erased_head_step_head_step_Load,
    erased_head_step_head_step_Store,
    erased_head_step_head_step_CmpXchg,
    erased_head_step_head_step_FAA.
Qed.

Lemma fill_to_resolve e v1 v2 K e' :
  to_val e' = None →
  Resolve e v1 v2 = fill K e' →
  K = [] ∨ ∃ K' Ki, K = K' ++ [ResolveLCtx Ki v1 v2].
Proof.
  intros Hnv Hrs; simpl in *.
  assert (∀ v K, fill K e' ≠ v) as Hcontr.
  { intros w K' Hw.
    assert (to_val (of_val w) = to_val (fill K' e')) as He'
        by (by rewrite Hw).
    rewrite fill_not_val in He'; by eauto. }
  destruct K as [|Ki K _] using rev_ind; first by left.
  rewrite fill_app in Hrs.
  destruct Ki; simplify_eq/=; eauto;
    try exfalso; eapply Hcontr; eauto.
Qed.

Lemma projs_pure_steps (v0 v1 v2 : val) :
  rtc pure_step (Fst (Fst (v0, v1, v2))) v0.
Proof.
  etrans; first apply (rtc_pure_step_ctx (fill [PairLCtx _; FstCtx; FstCtx])).
  { apply rtc_once.
    apply pure_head_step_pure_step.
    split; first repeat econstructor.
    intros ????? Hhstep; inversion Hhstep; simplify_eq/=; eauto. }
  simpl.
  etrans; first apply (rtc_pure_step_ctx (fill [FstCtx; FstCtx])).
  { apply rtc_once.
    apply pure_head_step_pure_step.
    split; first repeat econstructor.
    intros ????? Hhstep; inversion Hhstep; simplify_eq/=; eauto. }
  simpl.
  etrans; first apply (rtc_pure_step_ctx (fill [FstCtx])).
  { apply rtc_once.
    apply pure_head_step_pure_step.
    split; first repeat econstructor.
    intros ????? Hhstep; inversion Hhstep; simplify_eq/=; eauto. }
  simpl.
  apply rtc_once.
  apply pure_head_step_pure_step.
  split; first repeat econstructor.
  intros ????? Hhstep; inversion Hhstep; simplify_eq/=; eauto.
Qed.

Lemma Resolve_3_vals_head_stuck v0 v1 v2 σ κ e σ' efs :
  ¬ head_step (Resolve v0 v1 v2) σ κ e σ' efs.
Proof.
  intros Hhstep.
  inversion Hhstep; simplify_eq/=.
  apply (eq_None_not_Some (to_val (Val v0))); last eauto.
  by eapply val_head_stuck.
Qed.

Lemma Resolve_3_vals_unsafe (v0 v1 v2 : val) σ :
  ¬ not_stuck (Resolve v0 v1 v2) σ.
Proof.
  assert(∀ w K e, Val w = fill K e → is_Some (to_val e)) as Hvfill.
  { intros ? K ? Heq; eapply (fill_val K); rewrite /= -Heq; eauto. }
  apply not_not_stuck.
  split; first done.
  intros ???? [K e1' e2' Hrs Hhstep]; simplify_eq/=.
  destruct K as [|Ki K _] using rev_ind.
  { simplify_eq/=.
    eapply Resolve_3_vals_head_stuck; eauto. }
  rewrite fill_app in Hrs.
  destruct Ki; simplify_eq/=.
  - pose proof (fill_item_val Ki (fill K e1')) as Hnv.
    apply fill_val in Hnv as [? Hnv]; last by rewrite -Hrs; eauto.
    by erewrite val_head_stuck in Hnv.
  - edestruct Hvfill as [? Heq]; eauto.
    by erewrite val_head_stuck in Heq.
  - edestruct Hvfill as [? Heq]; eauto.
    by erewrite val_head_stuck in Heq.
Qed.

(** [(e1, σ1)] takes a [prim_step] to [(e2', σ2')] forking threads [efs']
 such that [σ2] is the erasure of [σ2'] and [efs] is the erasure of
 [efs']. Furthermore, [e2] takes [pure_steps] to match up with [e2].  It is
 crucial for us that [e2] takes [pure_step]s because we need to know
 that [e2] does not get stuck and that the steps are deterministic.

 Essentially, the main part of the erasure proof's argument is that if
 the erased program takes steps, then the original program also takes
 matching steps. This however, does not entirely hold. In cases where
 the erasure of [Resovle] takes a step, the original program
 immediately produces the value while the erased program has to still
 perform projections [Fst] to get the result (see the [Resolve] case
 of [erase_expr]). For this purpose, we prove that in those cases (and
 also in general) the erased program also takes a number of (possibly
 zero) steps so that the original and the erased programs are matched
 up again. *)
Definition prim_step_matched_by_erased_steps e1 σ1 e2 σ2 efs :=
  ∃ e2' σ2' κ' efs' e2'',
    prim_step e1 σ1 κ' e2' σ2' efs' ∧ rtc pure_step e2 e2'' ∧
    erase_expr e2' = e2'' ∧ erase_state σ2' = σ2 ∧ erase_tp efs' = efs.

Lemma prim_step_matched_by_erased_steps_ectx K e1 σ1 e2 σ2 efs :
  prim_step_matched_by_erased_steps e1 σ1 e2 σ2 efs →
  prim_step_matched_by_erased_steps (fill K e1) σ1 (fill (erase_ectx K) e2) σ2 efs.
Proof.
  intros (?&?&?&?&?&?&?&?&?&?); simplify_eq/=.
  eexists _, _, _, _, _; repeat split.
  - by apply fill_prim_step.
  - rewrite erase_ectx_expr.
    by eapply (rtc_pure_step_ctx (fill (erase_ectx K))).
Qed.

Definition is_Resolve (e : expr) :=
  match e with Resolve _ _ _ => True | _ => False end.

Global Instance is_Resolve_dec e : Decision (is_Resolve e).
Proof. destruct e; solve_decision. Qed.

Lemma non_resolve_prim_step_matched_by_erased_steps_ectx_item
      Ki e1 e1' σ1 e2 σ2 efs :
  to_val e1' = None →
  ¬ is_Resolve e1 →
  not_stuck e1 σ1 →
  erase_expr e1 = fill_item Ki e1' →
  (∀ e1, erase_expr e1 = e1' → not_stuck e1 σ1 →
         prim_step_matched_by_erased_steps e1 σ1 e2 σ2 efs) →
  prim_step_matched_by_erased_steps e1 σ1 (fill_item Ki e2) σ2 efs.
Proof.
  intros Hnv Hnr Hsf He1 IH.
  destruct Ki; simplify_eq/=;
    repeat
      match goal with
      | H : erase_expr ?e = _ |- _ => destruct e; simplify_eq/=; try done
      | H : context [erased_new_proph] |- _ =>
        rewrite /erased_new_proph in H; simplify_eq/=
      | |- prim_step_matched_by_erased_steps ?e _ _ _ _ =>
        let tac K e :=
            lazymatch K with
            | [] => fail
            | _ => apply (prim_step_matched_by_erased_steps_ectx K);
                    apply IH; [done| by eapply (not_stuck_under_ectx (fill K))]
            end
        in
        reshape_expr e tac
      end.
Qed.

Lemma prim_step_matched_by_erased_steps_ectx_item Ki K e1 e1' σ1 e2 σ2 efs κ :
  head_step e1' (erase_state σ1) κ e2 σ2 efs →
  not_stuck e1 σ1 →
  erase_expr e1 = fill_item Ki (fill K e1') →
  (∀ K' e1, length K' ≤ length K →
     erase_expr e1 = (fill K' e1') → not_stuck e1 σ1 →
     prim_step_matched_by_erased_steps e1 σ1 (fill K' e2) σ2 efs) →
  prim_step_matched_by_erased_steps e1 σ1 (fill_item Ki (fill K e2)) σ2 efs.
Proof.
  intros Hhstp Hsf He1 IH; simpl in *.
  (** Case split on whether e1 is a [Resolve] expression. *)
  destruct (decide (is_Resolve e1)); last first.
  { (** e1 is not a [Resolve] expression. *)
    eapply non_resolve_prim_step_matched_by_erased_steps_ectx_item; eauto; [|].
    - by eapply fill_not_val, val_head_stuck.
    - intros; eapply (IH K); simpl; eauto with lia. }
  (** e1 is a [Resolve] expression. *)
  destruct Ki; simplify_eq/=;
    repeat
      match goal with
      | H : erase_expr ?e = ?e' |- _ =>
        progress
          match e' with
          | fill _ _ => idtac
          | _ => destruct e; simplify_eq/=
          end
      end; try done.
  destruct K as [|Ki K _] using rev_ind; simplify_eq/=; [|].
  { (* case where (Fst (erase_expr e1_1, erase_expr e1_2, erase_expr e1_3)) *)
    (*      takes a head_step; it is impossible! *)
    by inversion Hhstp; simplify_eq. }
  rewrite /erase_resolve fill_app /= in He1; simplify_eq/=.
  destruct Ki; simplify_eq/=; rewrite fill_app /=.
  destruct K as [|Ki K _] using rev_ind; simplify_eq/=; [|].
  { (* case where (erase_expr e1_1, erase_expr e1_2, erase_expr e1_3) *)
    (*      takes a head_step; it is impossible! *)
    inversion Hhstp. }
  rewrite fill_app /= in He1.
  destruct Ki; simplify_eq/=; rewrite fill_app /=.
  - destruct K as [|Ki K _] using rev_ind; simplify_eq/=; [|].
    { (** [Resolve v0 v1 v2] is not safe! *)
      inversion Hhstp; simplify_eq/=.
      repeat
        match goal with
        | H : erase_expr ?e = _ |- _ => destruct e; simplify_eq/=
        | H : _ = erase_expr ?e |- _ => destruct e; simplify_eq/=
        end.
      by exfalso; eapply Resolve_3_vals_unsafe. }
    rewrite fill_app /= in He1.
    destruct Ki; simplify_eq/=; rewrite fill_app /=.
    + (** e1 is of the form ([Resolve] e10 e11 v0) and e11 takes a prim_step. *)
      destruct Hsf as [[? ?]| (?&?&?&?&Hrpstp)]; first done; simpl in *.
      inversion Hrpstp as [??? Hrs ? Hhstp']; simplify_eq/=.
      repeat
        match goal with
        | H : erase_expr ?e = ?e' |- _ =>
          progress
            match e' with
            | fill _ _ => idtac
            | _ => destruct e; simplify_eq/=
            end
        end.
      edestruct fill_to_resolve as [?|[K' [Ki HK]]]; eauto;
        [by eapply val_head_stuck| |]; simplify_eq/=.
      * (** e1 is of the form ([Resolve] e10 e11 v0) and e11 takes a head_step. *)
        inversion Hhstp'; simplify_eq.
        edestruct (IH K) as (?&?&?&?&?&Hpstp&?&?&?&?);
          [rewrite !app_length /=; lia|done|by eapply head_step_not_stuck|];
            simplify_eq/=.
        apply head_reducible_prim_step in Hpstp; simpl in *;
          last by rewrite /head_reducible /=; eauto 10.
        epose (λ H, head_step_to_val _ _ _ (Val _) _ _ _ _ _ _ _ H Hpstp)
          as Hhstv; edestruct Hhstv as [? ?%of_to_val]; [done|eauto|];
          simplify_eq.
        eexists _, _, _, _, _; repeat split;
          first (by apply head_prim_step; econstructor; eauto); auto.
        etrans.
        { by apply (rtc_pure_step_ctx
                      (fill [PairLCtx _; PairLCtx _; FstCtx; FstCtx])). }
        apply projs_pure_steps.
      * (** e1 is of the form ([Resolve] e10 v v0) and e10 takes a
           (non-head) prim_step. *)
        rewrite fill_app in Hrs; simplify_eq/=.
        edestruct (IH K) as (?&?&?&?&?&Hpstp&Hprstps&?&?&?);
          [rewrite !app_length; lia|done| |].
        { change (fill_item Ki) with (fill [Ki]).
          by rewrite -fill_app; eapply prim_step_not_stuck, Ectx_step. }
        simplify_eq/=.
        change (fill_item Ki) with (fill [Ki]) in Hpstp.
        rewrite -fill_app in Hpstp.
        eapply head_reducible_prim_step_ctx in Hpstp as [e2'' [He2'' Hpstp]];
          last by eexists _; eauto.
        simplify_eq/=.
        eexists _, _, _, _, _; repeat split.
        -- apply (fill_prim_step [ResolveLCtx _ _ _]); eapply Ectx_step; eauto.
        -- simpl; rewrite fill_app in Hprstps.
           by apply (rtc_pure_step_ctx
                    (fill [PairLCtx _; PairLCtx _; FstCtx; FstCtx])).
    + (** e1 is of the form ([Resolve] e1_ e1_2 v) and e1_2 takes a prim_step. *)
      repeat
        match goal with
        | H : erase_expr ?e = ?e' |- _ =>
          progress
            match e' with
            | fill _ _ => idtac
            | _ => destruct e; simplify_eq/=
            end
        end.
      apply (prim_step_matched_by_erased_steps_ectx [ResolveMCtx _ _]).
      apply IH; [rewrite !app_length /=; lia|done|
                 by eapply (not_stuck_under_ectx (fill [ResolveMCtx _ _])); simpl].
  - (** e1 is of the form ([Resolve] e1_ e1_2 e13) and e1_3 takes a prim_step. *)
    apply (prim_step_matched_by_erased_steps_ectx [ResolveRCtx _ _]).
    apply IH; [rewrite !app_length /=; lia|done|
                 by eapply (not_stuck_under_ectx (fill [ResolveRCtx _ _])); simpl].
Qed.

Lemma erased_prim_step_prim_step e1 σ1 κ e2 σ2 efs:
  prim_step (erase_expr e1) (erase_state σ1) κ e2 σ2 efs → not_stuck e1 σ1 →
  prim_step_matched_by_erased_steps e1 σ1 e2 σ2 efs.
Proof.
  intros Hstp He1sf.
  inversion Hstp as [K e1' e2' He1 ? Hhstp]; clear Hstp; simplify_eq/=.
  set (len := length K); assert (length K = len) as Hlen by done; clearbody len.
  revert K Hlen e1 He1 He1sf.
  induction len as [m IHm]using lt_wf_ind; intros K Hlen e1 He1 He1sf;
    simplify_eq.
  destruct K as [|Ki K _] using rev_ind; simplify_eq/=.
  { apply erased_head_step_head_step in Hhstp as (?&?&?&?&?&<-&?&<-).
    eexists _, _, _, _, _; repeat split;
      first (by apply head_prim_step); auto using rtc_refl. }
  rewrite app_length in IHm; simpl in *.
  rewrite fill_app /=; rewrite fill_app /= in He1.
  eapply prim_step_matched_by_erased_steps_ectx_item; eauto; [].
  { intros; simpl in *; apply (IHm (length K')); auto with lia. }
Qed.

Lemma head_step_erased_prim_step_CmpXchg v1 v2 σ l vl:
  heap σ !! l = Some vl →
  vals_compare_safe vl v1 →
  ∃ e2' σ2' ef', prim_step (CmpXchg #l (erase_val v1)
                             (erase_val v2)) (erase_state σ) [] e2' σ2' ef'.
Proof.
  intros Hl Hv.
  destruct (bool_decide (vl = v1)) eqn:Heqvls.
  - do 3 eexists; apply head_prim_step;
      econstructor; [|by apply vals_compare_safe_erase|by eauto].
      by rewrite /erase_state /state_upd_heap /= lookup_erase_heap Hl.
  - do 3 eexists; apply head_prim_step;
        econstructor; [|by apply vals_compare_safe_erase|by eauto].
      by rewrite /erase_state /state_upd_heap /= lookup_erase_heap Hl.
Qed.

Lemma head_step_erased_prim_step_resolve e w σ :
  (∃ e2' σ2' ef', prim_step (erase_expr e) (erase_state σ) [] e2' σ2' ef') →
  ∃ e2' σ2' ef',
    prim_step (erase_resolve (erase_expr e) #LitPoison (erase_val w))
              (erase_state σ) [] e2' σ2' ef'.
Proof.
  intros (?&?&?&?).
  by eexists _, _, _;
    apply (fill_prim_step [PairLCtx _; PairLCtx _;FstCtx; FstCtx]).
Qed.

Lemma head_step_erased_prim_step_un_op σ op v v':
  un_op_eval op v = Some v' →
  ∃ e2' σ2' ef', prim_step (UnOp op (erase_val v)) (erase_state σ) [] e2' σ2' ef'.
Proof.
  do 3 eexists; apply head_prim_step; econstructor.
  apply un_op_eval_erase; eauto.
Qed.

Lemma head_step_erased_prim_step_bin_op σ op v1 v2 v':
  bin_op_eval op v1 v2 = Some v' →
  ∃ e2' σ2' ef', prim_step (BinOp op (erase_val v1) (erase_val v2))
                           (erase_state σ) [] e2' σ2' ef'.
Proof.
  do 3 eexists; apply head_prim_step; econstructor.
  apply bin_op_eval_erase; eauto.
Qed.

Lemma head_step_erased_prim_step_allocN σ l n v:
  0 < n → (∀ i : Z, 0 ≤ i → i < n → heap σ !! (l +ₗ i) = None) →
  ∃ e2' σ2' ef',
    prim_step (AllocN #n (erase_val v)) (erase_state σ) [] e2' σ2' ef'.
Proof.
  do 3 eexists; apply head_prim_step; econstructor; eauto.
  intros; rewrite lookup_erase_heap_None; eauto.
Qed.

Lemma head_step_erased_prim_step_load σ l v:
  heap σ !! l = Some v →
  ∃ e2' σ2' ef', prim_step (! #l) (erase_state σ) [] e2' σ2' ef'.
Proof.
  do 3 eexists; apply head_prim_step; econstructor.
  rewrite /erase_state /state_upd_heap /= lookup_erase_heap.
  by destruct lookup; simplify_eq.
Qed.

Lemma head_step_erased_prim_step_store σ l v:
  is_Some (heap σ !! l) →
  ∃ e2' σ2' ef', prim_step (#l <- erase_val v) (erase_state σ) [] e2' σ2' ef'.
Proof.
  intros [w Hw].
  do 3 eexists; apply head_prim_step; econstructor.
  rewrite /erase_state /state_upd_heap /= lookup_erase_heap Hw; eauto.
Qed.

Lemma head_step_erased_prim_step_FAA σ l n n':
  heap σ !! l = Some #n →
  ∃ e2' σ2' ef', prim_step (FAA #l #n') (erase_state σ) [] e2' σ2' ef'.
Proof.
  intros Hl.
  do 3 eexists; apply head_prim_step. econstructor.
  by rewrite /erase_state /state_upd_heap /= lookup_erase_heap Hl.
Qed.

(**
[Resolve] is translated as a projection out of a triple.
Therefore, when resolve takes a head step, the erasure of [Resolve] takes a
prim step inside the triple.
*)
Lemma head_step_erased_prim_step e1 σ1 κ e2 σ2 ef:
  head_step e1 σ1 κ e2 σ2 ef →
  ∃ e2' σ2' ef', prim_step (erase_expr e1) (erase_state σ1) [] e2' σ2' ef'.
Proof.
  induction 1; simplify_eq/=;
    eauto using head_step_erased_prim_step_CmpXchg,
                head_step_erased_prim_step_resolve,
                head_step_erased_prim_step_un_op,
                head_step_erased_prim_step_bin_op,
                head_step_erased_prim_step_allocN,
                head_step_erased_prim_step_load,
                head_step_erased_prim_step_store,
                head_step_erased_prim_step_FAA;
    by do 3 eexists; apply head_prim_step; econstructor.
Qed.

Lemma reducible_erased_reducible e σ :
  reducible e σ → reducible (erase_expr e) (erase_state σ).
Proof.
  intros (?&?&?&?&Hpstp); simpl in *.
  inversion Hpstp; simplify_eq/=.
  rewrite erase_ectx_expr.
  edestruct head_step_erased_prim_step as (?&?&?&?); first done; simpl in *.
  eexists _, _, _, _; eapply fill_prim_step; eauto.
Qed.

Lemma pure_step_tp_safe t1 t2 e1 σ :
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ) → pure_steps_tp t1 (erase_tp t2) →
  e1 ∈ t1 → not_stuck e1 (erase_state σ).
Proof.
  intros Ht2 Hpr [i He1]%elem_of_list_lookup_1.
  eapply Forall2_lookup_l in Hpr as [e2' [He2' Hpr]]; simpl in *; eauto.
  rewrite /erase_tp list_lookup_fmap in He2'.
  destruct (t2 !! i) eqn:He2; simplify_eq/=.
  apply elem_of_list_lookup_2, Ht2 in He2.
  clear -Hpr He2.
  inversion Hpr as [|??? [? _]]; simplify_eq.
  - destruct He2 as [[? ?%of_to_val]|]; simplify_eq/=; first by left; eauto.
    by right; apply reducible_erased_reducible.
  - right; eauto using reducible_no_obs_reducible.
Qed.

(** This is the top-level erasure theorem: erasure preserves adequacy. *)
Theorem erasure e σ φ :
  adequate NotStuck e σ φ →
  adequate NotStuck (erase_expr e) (erase_state σ)
           (λ v σ, ∃ v' σ', erase_val v' = v ∧ erase_state σ' = σ ∧ φ v' σ').
Proof.
  simpl; intros Hade; simpl in *.
  cut (∀ t2 σ2,
          rtc erased_step ([erase_expr e], erase_state σ) (t2, σ2) →
          (∃ t2' t2'' σ2',
              rtc erased_step ([e], σ) (t2'', σ2') ∧
              t2' = erase_tp t2'' ∧ σ2 = erase_state σ2' ∧
              pure_steps_tp t2 t2')).
  { intros Hreach; split; simpl in *.
    - intros ? ? ? Hrtc; edestruct (Hreach _ _ Hrtc) as
          (t2'&t2''&σ2'&Hos&Ht2'&Hσ2&Hptp); simplify_eq/=.
      apply Forall2_cons_inv_l in Hptp as (oe&t3&Hoe%rtc_pure_step_val&_&?);
        destruct t2''; simplify_eq/=.
      apply erase_to_val in Hoe as (?&?%of_to_val&?); simplify_eq.
      pose proof (adequate_result _ _ _ _ Hade _ _ _ Hos); eauto.
    - intros ? ? ? Hs Hrtc He2; edestruct (Hreach _ _ Hrtc) as
          (t2'&t2''&σ2'&Hos&Ht2'&Hσ2&Hptp); simplify_eq/=.
      eapply pure_step_tp_safe; [|done..].
      intros e2' He2'.
      apply (adequate_not_stuck _ _ _ _ Hade _ _ _ eq_refl Hos He2'). }
  intros t2 σ2 [n Hstps]%rtc_nsteps; simpl in *; revert t2 σ2 Hstps.
  induction n as [|n IHn].
  { intros t2 σ2 Hstps; inversion Hstps; simplify_eq /=.
    repeat econstructor. }
  intros t2 σ2 Hstps.
  apply nsteps_inv_r in Hstps as [[t3 σ3] [Hstps Hρ]]; simpl in *.
  destruct (IHn _ _ Hstps) as (t2'&t2''&σ2'&Hostps&?&?&Hprstps); simplify_eq.
  edestruct @erased_step_pure_step_tp as [[? Hint]|Hext]; simplify_eq/=;
    eauto 10; [|done..].
  destruct Hext as (i&ei&t2'&efs&e'&κ&Hi1&Ht2&Hpstp);
    simplify_eq/=.
  rewrite /erase_tp list_lookup_fmap in Hi1.
  destruct (t2'' !! i) as [eio|] eqn:Heq; simplify_eq/=.
  edestruct erased_prim_step_prim_step as
    (eio' & σ3 & κ' & efs' & ee & Heiopstp & Hprstps' & ?&?&?); first done;
    last simplify_eq/=.
  { eapply adequate_not_stuck; eauto using elem_of_list_lookup_2. }
  eexists _, _, _; repeat split.
  { etrans; first done.
    apply rtc_once; eexists.
    eapply step_insert; eauto. }
  rewrite /erase_tp fmap_app.
  rewrite list_fmap_insert/=.
  apply Forall2_app; last done.
  apply Forall2_same_length_lookup; split.
  { apply Forall2_length in Hprstps; rewrite fmap_length in Hprstps.
    by rewrite !insert_length fmap_length. }
  intros j x y.
  destruct (decide (i = j)); simplify_eq.
  { rewrite !list_lookup_insert ?fmap_length; eauto using lookup_lt_Some; [].
    by intros ? ?; simplify_eq. }
  rewrite !list_lookup_insert_ne // list_lookup_fmap.
  intros ? ?.
  eapply Forall2_lookup_lr; eauto.
  by rewrite /erase_tp list_lookup_fmap.
Qed.
