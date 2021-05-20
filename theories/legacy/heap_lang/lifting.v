From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap excl.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export proph_map.
From diris.program_logic Require Export weakestpre.
From diris.program_logic Require Import ectx_lifting.
From diris.heap_lang Require Export lang.
Set Default Proof Using "Type".

(* From diris.heap_lang Require Import notation. *)
(* From diris.heap_lang Require Import tactics. *)


(* From iris.proofmode Require Import tactics. *)
(* From diris.program_logic Require Export ectx_language weakestpre lifting. *)
(*

Class irisG (Λ : language) (Σ : gFunctors) (A : Type) := IrisG {
  iris_invG :> invG Σ;

  abstract_state : Type;

  (** The state interpretation is an invariant that should hold in between each
  step of reduction. Here [Λstate] is the global state, [list Λobservation] are
  the remaining observations, and [nat] is the number of forked-off threads
  (not the total number of threads, which is one higher because there is always
  a main thread). *)
  state_interp : abstract_state → state Λ → list (observation Λ) → list (expr Λ) → iProp Σ;

  (** The legal_state predicate holds of every state, even those that cannot step.
  e.g. stuck_valid s e σ :=
    ⌜if s is NotStuck then reducible e σ ∨ waiting e σ else True⌝   *)
  stuck_valid : abstract_state → state Λ → A → expr Λ → Prop;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : nat → val Λ → iProp Σ;

  tid_get : A → nat → Prop;
  tid_set : nat → A → A;
}.

Define:
1. l ↦ v for lock memory locations
2. Obs_i O for obligations
3. is_lock l R
4. locked l
5. state_interp
6. fork_post



Monoids:
M1 = auth (gmap loc (agree (nat * ▷iProp))       for the is_lock l R o
M2 = auth (gmap nat (excl (gset nat)))           for the Obs_i O
M3 = auth (gmap loc (excl bool))                 for the locked l

◯●

is_lock l R o := own γ1 (◯{l := to_agree (R,o)})
Obs i O       := own γ2 (◯{i := to_excl O})
locked l      := own γ3 (◯{l := to_excl true})


abstract_state := gmap loc (nat * iProp * bool) * (list (gset nat * option loc))


Definition state_interp (L,T) σ κs es :=
  ⌜ length es = length T ∧
    ∀ l o R b, L !! l = Some (o,R,true) → ∃ tid O ls, T !! tid = Some O ∧ l ∈ O ⌝ ∗
  own γ1 (●f12 L) * own γ2 (●f1 T) * own γ3 (●f3 L) *


Definition stuck_valid (L,T) σ (s,tid) e :=
  ∃ K l O,
    e = fill K (WAS l false true) ∧
    T !! tid = Some O ∧
    ∃ o R b, L !! l = Some (o,R,b) ∧ o < O.


Definition tid_get (s,i) j := i=j.
Definition tid_set (s,i) j := (s,j).

o < O := forall o', o' ∈ O -> o < o'

The final result that we want to get is that if there exist (L,T) such that
1. stuck_valid (L,T) σ (s,i) e holds for all threads i
2. state_interp (L,T) σ κs es holds for the machine state
Then either (a) all threads as values or (b) there is a thread that can take a step.

Deadlock freedom proof sketch:
==============================
We first check if all threads are values, if so, success.
We then look at the thread that are not values. If the lockstate of one of the threads is None, then it is reducible, so success.
If the lockstate of all the non-value threads is Some, we need to show that one of the locks is not locked, and therefore the WAS can step.
I claim that the WAS of the lock with lowest number can step. Suppose to the contrary that it cannot step, then thread i is waiting on some lock l with number o, with L !! l = Some(o,R,true) where the true means that the lock is indeed locked.
Then there is a thread i' with obs O' and lockstate ls' that has l in its obligations, so o ∈ O'.
By the previous assumption, ls' = Some l' with number o'. Then by stuck_valid of i', we have o' < O'. By the assumption that o was the lowest, o <= o'.
So we have simultaneously o < O' and o ∈ O. Contradiction.


R * (forall l, is_lock l R o -* Φ l)
------------------------------------
WP_i newlock () { Φ }


is_lock l R o * Obs_i O * o < O * (Obs_i (O + {o}) * R * locked l -* Φ ())
--------------------------------------------------------------------------
WP_i acquire l { Φ }


is_lock l R o * locked l * R * Obs_i O * (Obs_i (O - {o}) -* Φ ())
------------------------------------------------------------------
WP release l { Φ }


Obs_i (O + O') * (forall j, Obs_j O -* WP_j e { Obs_j empty }) * (Obs_i O' -* Φ ())
-----------------------------------------------------------------------------------
WP_i fork e { Φ }

*)

From iris.algebra Require Import auth gset gmap excl agree namespace_map.
From stdpp Require Export namespaces.
From iris.base_logic.lib Require Export own.


Class deadlockPreG Σ := DeadlockPreG {
  deadlock_locknum_inG :> inG Σ (authR (gmapUR loc (agreeR natO)));
  deadlock_obs_inG :> inG Σ (authR (gmapUR nat (exclR (gsetR natO))));
  deadlock_lockres_inG :> inG Σ (authR (gmapUR loc (agreeR (laterO (iPrePropO Σ)))));
  deadlock_locked_inG :> inG Σ (authR (gmapUR loc (exclR boolO)));
}.

Class deadlockG Σ := DeadlockG {
  deadlock_PreG :> deadlockPreG Σ;
  locknum_γ : gname;
  obs_γ : gname;
  lockres_γ : gname;
  locked_γ : gname
}.

Arguments locknum_γ {_} _ : assert.
Arguments obs_γ {_} _ : assert.
Arguments lockres_γ {_} _ : assert.
Arguments locked_γ {_} _ : assert.

Definition deadlockΣ : gFunctors :=
  #[GFunctor (authRF (gmapURF loc (agreeRF natO)));
    GFunctor (authRF (gmapURF nat (exclRF (gsetR natO))));
    GFunctor (authRF (gmapURF loc (agreeRF (laterOF idOF))));
    GFunctor (authRF (gmapURF loc (exclRF boolO)))].

Instance subG_deadlockΣ {Σ} : subG deadlockΣ Σ → deadlockPreG Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{dG : !deadlockG Σ}.

  Definition lock_mapsto (l:loc) (v:nat) : iProp Σ :=
    own (locknum_γ dG) (◯ {[ l := to_agree v ]}).

  Definition obs (i:nat) (O:gset nat) : iProp Σ :=
    own (obs_γ dG) (◯{[ i := Excl O ]}).

  Definition is_lock (l:loc) (R:iProp Σ) : iProp Σ :=
    own (lockres_γ dG) (◯ {[ l := to_agree (Next (iProp_unfold R)) ]}).

  Definition locked (l:loc) : iProp Σ :=
    own (locked_γ dG) (◯{[ l := Excl true ]}).

  Definition less_obs (o:nat) (O:gset nat) :=
    ∀ o', o' ∈ O -> o < o'.

  Definition f_locknum : gmap loc (iProp Σ * nat * bool) → gmap loc (agree nat) :=
    fmap (λ '(_,n,_),  to_agree n).
  Definition f_lockres : gmap loc (iProp Σ * nat * bool) → gmap loc (agree (later (iPrePropO Σ))) :=
    fmap (λ '(R,_,_),  to_agree (Next (iProp_unfold R))).
  Definition f_locked : gmap loc (iProp Σ * nat * bool) → gmap loc (excl bool) :=
    fmap (λ '(_,_,b),  Excl b).
  Definition f_obs : list (gset nat) → gmap nat (excl (gset nat)) :=
    λ l, fmap Excl (map_seq 0 l).

  Definition W (σ:state) (e:expr) (lo:option loc) : Prop :=
    match lo with
    | None => ¬ waiting e σ
    | Some l => ∃ K, e = fill K (WAS (Val (LitV (LitLoc l))) (Val (LitV (LitBool false)))
                                     (Val (LitV (LitBool true))))
    end.

  (* For each thread, if it's waiting on l, the locknum of l is less than its obs *)
  Definition deadlock_thread_inv
      (σ:state) (e:expr) (lockstate:option loc) (obs:gset nat)
      (L:gmap loc (iProp Σ * nat * bool)) :=
    match lockstate with
    | None => ¬ waiting e σ
    | Some l =>
      ∃ R n b, L !! l = Some (R,n,b) ∧ less_obs n obs ∧
      ∃ K, e = fill K (WAS (Val (LitV (LitLoc l)))
                           (Val (LitV (LitBool false)))
                           (Val (LitV (LitBool true))))
    end.



  (* TODO: add that each locked lock is in some thread's obs. *)
  Definition deadlock_inv (σ:state) (es:list expr)
      (T : list (gset nat * option loc)) (L:gmap loc (iProp Σ * nat * bool)) :=
    Forall2 (λ e '(obs,lockstate), deadlock_thread_inv σ e lockstate obs L) es T.

  Definition state_interp (σ : state) (es : list expr) : iProp Σ :=
    (∃ (L : gmap loc (iProp Σ * nat * bool)) (T : list (gset nat * option loc)),
      ⌜ deadlock_inv σ es T L ⌝ ∗
      own (locknum_γ dG) (● f_locknum L) ∗
      own (lockres_γ dG) (● f_lockres L) ∗
      own (locked_γ dG) (● f_locked L) ∗
      own (obs_γ dG) (● f_obs T))%I.

  Definition legally_waiting (t_id : nat) (e : expr) :=
    ∃ l O o R,
      ⌜ e = (WAS (Val (LitV (LitLoc l))) (Val (LitV (LitBool false)))
                                         (Val (LitV (LitBool true))) ⌝ *
      Obs t_id O * is_lock l R o * less_obs o O.

  Definition fork_post (t_id:nat) (v:val) : iProp Σ := obs t_id ∅.

  Lemma deadlock_inv_no_deadlock
    (σ:state) (es:list expr)
    (T: list (gset nat * option loc))
    (L:gmap loc (iProp Σ * nat * bool)) :
    deadlock_inv σ es T L → es ≠ [] → ∃ n e, es !! n = Some e ∧ ¬ waiting e σ.
  Proof.
    intros H Hemp. unfold deadlock_inv in H.
    destruct (decide (Exists (λ '(obs,lockstate), lockstate = None) T)).
    + apply Exists_exists in e as [[obs lockstate] [Hin e]]. subst.
      apply elem_of_list_lookup_1 in Hin as [i Hin].
      exists i.
      destruct (es !! i) eqn:E.
      - exists e. split; first done.
        by eapply Forall2_lookup_lr in H;[|done..].
      - apply Forall2_length in H.
        apply lookup_lt_Some in Hin.
        rewrite -H in Hin.
        eapply lookup_lt_is_Some_2 in Hin. destruct Hin as [? Hin].
        rewrite E in Hin. simplify_eq.
    + exfalso.
      rewrite<- Forall_Exists_neg in n.
  Admitted.

  (* TODO Jules: Add extra pre-state to WAS operational semantics *)

End definitions.

Class heapG Σ := HeapG {
  heapG_deadlockG :> deadlockG Σ;
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ;
  heapG_proph_mapG :> proph_mapG proph_id (val * val) Σ
}.
Instance heapG_irisG `{!heapG Σ} : irisG heap_ectx_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs es :=
    (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id) ∗ state_interp σ es)%I;
  fork_post := fork_post;
}.

Lemma Forall2_insert_l {A B} (P : A → B → Prop) (l : list A) (k : list B) (x : A) (i : nat) :
    Forall2 P l k → (∀ y, k !! i = Some y → P x y) → Forall2 P (<[i:=x]> l) k.
Proof.
  intros Hfa Hy.
  destruct (k !! i) as [b|] eqn:E.
  - replace k with (<[i:=b]> k).
    + eapply Forall2_insert; eauto.
    + by apply list_insert_id.
  - rewrite list_insert_ge; first done.
    apply Forall2_same_length_lookup in Hfa as [-> _].
    by apply lookup_ge_None_1.
Qed.

Lemma Forall2_insert_r {A B} (P : A → B → Prop) (l : list A) (k : list B) (x : B) (i : nat) :
    Forall2 P l k → (∀ y, l !! i = Some y → P y x) → Forall2 P l (<[i:=x]> k).
Proof.
  intros Hfa Hy.
  destruct (l !! i) as [b|] eqn:E.
  - replace l with (<[i:=b]> l).
    + eapply Forall2_insert; eauto.
    + by apply list_insert_id.
  - rewrite list_insert_ge; first done.
    apply Forall2_same_length_lookup in Hfa as [<- _].
    by apply lookup_ge_None_1.
Qed.

Lemma Forall2_replace_l {A B} (P : A → B → Prop) (l : list A) (k : list B) (x y : A) (i : nat) :
    (∀ z, P x z → P y z) → Forall2 P (<[i:=x]> l) k → Forall2 P (<[i:=y]> l) k.
Proof.
  intros Hy Hfa.
  apply Forall2_same_length_lookup in Hfa as [Hlen Hfa].
  apply Forall2_same_length_lookup.
  split. { rewrite insert_length. by rewrite insert_length in Hlen. }
  intros i' x' y' Hx' Hy'.
  destruct (decide (i = i')).
  + subst.
    assert (i' < length l).
    { apply lookup_lt_Some in Hy'.
      by rewrite -Hlen insert_length in Hy'. }
    rewrite list_lookup_insert in Hx'; last done.
    simplify_eq. apply Hy. apply (Hfa i'); last done.
    by apply list_lookup_insert.
  + rewrite list_lookup_insert_ne in Hx'; last done.
    apply (Hfa i'); last done.
    by rewrite list_lookup_insert_ne.
Qed.

Section st_interp_ctx_inv.
  Context `{!heapG Σ}.

  Global Instance state_interp_context_invariant (K : list ectx_item)
    : LanguageCtxInterp (fill K).
  Proof.
    split.
    - simpl. intros σ κs es i e Hesi.
      iIntros "($ & $ & Hsi)".
      iDestruct "Hsi" as (L T Hinv) "(Hlocknum & Hlockres & Hlocked & Hobs)".
      iExists L, T. iFrame. iPureIntro.
      unfold deadlock_inv in *.
      eapply Forall2_replace_l; last by eauto.
      intros [obs lockstate] HTi.
      clear Hinv.
      unfold deadlock_thread_inv in *.
      destruct lockstate as [l|].
      + destruct HTi as [R [n [b HH]]].
        exists R,n,b. destruct HH as [? [??]].
        do 2 (split; first by eauto).
        destruct H1 as [K' ->].
        exists (K' ++ K). by rewrite fill_app.
      + contradict HTi.
        eapply (fill_waiting (K:= fill K)); last done.
        admit.
    - intros σ κs es i e Hesi Hval.
      iIntros "(? & ? & Hsi)". iFrame.
      iDestruct "Hsi" as (L T) "(% & Hlocknum & Hlockres & Hlocked & Hobs)".
      iExists L. iExists T. iFrame. iPureIntro.
      unfold deadlock_inv in *.
      eapply Forall2_replace_l; last by eauto.
      intros [obs lockstate] HTi.
      unfold deadlock_thread_inv in *.
      destruct lockstate as [l|].
      + destruct HTi as [R [n [b HH]]].
        exists R,n,b. destruct HH as [? [??]].
        do 2 (split; first by eauto).
        destruct H2 as [K' H2].
        assert (H2' := H2).
        eapply step_by_val in H2.
        { destruct H2 as [K'' H2].
          exists K''. subst.
          simpl in H2'.
          rewrite fill_app in H2'.
          apply fill_inj in H2'.
          auto. }
        { auto. }
        { admit. }
      + contradict HTi.
        by eapply (waiting_fill (K:= fill K)).
  Admitted.
End st_interp_ctx_inv.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l 1 v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : core.
Local Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _ _) => eapply CmpXchgS : core.
Local Hint Extern 0 (head_step (AllocN _ _) _ _ _ _ _) => apply alloc_fresh : core.
Local Hint Extern 0 (head_step NewProph _ _ _ _ _) => apply new_proph_id_fresh : core.
Local Hint Resolve to_of_val : core.

Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

Instance rec_atomic s f x e : Atomic s (Rec f x e).
Proof. solve_atomic. Qed.
Instance pair_atomic s v1 v2 : Atomic s (Pair (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance injl_atomic s v : Atomic s (InjL (Val v)).
Proof. solve_atomic. Qed.
Instance injr_atomic s v : Atomic s (InjR (Val v)).
Proof. solve_atomic. Qed.
(** The instance below is a more general version of [Skip] *)
Instance beta_atomic s f x v1 v2 : Atomic s (App (RecV f x (Val v1)) (Val v2)).
Proof. destruct f, x; solve_atomic. Qed.
Instance unop_atomic s op v : Atomic s (UnOp op (Val v)).
Proof. solve_atomic. Qed.
Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance if_true_atomic s v1 e2 : Atomic s (If (Val $ LitV $ LitBool true) (Val v1) e2).
Proof. solve_atomic. Qed.
Instance if_false_atomic s e1 v2 : Atomic s (If (Val $ LitV $ LitBool false) e1 (Val v2)).
Proof. solve_atomic. Qed.
Instance fst_atomic s v : Atomic s (Fst (Val v)).
Proof. solve_atomic. Qed.
Instance snd_atomic s v : Atomic s (Snd (Val v)).
Proof. solve_atomic. Qed.

Instance fork_atomic s e : Atomic s (Fork e).
Proof. solve_atomic. Qed.

Instance alloc_atomic s v w : Atomic s (AllocN (Val v) (Val w)).
Proof. solve_atomic. Qed.
Instance load_atomic s v : Atomic s (Load (Val v)).
Proof. solve_atomic. Qed.
Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance cmpxchg_atomic s v0 v1 v2 : Atomic s (CmpXchg (Val v0) (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance was_atomic s v0 v1 v2 : Atomic s (WAS (Val v0) (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance faa_atomic s v1 v2 : Atomic s (FAA (Val v1) (Val v2)).
Proof. solve_atomic. Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Instance pure_recc f x (erec : expr) :
  PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof. solve_pure_exec. Qed.
Instance pure_pairc (v1 v2 : val) :
  PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof. solve_pure_exec. Qed.
Instance pure_injlc (v : val) :
  PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
Proof. solve_pure_exec. Qed.
Instance pure_injrc (v : val) :
  PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
Proof. solve_pure_exec. Qed.

Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
  PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof. solve_pure_exec. Qed.

Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
Proof. solve_pure_exec. Qed.
(* Higher-priority instance for [EqOp]. *)
Instance pure_eqop v1 v2 :
  PureExec (vals_compare_safe v1 v2) 1
    (BinOp EqOp (Val v1) (Val v2))
    (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
Proof.
  intros Hcompare.
  cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { intros. revert Hcompare. solve_pure_exec. }
  rewrite /bin_op_eval /= decide_True //.
Qed.

Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Instance pure_fst v1 v2 :
  PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof. solve_pure_exec. Qed.

Instance pure_snd v1 v2 :
  PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof. solve_pure_exec. Qed.

Instance pure_case_inl v e1 e2 :
  PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof. solve_pure_exec. Qed.

Instance pure_case_inr v e1 e2 :
  PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof. solve_pure_exec. Qed.

Section lifting.
Context `{!heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.


Lemma wp_newlock s E v :
  {{{ True }}} Alloc (Val $ LitV $ LitBool false) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_allocN_seq; auto with lia.
  iIntros "!>" (l) "/= (? & _)". rewrite loc_add_0. iApply "HΦ"; iFrame.
Qed.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ /=". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "Hσ !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. by iFrame.
Qed.

(** Heap *)
(** The usable rules for [allocN] stated in terms of the [array] proposition
are derived in te file [array]. *)
Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_mapsto l v (n : nat) :
  ([∗ map] l' ↦ v ∈ heap_array l (replicate n v), l' ↦ v) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma wp_allocN_seq s E v n :
  0 < n →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs k) "[Hσ Hκs] !>"; iSplit; first by auto with lia.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_alloc_gen _ (heap_array l (replicate (Z.to_nat n) v)) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id; auto with lia. }
  iModIntro; iSplit; first done. iFrame "Hσ Hκs". iApply "HΦ".
  iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_mapsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.

Lemma wp_alloc s E v :
  {{{ True }}} Alloc (Val v) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_allocN_seq; auto with lia.
  iIntros "!>" (l) "/= (? & _)". rewrite loc_add_0. iApply "HΦ"; iFrame.
Qed.

Lemma wp_load s E l q v :
  {{{ ▷ l ↦{q} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_store s E l v' v :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; [iPureIntro; left; eauto|].
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{q} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{q} v' }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_false //.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

(*
Lemma wp_was_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} WAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET #(); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by simplify_eq; eauto.
  iNext. iIntros (v2' σ2 efs  Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. iApply "HΦ". iFrame.
Qed.

Lemma wp_was_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{q} v' }}} WAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET #(); False }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit.
  { iPureIntro. right. eapply (Ectx_waiting _ _ [] (WAS #l v1 v2)); first done.
    eapply WasW; done. }
  iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
Qed. *)

Lemma wp_was s E l v' v1 v2 :
  vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} WAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET #(); ⌜v' = v1⌝ ∗ l ↦ v2 }}}.
Proof.
  iIntros (? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit.
  { destruct (decide (v' = v1)) eqn:Eqn.
    - simplify_eq. eauto.
    - iPureIntro. right. eapply (Ectx_waiting _ _ [] (WAS #l v1 v2)); first done.
      eapply WasW; done. }
  iNext. iIntros (v2' σ2 efs  Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. iApply "HΦ". iFrame. done.
Qed.

Lemma wp_was_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} WAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET #(); l ↦ v2 }}}.
Proof.
  iIntros (???) "H Post".
  iApply (wp_was with "H"); auto.
  iNext. iIntros "[_?]". iApply "Post". iFrame.
Qed.

Lemma wp_was_fail s E l v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} WAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET #(); False }}}.
Proof.
  iIntros (???) "H _".
  iApply (wp_was with "H"); auto.
  iNext. iIntros "[%_]". simplify_eq.
Qed.

Lemma wp_faa s E l i1 i2 :
  {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

End lifting.
