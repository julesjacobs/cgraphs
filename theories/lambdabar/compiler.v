From diris.microgv Require Export langtools.
From diris.microgv Require Export langdef.

Module GV.

(* Expressions and values *)
(* ---------------------- *)

Inductive expr :=
  | Val : val -> expr
  | Var : string -> expr
  | Fun : string -> expr -> expr
  | App : expr -> expr -> expr
  | Unit : expr
  | Pair : expr -> expr -> expr
  | LetPair : expr -> expr -> expr
  | Sum : nat -> expr -> expr
  | MatchSum n : expr -> (fin n -> expr) -> expr
  | Fork : expr -> expr
  | Send : expr -> expr -> expr
  | Send' : val -> val -> expr (* We have dummy steps in the operational semantics to get a lockstep correspondence. *)
  | Send'' : val -> val -> expr (* This shows precisely which operations do administrative β reductions after compilation. *)
  | Send''' : val -> val -> expr
  | Send'''' : val -> val -> expr
  | Recv : expr -> expr
  | Close : expr -> expr
with val :=
  | FunV : string -> expr -> val
  | UnitV : val
  | PairV : val -> val -> val
  | SumV : nat -> val -> val
  | ChanV : nat -> val.


(* Operational semantics *)
(* --------------------- *)

Definition subst (x:string) (a:val) := fix rec e :=
  match e with
  | Val _ => e
  | Var x' => if decide (x = x') then Val a else e
  | Fun x' e => Fun x' (if decide (x = x') then e else rec e)
  | App e1 e2 => App (rec e1) (rec e2)
  | Unit => Unit
  | Pair e1 e2 => Pair (rec e1) (rec e2)
  | LetPair e1 e2 => LetPair (rec e1) (rec e2)
  | Sum n e => Sum n (rec e)
  | MatchSum n e1 e2 => MatchSum n (rec e1) (rec ∘ e2)
  | Fork e => Fork (rec e)
  | Send e1 e2 => Send (rec e1) (rec e2)
  | Send' v1 v2 => Send' v1 v2
  | Send'' v1 v2 => Send'' v1 v2
  | Send''' v1 v2 => Send''' v1 v2
  | Send'''' v1 v2 => Send'''' v1 v2
  | Recv e => Recv (rec e)
  | Close e => Close (rec e)
  end.

Inductive pure_step : expr -> expr -> Prop :=
  | Fun_step x e :
    pure_step (Fun x e) (Val $ FunV x e)
  | App_step x e a :
    pure_step (App (Val $ FunV x e) (Val a)) (subst x a e)
  | Unit_step :
    pure_step Unit (Val $ UnitV)
  | Pair_step v1 v2 :
    pure_step (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2)
  | LetPair_step v1 v2 e:
    pure_step (LetPair (Val $ PairV v1 v2) e) (App (App e (Val v1)) (Val v2))
  | Sum_step n v :
    pure_step (Sum n (Val v)) (Val $ SumV n v)
  | MatchSum_step n (i : fin n) v es :
    pure_step (MatchSum n (Val $ SumV i v) es) (App (es i) (Val v))
  | Send'_step v1 v2 :
    pure_step (Send (Val v1) (Val v2)) (Send' v1 v2)
  | Send''_step v1 v2 :
    pure_step (Send' v1 v2) (Send'' v1 v2)
  | Send'''_step v1 v2 :
    pure_step (Send'' v1 v2) (Send''' v1 v2)
  | Send''''_step v1 v2 :
    pure_step (Send''' v1 v2) (Send'''' v1 v2).


Inductive ctx1 : (expr -> expr) -> Prop :=
  | Ctx_App_l e : ctx1 (λ x, App x e)
  | Ctx_App_r e : ctx1 (λ x, App e x)
  | Ctx_Pair_l e : ctx1 (λ x, Pair x e)
  | Ctx_Pair_r e : ctx1 (λ x, Pair e x)
  | Ctx_LetPair e : ctx1 (λ x, LetPair x e)
  | Ctx_Sum i : ctx1 (λ x, Sum i x)
  | Ctx_MatchSum n es : ctx1 (λ x, MatchSum n x es)
  | Ctx_Fork : ctx1 (λ x, Fork x)
  | Ctx_Send_l e : ctx1 (λ x, Send x e)
  | Ctx_Send_r e : ctx1 (λ x, Send e x)
  | Ctx_Recv : ctx1 (λ x, Recv x)
  | Ctx_Close : ctx1 (λ x, Close x).

Inductive ctx : (expr -> expr) -> Prop :=
  | Ctx_id : ctx id
  | Ctx_comp k1 k2 : ctx1 k1 -> ctx k2 -> ctx (k1 ∘ k2).

(* Buffers are represented as doubly linked lists in the heap. *)
(* When a buffer element has been used, it gets set to `Used`.
   THe `Used` marker is then deleted from the heap in a subsequent step.
   This maintains the lockstep correspondence.
   The Buf' and Buf'' are for the administrative β reductions that messenger threads do. *)
Inductive obj := Thread (e : expr) | Chan | Buf (c1 c2 : nat) (v : val) | Buf' (c1 c2 : nat) (v : val) | Buf'' (c1 c2 : nat) (v : val) | Used.
Definition cfg := gmap nat obj.

Inductive local_step : nat -> cfg -> cfg -> Prop :=
  | Pure_step i k e e' :
    ctx k -> pure_step e e' ->
    local_step i {[ i := Thread (k e) ]} {[ i := Thread (k e') ]}
  | Exit_step i v :
    local_step i {[ i := Thread (Val v) ]} ∅
  | Buf_done_step i :
    local_step i {[ i := Used ]} ∅
  | Fork_step i j n k v :
    i ≠ j -> i ≠ n -> j ≠ n -> ctx k ->
    local_step i {[ i := Thread (k (Fork (Val v))) ]}
                 {[ i := Thread (k (Val $ ChanV n));
                    j := Thread (App (Val v) (Val $ ChanV n));
                    n := Chan ]}
  | Send_step i j n k v c :
    i ≠ j -> i ≠ n -> j ≠ n -> ctx k ->
    local_step i {[ i := Thread (k (Send'''' (ChanV c) v)) ]}
                 {[ i := Thread (k (Val $ ChanV n));
                    j := Buf c n v;
                    n := Chan ]}
  | Buf'_step i n v c :
    local_step i {[ i := Buf c n v ]} {[ i := Buf' c n v ]}
  | Buf''_step i n v c :
    local_step i {[ i := Buf' c n v ]} {[ i := Buf'' c n v ]}
  | Recv_step i j n  k v c :
    i ≠ j -> i ≠ n -> j ≠ n -> ctx k ->
    local_step n {[ i := Thread (k (Recv (Val $ ChanV n)));
                    j := Buf'' n c v;
                    n := Chan ]}
                 {[ i := Thread (k $ Val (PairV (ChanV c) v));
                    j := Used ]}.

Inductive step : nat -> cfg -> cfg -> Prop :=
  | Frame_step ρ ρ' ρf i :
    ρ ##ₘ ρf -> ρ' ##ₘ ρf ->
    local_step i ρ ρ' -> step i (ρ ∪ ρf) (ρ' ∪ ρf).

Definition step' ρ ρ' := ∃ i, step i ρ ρ'.
Definition steps := rtc step'.

End GV.

Notation Let x e1 e2 := (App (Fun x e2) e1).
Notation Let' x e1 e2 := (App (Val $ FunV x e2) e1).
Notation Let2 x y e1 e2 e3 := (App (App (Val $ FunV x (Fun y e3)) e1) e2).

Fixpoint compile (e : GV.expr) : expr :=
  match e with
  | GV.Val v => Val $ compile_val v
  | GV.Var x => Var x
  | GV.Fun x e => Fun x (compile e)
  | GV.App e1 e2 => App (compile e1) (compile e2)
  | GV.Unit => Unit
  | GV.Pair e1 e2 => Pair (compile e1) (compile e2)
  | GV.LetPair e1 e2 => LetPair (compile e1) (compile e2)
  | GV.Sum n e => Sum n (compile e)
  | GV.MatchSum n e f => MatchSum n (compile e) (compile ∘ f)
  | GV.Fork e => Fork (compile e)
  | GV.Send e1 e2 =>
      Let2 "x" "y" (compile e1) (compile e2) (
          Fork (Fun "z" (App (Var "x") (Pair (Var "z") (Var "y"))))
      )
  | GV.Send' v1 v2 =>
      Let "y" (Val $ compile_val v2) (
        Fork (Fun "z" (App (Val $ compile_val v1) (Pair (Var "z") (Var "y"))))
      )
  | GV.Send'' v1 v2 =>
      Let' "y" (Val $ compile_val v2) (
        Fork (Fun "z" (App (Val $ compile_val v1) (Pair (Var "z") (Var "y"))))
      )
  | GV.Send''' v1 v2 =>
        Fork (Fun "z" (App (Val $ compile_val v1) (Pair (Var "z") (Val $ compile_val v2))))
  | GV.Send'''' v1 v2 =>
        Fork (Val $ FunV "z" (App (Val $ compile_val v1) (Pair (Var "z") (Val $ compile_val v2))))
  | GV.Recv e => App (compile e) (Val $ UnitV)
  | GV.Close e => App (compile e) (Val $ UnitV)
  end
with compile_val (v : GV.val) : val :=
  match v with
  | GV.FunV x e => FunV x (compile e)
  | GV.UnitV => UnitV
  | GV.PairV v1 v2 => PairV (compile_val v1) (compile_val v2)
  | GV.SumV n v => SumV n (compile_val v)
  | GV.ChanV n => BarrierV n
  end.

Definition compile_obj (o : GV.obj) : obj :=
  match o with
  | GV.Thread e => Thread (compile e)
  | GV.Chan => Barrier
  | GV.Buf c n v => Thread (App (Val $ FunV "z" (App (Val $ BarrierV c) (Pair (Var "z") (Val $ compile_val v)))) (Val $ BarrierV n))
  | GV.Buf' c n v => Thread (App (Val $ BarrierV c) (Pair (Val $ BarrierV n) (Val $ compile_val v)))
  | GV.Buf'' c n v => Thread (App (Val $ BarrierV c) (Val $ PairV (BarrierV n) (compile_val v)))
  | GV.Used => Thread (Val $ UnitV)
  end.

Definition compile_cfg (ρ : GV.cfg) : cfg := compile_obj <$> ρ.

Lemma compile_ctx k1 :
  GV.ctx k1 -> ∃ k2, ctx k2 ∧ ∀ e, compile (k1 e) = k2 (compile e).
Proof.
  induction 1; eauto using ctx.
  destruct IHctx as [k3 [Hk3 Heq]].
  destruct H; simpl; setoid_rewrite Heq.
  - eexists (λ x, App (k3 x) _). split; eauto.
    eapply (Ctx_comp (λ x, App x _)); eauto using ctx1.
  - eexists (λ x, App _ (k3 x)). split; eauto.
    eapply (Ctx_comp (λ x, App _ x)); eauto using ctx1.
  - eexists (λ x, Pair (k3 x) _). split; eauto.
    eapply (Ctx_comp (λ x, Pair x _)); eauto using ctx1.
  - eexists (λ x, Pair _ (k3 x)). split; eauto.
    eapply (Ctx_comp (λ x, Pair _ x)); eauto using ctx1.
  - eexists (λ x, LetPair (k3 x) _). split; eauto.
    eapply (Ctx_comp (λ x, LetPair x _)); eauto using ctx1.
  - eexists (λ x, Sum _ (k3 x)). split; eauto.
    eapply (Ctx_comp (λ x, Sum _ x)); eauto using ctx1.
  - eexists (λ x, MatchSum _ (k3 x) _). split; eauto.
    eapply (Ctx_comp (λ x, MatchSum _ x _)); eauto using ctx1.
  - eexists (λ x, Fork (k3 x) ). split; eauto.
    eapply (Ctx_comp (λ x, Fork x)); eauto using ctx1.
  - eexists (λ x, App (App _ (k3 x)) _). split; eauto.
    eapply (Ctx_comp (λ x, App x _)); eauto using ctx1.
    eapply (Ctx_comp (λ x, App _ x)); eauto using ctx1.
  - eexists (λ x, App _ (k3 x)). split; eauto.
    eapply (Ctx_comp (λ x, App _ x)); eauto using ctx1.
  - eexists (λ x, App (k3 x) _). split; eauto.
    eapply (Ctx_comp (λ x, App x _)); eauto using ctx1.
  - eexists (λ x, App (k3 x) _). split; eauto.
    eapply (Ctx_comp (λ x, App x _)); eauto using ctx1.
Qed.

Lemma compile_subst x v e :
  compile (GV.subst x v e) = subst x (compile_val v) (compile e).
Proof.
  induction e; simpl; eauto; repeat case_decide; eauto;
  try by f_equal; simplify_eq.
  - f_equal; eauto. apply functional_extensionality. eauto.
  - do 4 (f_equal; eauto).
Qed.

Lemma ctx_append k1 k2 :
  ctx k1 -> ctx k2 -> ctx (k1 ∘ k2).
Proof.
  induction 1; eauto. intros Q.
  eapply (Ctx_comp k1); eauto.
Qed.

Lemma compile_pure_step i e e' k :
  ctx k ->
  GV.pure_step e e' ->
  local_step i {[i := Thread (k (compile e))]} {[i := Thread (k (compile e'))]}.
Proof.
  intros Hk []; simpl; try solve [econstructor; eauto using pure_step].
  - rewrite compile_subst. econstructor; eauto using pure_step.
  - econstructor; eauto using pure_step. econstructor.
  - eapply (Pure_step _ (λ x, k (App x _))); eauto using pure_step.
    { eapply ctx_append; eauto. eapply (Ctx_comp (λ x, App x _)); eauto using ctx, ctx1. }
    eapply App_step.
  - eapply (Pure_step _ (λ x, k (App x _))); eauto using pure_step.
    { eapply ctx_append; eauto. eapply (Ctx_comp (λ x, App x _)); eauto using ctx, ctx1. }
  - eapply Pure_step; eauto.
    eapply App_step.
  - eapply (Pure_step _ (λ x, k (Fork x))); eauto using pure_step.
    { eapply ctx_append; eauto. eapply Ctx_comp; eauto using ctx, ctx1. }
Qed.

Lemma compile_step ρ ρ' i :
  GV.step i ρ ρ' -> step i (compile_cfg ρ) (compile_cfg ρ').
Proof.
  intros Hstep.
  destruct Hstep.
  unfold compile_cfg.
  rewrite !map_fmap_union.
  econstructor; eauto using fmap_map_disjoint.
  clear H H0.
  destruct H1.
  - rewrite !map_fmap_singleton /=.
    destruct (compile_ctx k) as [k2 [Hk2 Hk2c]]; first done.
    rewrite !Hk2c.
    eapply compile_pure_step; done.
  - rewrite fmap_empty map_fmap_singleton /=. econstructor.
  - rewrite fmap_empty map_fmap_singleton /=. econstructor.
  - rewrite !fmap_insert fmap_empty /=.
    destruct (compile_ctx k) as [k2 [Hk2 Hk2c]]; first done.
    rewrite !Hk2c.
    econstructor; eauto.
  - rewrite !fmap_insert fmap_empty /=.
    destruct (compile_ctx k) as [k2 [Hk2 Hk2c]]; first done.
    rewrite !Hk2c /=.
    eapply Fork_step; eauto.
  - rewrite !map_fmap_singleton /=.
    eapply (Pure_step _ id); eauto using ctx.
    econstructor.
  - rewrite !map_fmap_singleton /=.
    eapply Pure_step; eauto using pure_step, ctx, ctx1.
  - rewrite !fmap_insert fmap_empty /=.
    destruct (compile_ctx k) as [k2 [Hk2 Hk2c]]; first done.
    rewrite !Hk2c /=.
    eapply (Sync_step i j n k2 id UnitV); eauto using ctx.
Qed.