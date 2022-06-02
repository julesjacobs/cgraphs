From iris.proofmode Require Import base tactics classes.

Definition chan := nat.
Definition endpoint := (chan * bool)%type.

Definition other (e : endpoint) : endpoint :=
    let '(x,b) := e in (x, negb b).

Inductive val :=
    | UnitV : val
    | NatV : nat -> val
    | PairV : val -> val -> val
    | InjV : bool -> val -> val
    | FunV : string -> expr -> val
    | UFunV : string -> expr -> val
    | ChanV : endpoint -> val

with expr :=
    | Val : val -> expr
    | Var : string -> expr
    | Pair : expr -> expr -> expr
    | Inj : bool -> expr -> expr
    | App : expr -> expr -> expr
    | UApp : expr -> expr -> expr
    | Lam : string -> expr -> expr
    | ULam : string -> expr -> expr
    | Send : expr -> expr -> expr
    | Recv : expr -> expr
    | Let : string -> expr -> expr -> expr
    | LetUnit : expr -> expr -> expr
    | LetProd : string -> string -> expr -> expr -> expr
    | MatchVoid : expr -> expr
    | MatchSum : expr -> string -> expr -> expr -> expr
    | If : expr -> expr -> expr -> expr
    | Fork : expr -> expr
    | Close : expr -> expr.

Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

Definition heap := gmap endpoint (list val).

CoInductive chan_type' (T : Type) :=
    | SendT : T -> chan_type' T -> chan_type' T
    | RecvT : T -> chan_type' T -> chan_type' T
    | EndT : chan_type' T.
Arguments SendT {_} _ _.
Arguments RecvT {_} _ _.
Arguments EndT {_}.
Global Instance sendt_params : Params (@SendT) 1 := {}.
Global Instance recvt_params : Params (@RecvT) 1 := {}.


CoInductive chan_type_equiv `{Equiv T} : Equiv (chan_type' T) :=
    | cteq_EndT : EndT ≡ EndT
    | cteq_SendT t1 t2 s1 s2 : t1 ≡ t2 -> s1 ≡ s2 -> SendT t1 s1 ≡ SendT t2 s2
    | cteq_RecvT t1 t2 s1 s2 : t1 ≡ t2 -> s1 ≡ s2 -> RecvT t1 s1 ≡ RecvT t2 s2.
Global Existing Instance chan_type_equiv.

Lemma chan_type_reflexive `{Equiv T} :
    Reflexive (≡@{T}) -> Reflexive (≡@{chan_type' T}).
Proof.
    intros ?. cofix IH. intros []; constructor; done.
Defined.

Lemma chan_type_symmetric `{Equiv T} :
    Symmetric (≡@{T}) -> Symmetric (≡@{chan_type' T}).
Proof.
    intros ?. cofix IH. intros ??[]; constructor; done.
Defined.

Lemma chan_type_transitive `{Equiv T} :
    Transitive (≡@{T}) -> Transitive (≡@{chan_type' T}).
Proof.
    intros ?. cofix IH. intros ???[]; inversion_clear 1; constructor; by etrans.
Defined.

Global Instance chan_type_equivalence `{Equiv T} :
    Equivalence (≡@{T}) -> Equivalence (≡@{chan_type' T}).
Proof.
    split.
    - apply chan_type_reflexive. apply _.
    - apply chan_type_symmetric. apply _.
    - apply chan_type_transitive. apply _.
Qed.

Global Instance sendt_proper `{Equiv T} : Proper ((≡) ==> (≡) ==> (≡)) (@SendT T).
Proof. by constructor. Qed.
Global Instance recvt_proper `{Equiv T} : Proper ((≡) ==> (≡) ==> (≡)) (@RecvT T).
Proof. by constructor. Qed.

Definition chan_type_id {T} (s : chan_type' T) : chan_type' T :=
    match s with
    | SendT t s' => SendT t s'
    | RecvT t s' => RecvT t s'
    | EndT => EndT
    end.

Lemma chan_type_id_id {T} (s : chan_type' T) :
    chan_type_id s = s.
Proof.
    by destruct s.
Qed.

Lemma chan_type_equiv_alt `{Equiv T} (s1 s2 : chan_type' T) :
    chan_type_id s1 ≡ chan_type_id s2 -> s1 ≡ s2.
Proof.
    intros.
    rewrite -(chan_type_id_id s1).
    rewrite -(chan_type_id_id s2).
    done.
Defined.

Lemma chan_type_equiv_end_eq `{Equiv T} (s : chan_type' T) :
    s ≡ EndT -> s = EndT.
Proof.
    by inversion 1.
Qed.

CoFixpoint dual {T} (s : chan_type' T) : chan_type' T :=
    match s with
    | SendT t s' => RecvT t (dual s')
    | RecvT t s' => SendT t (dual s')
    | EndT => EndT
    end.

Global Instance dual_proper `{Equiv T} : Proper ((≡) ==> (≡)) (@dual T).
Proof.
    cofix IH.
    intros s1 s2 HH.
    apply chan_type_equiv_alt.
    destruct HH; simpl; constructor; done || by apply IH.
Qed.

Section dual.
    Context `{Equiv T, !Equivalence (≡@{T})}.
    Implicit Type s : chan_type' T.

    Lemma dual_dual s :
        dual (dual s) ≡ s.
    Proof.
        apply chan_type_equiv_alt.
        revert s. cofix IH. intros []; simpl; constructor; try done;
        apply chan_type_equiv_alt; apply IH.
    Qed.

    Lemma dual_send s t : dual (SendT t s) ≡ RecvT t (dual s).
    Proof.
        apply chan_type_equiv_alt; done.
    Qed.

    Lemma dual_recv s t : dual (RecvT t s) ≡ SendT t (dual s).
    Proof.
        apply chan_type_equiv_alt; done.
    Qed.

    Lemma dual_end : dual (EndT : chan_type' T) ≡ EndT.
    Proof.
        apply chan_type_equiv_alt; done.
    Qed.

    Lemma dual_end_inv s : dual s ≡ EndT -> s = EndT.
    Proof.
        intros HH. destruct s; eauto.
        - rewrite ->dual_send in HH. inversion HH.
        - rewrite ->dual_recv in HH. inversion HH.
    Qed.
End dual.

Canonical Structure chan_type'O (T:ofe) := discreteO (chan_type' T).

CoInductive type :=
    | UnitT : type
    | VoidT : type
    | NatT : type
    | PairT : type -> type -> type
    | SumT : type -> type -> type
    | FunT : type -> type -> type
    | UFunT : type -> type -> type
    | ChanT : chan_type' type -> type.

Definition type_id (t : type) :=
    match t with
    | UnitT => UnitT
    | VoidT => VoidT
    | NatT => NatT
    | PairT t1 t2 => PairT t1 t2
    | SumT t1 t2 => SumT t1 t2
    | FunT t1 t2 => FunT t1 t2
    | UFunT t1 t2 => UFunT t1 t2
    | ChanT s => ChanT s
    end.

Lemma type_id_id t : type_id t = t.
Proof.
    by destruct t.
Qed.

CoInductive type_equiv : Equiv type :=
    | teq_UnitT : UnitT ≡ UnitT
    | teq_VoidT : VoidT ≡ VoidT
    | teq_NatT : NatT ≡ NatT
    | teq_PairT t1 t2 t1' t2' : t1 ≡ t2 -> t1' ≡ t2' -> PairT t1 t1' ≡ PairT t2 t2'
    | teq_SumT t1 t2 t1' t2' : t1 ≡ t2 -> t1' ≡ t2' -> SumT t1 t1' ≡ SumT t2 t2'
    | teq_FunT t1 t2 t1' t2' : t1 ≡ t2 -> t1' ≡ t2' -> FunT t1 t1' ≡ FunT t2 t2'
    | teq_UFunT t1 t2 t1' t2' : t1 ≡ t2 -> t1' ≡ t2' -> UFunT t1 t1' ≡ UFunT t2 t2'
    | teq_ChanT s1 s2 : s1 ≡ s2 -> ChanT s1 ≡ ChanT s2.
Global Existing Instance type_equiv.

Global Instance type_equivalence : Equivalence (≡@{type}).
Proof.
    split.
    - cofix IH. intros []; constructor; done || apply chan_type_reflexive, _.
    - cofix IH. intros ??[]; constructor; done || by apply (chan_type_symmetric _).
    - cofix IH. intros ???[]; inversion_clear 1; constructor;
      by etrans || by eapply (chan_type_transitive _).
Qed.

Canonical Structure typeO := discreteO type.
Notation chan_type := (chan_type' type).
Notation chan_typeO := (chan_type'O typeO).

Notation envT := (gmap string type).

CoInductive unrestricted : type -> Prop :=
    | Nat_unrestricted : unrestricted NatT
    | Unit_unrestricted : unrestricted UnitT
    | Void_unrestricted : unrestricted VoidT
    | UFun_unrestricted t1 t2 : unrestricted (UFunT t1 t2)
    | Pair_unrestricted t1 t2 :
        unrestricted t1 -> unrestricted t2 ->
        unrestricted (PairT t1 t2)
    | Sum_unrestricted t1 t2 :
        unrestricted t1 -> unrestricted t2 ->
        unrestricted (SumT t1 t2).

Definition disj (Γ1 Γ2 : envT) : Prop :=
  ∀ i t1 t2, Γ1 !! i = Some t1 -> Γ2 !! i = Some t2 -> t1 ≡ t2 ∧ unrestricted t1.

Definition Γunrestricted (Γ : envT) :=
  ∀ x t, Γ !! x = Some t -> unrestricted t.

Lemma Γunrestricted_empty : Γunrestricted ∅.
Proof.
  intros ??. rewrite lookup_empty. intro. congruence.
Qed.

Inductive typed : envT -> expr -> type -> Prop :=
    | Unit_typed Γ :
        Γunrestricted Γ ->
        typed Γ (Val UnitV) UnitT
    | Nat_typed : ∀ Γ n,
        Γunrestricted Γ ->
        typed Γ (Val (NatV n)) NatT
    | Var_typed : ∀ Γ x t t',
        Γ !! x = None ->
        Γunrestricted Γ ->
        t ≡ t' ->
        typed (Γ ∪ {[ x := t ]}) (Var x) t'
    | Pair_typed : ∀ Γ1 Γ2 e1 e2 t1 t2,
        disj Γ1 Γ2 ->
        typed Γ1 e1 t1 ->
        typed Γ2 e2 t2 ->
        typed (Γ1 ∪ Γ2) (Pair e1 e2) (PairT t1 t2)
    | App_typed : ∀ Γ1 Γ2 e1 e2 t1 t2,
        disj Γ1 Γ2 ->
        typed Γ1 e1 (FunT t1 t2) ->
        typed Γ2 e2 t1 ->
        typed (Γ1 ∪ Γ2) (App e1 e2) t2
    | UApp_typed : ∀ Γ1 Γ2 e1 e2 t1 t2,
        disj Γ1 Γ2 ->
        typed Γ1 e1 (UFunT t1 t2) ->
        typed Γ2 e2 t1 ->
        typed (Γ1 ∪ Γ2) (UApp e1 e2) t2
    | Lam_typed : ∀ Γ x e t1 t2,
        Γ !! x = None ->
        typed (Γ ∪ {[ x := t1 ]}) e t2 ->
        typed Γ (Lam x e) (FunT t1 t2)
    | ULam_typed : ∀ Γ x e t1 t2,
        Γ !! x = None ->
        Γunrestricted Γ ->
        typed (Γ ∪ {[ x := t1 ]}) e t2 ->
        typed Γ (ULam x e) (UFunT t1 t2)
    | Send_typed : ∀ Γ1 Γ2 e1 e2 t r,
        disj Γ1 Γ2 ->
        typed Γ1 e1 (ChanT (SendT t r)) ->
        typed Γ2 e2 t ->
        typed (Γ1 ∪ Γ2) (Send e1 e2) (ChanT r)
    | Recv_typed : ∀ Γ e t r,
        typed Γ e (ChanT (RecvT t r)) ->
        typed Γ (Recv e) (PairT (ChanT r) t)
    | Let_typed : ∀ Γ1 Γ2 e1 e2 t1 t2 x,
        disj Γ1 Γ2 ->
        Γ2 !! x = None ->
        typed Γ1 e1 t1 ->
        typed (Γ2 ∪ {[ x := t1 ]}) e2 t2 ->
        typed (Γ1 ∪ Γ2) (Let x e1 e2) t2
    | LetUnit_typed : ∀ Γ1 Γ2 e1 e2 t,
        disj Γ1 Γ2 ->
        typed Γ1 e1 UnitT ->
        typed Γ2 e2 t ->
        typed (Γ1 ∪ Γ2) (LetUnit e1 e2) t
    | LetProd_typed : ∀ Γ1 Γ2 e1 e2 t11 t12 t2 x1 x2,
        disj Γ1 Γ2 ->
        x1 ≠ x2 ->
        Γ2 !! x1 = None ->
        Γ2 !! x2 = None ->
        typed Γ1 e1 (PairT t11 t12) ->
        typed (Γ2 ∪ {[ x1 := t11 ]} ∪ {[ x2 := t12 ]}) e2 t2 ->
        typed (Γ1 ∪ Γ2) (LetProd x1 x2 e1 e2) t2
    | MatchVoid_typed : ∀ Γ e t,
        typed Γ e VoidT ->
        typed Γ (MatchVoid e) t
    | MatchSum_typed : ∀ Γ1 Γ2 e1 eL eR tL tR t x,
        disj Γ1 Γ2 ->
        Γ2 !! x = None ->
        typed Γ1 e1 (SumT tL tR) ->
        typed (Γ2 ∪ {[ x := tL ]}) eL t ->
        typed (Γ2 ∪ {[ x := tR ]}) eR t ->
        typed (Γ1 ∪ Γ2) (MatchSum e1 x eL eR) t
    | If_typed : ∀ Γ1 Γ2 e1 e2 e3 t,
        disj Γ1 Γ2 ->
        typed Γ1 e1 NatT ->
        typed Γ2 e2 t ->
        typed Γ2 e3 t ->
        typed (Γ1 ∪ Γ2) (If e1 e2 e3) t
    | Fork_typed : ∀ Γ e ct,
        typed Γ e (FunT (ChanT (dual ct)) UnitT) ->
        typed Γ (Fork e) (ChanT ct)
    | Close_typed : ∀ Γ e,
        typed Γ e (ChanT EndT) ->
        typed Γ (Close e) UnitT
    | Iso_typed : ∀ Γ t t' e,
        t ≡ t' -> (* The ≡-relation is unfolding of recursive types *)
        typed Γ e t ->
        typed Γ e t'.

Fixpoint subst (x:string) (a:val) (e:expr) : expr :=
  match e with
  | Val _ => e
  | Var x' => if decide (x = x') then Val a else e
  | App e1 e2 => App (subst x a e1) (subst x a e2)
  | Inj b e1 => Inj b (subst x a e1)
  | Pair e1 e2 => Pair (subst x a e1) (subst x a e2)
  | UApp e1 e2 => UApp (subst x a e1) (subst x a e2)
  | Lam x' e1 => if decide (x = x') then e else Lam x' (subst x a e1)
  | ULam x' e1 => if decide (x = x') then e else ULam x' (subst x a e1)
  | Send e1 e2 => Send (subst x a e1) (subst x a e2)
  | Recv e1 => Recv (subst x a e1)
  | Let x' e1 e2 => Let x' (subst x a e1) (if decide (x = x') then e2 else subst x a e2)
  | LetUnit e1 e2 => LetUnit (subst x a e1) (subst x a e2)
  | LetProd x' y' e1 e2 =>
      LetProd x' y' (subst x a e1) (if decide (x = x' ∨ x = y') then e2 else subst x a e2)
  | MatchVoid e1 => MatchVoid (subst x a e1)
  | MatchSum e1 x' eL eR =>
      MatchSum (subst x a e1) x'
        (if decide (x = x') then eL else subst x a eL)
        (if decide (x = x') then eR else subst x a eR)
  | If e1 e2 e3 => If (subst x a e1) (subst x a e2) (subst x a e3)
  | Fork e1 => Fork (subst x a e1)
  | Close e1 => Close (subst x a e1)
  end.

Inductive pure_step : expr -> expr -> Prop :=
    | Pair_step : ∀ v1 v2,
        pure_step (Pair (Val v1) (Val v2)) (Val (PairV v1 v2))
    | Inj_step : ∀ v1 b,
        pure_step (Inj b (Val v1)) (Val (InjV b v1))
    | App_step : ∀ x e a,
        pure_step (App (Val (FunV x e)) (Val a)) (subst x a e)
    | UApp_step : ∀ x e a,
        pure_step (UApp (Val (UFunV x e)) (Val a)) (subst x a e)
    | Lam_step : ∀ x e,
        pure_step (Lam x e) (Val (FunV x e))
    | ULam_step : ∀ x e,
        pure_step (ULam x e) (Val (UFunV x e))
    | If_step1 : ∀ n e1 e2,
        n ≠ 0 ->
        pure_step (If (Val (NatV n)) e1 e2) e1
    | If_step2 : ∀ e1 e2,
        pure_step (If (Val (NatV 0)) e1 e2) e2
    | MatchSum_step : ∀ x v eL eR b,
        pure_step (MatchSum (Val (InjV b v)) x eL eR)
            (if b then subst x v eL else subst x v eR)
    | Let_step : ∀ x v e,
        pure_step (Let x (Val v) e) (subst x v e)
    | LetUnit_step : ∀ e,
        pure_step (LetUnit (Val UnitV) e) e
    | LetProd_step : ∀ x1 x2 v1 v2 e,
        pure_step (LetProd x1 x2 (Val (PairV v1 v2)) e) (subst x1 v1 $ subst x2 v2 e).

Inductive head_step : expr -> heap -> expr -> heap -> list expr -> Prop :=
    | Pure_step : ∀ e e' h,
        pure_step e e' -> head_step e h e' h []
    | Send_step : ∀ h c y buf,
        h !! (other c) = Some buf ->
        head_step (Send (Val (ChanV c)) (Val y)) h (Val (ChanV c)) (<[ other c := buf ++ [y] ]> h) []
    | Recv_step : ∀ h c y buf,
        h !! c = Some (y::buf) ->
        head_step (Recv (Val (ChanV c))) h (Val (PairV (ChanV c) y)) (<[ c := buf ]> h) []
    | Close_step : ∀ c h,
        h !! c = Some [] ->
        head_step (Close (Val (ChanV c))) h (Val UnitV) (delete c h) []
    | Fork_step : ∀ v (h : heap) i,
        h !! (i,true) = None ->
        h !! (i,false) = None ->
        head_step
          (Fork (Val v)) h
          (Val $ ChanV (i, true)) (<[ (i,true) := [] ]> $ <[ (i,false) := [] ]> h)
          [App (Val v) (Val (ChanV (i, false)))].

Inductive ctx1 : (expr -> expr) -> Prop :=
    | Ctx_App_l : ∀ e, ctx1 (λ x, App x e)
    | Ctx_App_r : ∀ v, ctx1 (λ x, App (Val v) x)
    | Ctx_Pair_l : ∀ e, ctx1 (λ x, Pair x e)
    | Ctx_Pair_r : ∀ v, ctx1 (λ x, Pair (Val v) x)
    | Ctx_Inj : ∀ b, ctx1 (λ x, Inj b x)
    | Ctx_UApp_l : ∀ e, ctx1 (λ x, UApp x e)
    | Ctx_UApp_r : ∀ v, ctx1 (λ x, UApp (Val v) x)
    | Ctx_Send_l : ∀ e, ctx1 (λ x, Send x e)
    | Ctx_Send_r : ∀ v, ctx1 (λ x, Send (Val v) x)
    | Ctx_Recv : ctx1 (λ x, Recv x)
    | Ctx_Let : ∀ s e, ctx1 (λ x, Let s x e)
    | Ctx_LetUnit : ∀ e, ctx1 (λ x, LetUnit x e)
    | Ctx_LetProd : ∀ s1 s2 e, ctx1 (λ x, LetProd s1 s2 x e)
    | Ctx_MatchVoid : ctx1 (λ x, MatchVoid x)
    | Ctx_MatchSum : ∀ s e1 e2, ctx1 (λ x, MatchSum x s e1 e2)
    | Ctx_If : ∀ e1 e2, ctx1 (λ x, If x e1 e2)
    | Ctx_Fork : ctx1 (λ x, Fork x)
    | Ctx_Close : ctx1 (λ x, Close x).

Inductive ctx : (expr -> expr) -> Prop :=
    | Ctx_nil : ctx (λ x, x)
    | Ctx_cons : ∀ k1 k2, ctx1 k1 -> ctx k2 -> ctx (λ x, (k1 (k2 x))).

Inductive ctx_step : expr -> heap -> expr -> heap -> list expr -> Prop :=
  | Ctx_step : ∀ k e h e' h' ts,
      ctx k -> head_step e h e' h' ts -> ctx_step (k e) h (k e') h' ts.

Inductive stepi : nat -> list expr -> heap -> list expr -> heap -> Prop :=
  | Head_step : ∀ e e' h h' i ts es,
      ctx_step e h e' h' ts ->
      es !! i = Some e ->
      stepi i es h (<[i := e']> es ++ ts) h'.

Definition step es h es' h' := ∃ i, stepi i es h es' h'.

Definition can_stepi i es h := ∃ es' h', stepi i es h es' h'.

(* Closure of the step relation; this is used in the theorem statement. *)
Inductive steps : list expr -> heap -> list expr -> heap -> Prop :=
  | Trans_step : ∀ e1 e2 e3 s1 s2 s3,
      step e1 s1 e2 s2 ->
      steps e2 s2 e3 s3 ->
      steps e1 s1 e3 s3
  | Empty_step : ∀ e1 s1,
      steps e1 s1 e1 s1.