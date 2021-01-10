From iris.proofmode Require Import base tactics classes.

Definition chan := nat.
Definition endpoint := (chan * bool)%type.

Definition other (e : endpoint) : endpoint :=
    let '(x,b) := e in (x, negb b).

Inductive val :=
    | Unit : val
    | Nat : nat -> val
    | Pair : val -> val -> val
    | Fun : string -> expr -> val
    | Chan : endpoint -> val

with expr :=
    | Val : val -> expr
    | Var : string -> expr
    | App : expr -> expr -> expr
    | Lam : string -> expr -> expr
    | Send : expr -> expr -> expr
    | Recv : expr -> expr
    | Let : string -> expr -> expr -> expr
    | LetUnit : expr -> expr -> expr
    | LetProd : string -> string -> expr -> expr -> expr
    | If : expr -> expr -> expr -> expr
    | Fork : expr -> expr
    | Close : expr -> expr.

Definition heap := gmap endpoint (list val).

Inductive type :=
    | UnitT : type
    | NatT : type
    | PairT : type -> type -> type
    | FunT : type -> type -> type
    | ChanT : chan_type -> type

with chan_type :=
    | SendT : type -> chan_type -> chan_type
    | RecvT : type -> chan_type -> chan_type
    | EndT : chan_type.

Notation envT := (gmap string type).

Fixpoint dual ct :=
    match ct with
    | EndT => EndT
    | SendT c ct => RecvT c (dual ct)
    | RecvT c ct => SendT c (dual ct)
    end.

Inductive typed : envT -> expr -> type -> Prop :=
    | Unit_typed : typed ∅ (Val Unit) UnitT
    | Nat_typed : ∀ n, typed ∅ (Val (Nat n)) NatT
    | Var_typed : ∀ x t,
        typed {[ x := t ]} (Var x) t
    | App_typed : ∀ Γ1 Γ2 e1 e2 t1 t2,
        Γ1 ##ₘ Γ2 ->
        typed Γ1 e1 (FunT t1 t2) ->
        typed Γ2 e2 t1 ->
        typed (Γ1 ∪ Γ2) (App e1 e2) t2
    | Lam_typed : ∀ Γ x e t1 t2,
        Γ !! x = None ->
        typed (Γ ∪ {[ x := t1 ]}) e t2 ->
        typed Γ (Lam x e) (FunT t1 t2)
    | Send_typed : ∀ Γ1 Γ2 e1 e2 t r,
        Γ1 ##ₘ Γ2 ->
        typed Γ1 e1 (ChanT (SendT t r)) ->
        typed Γ2 e2 t ->
        typed (Γ1 ∪ Γ2) (Send e1 e2) (ChanT r)
    | Recv_typed : ∀ Γ e t r,
        typed Γ e (ChanT (RecvT t r)) ->
        typed Γ (Recv e) (PairT t (ChanT r))
    | Let_typed : ∀ Γ1 Γ2 e1 e2 t1 t2 x,
        Γ1 ##ₘ Γ2 ->
        Γ2 !! x = None ->
        typed Γ1 e1 t1 ->
        typed (Γ2 ∪ {[ x := t1 ]}) e2 t2 ->
        typed (Γ1 ∪ Γ2) (Let x e1 e2) t2
    | LetUnit_typed : ∀ Γ1 Γ2 e1 e2 t,
        Γ1 ##ₘ Γ2 ->
        typed Γ1 e1 UnitT ->
        typed Γ2 e2 t ->
        typed (Γ1 ∪ Γ2) (LetUnit e1 e2) t
    | LetProd_typed : ∀ Γ1 Γ2 e1 e2 t11 t12 t2 x1 x2,
        Γ1 ##ₘ Γ2 ->
        x1 ≠ x2 ->
        Γ2 !! x1 = None ->
        Γ2 !! x2 = None ->
        typed Γ1 e1 (PairT t11 t12) ->
        typed (Γ2 ∪ {[ x1 := t11 ]} ∪ {[ x2 := t12 ]}) e2 t2 ->
        typed (Γ1 ∪ Γ2) (LetProd x1 x2 e1 e2) t2
    | If_typed : ∀ Γ1 Γ2 e1 e2 e3 t,
        Γ1 ##ₘ Γ2 ->
        typed Γ1 e1 NatT ->
        typed Γ2 e2 t ->
        typed Γ2 e3 t ->
        typed (Γ1 ∪ Γ2) (If e1 e2 e3) t
    | Fork_typed : ∀ Γ e ct,
        typed Γ e (FunT (ChanT (dual ct)) UnitT) ->
        typed Γ (Fork e) (ChanT ct)
    | Close_typed : ∀ Γ e,
        typed Γ e (ChanT EndT) ->
        typed Γ (Close e) UnitT.

Fixpoint subst (x:string) (a:val) (e:expr) : expr :=
  match e with
  | Val _ => e
  | Var x' => if decide (x = x') then Val a else e
  | App e1 e2 => App (subst x a e1) (subst x a e2)
  | Lam x' e1 => if decide (x = x') then e else Lam x' (subst x a e1)
  | Send e1 e2 => Send (subst x a e1) (subst x a e2)
  | Recv e1 => Recv (subst x a e1)
  | Let x' e1 e2 => Let x' (subst x a e1) (if decide (x = x') then e2 else subst x a e2)
  | LetUnit e1 e2 => LetUnit (subst x a e1) (subst x a e2)
  | LetProd x' y' e1 e2 =>
      LetProd x' y' (subst x a e1) (if decide (x = x' ∨ x = y') then e2 else subst x a e2)
  | If e1 e2 e3 => If (subst x a e1) (subst x a e2) (subst x a e3)
  | Fork e1 => Fork (subst x a e1)
  | Close e1 => Close (subst x a e1)
  end.

Inductive pure_step : expr -> expr -> Prop :=
    | App_step : ∀ x e a,
        pure_step (App (Val (Fun x e)) (Val a)) (subst x a e)
    | Lam_step : ∀ x e,
        pure_step (Lam x e) (Val (Fun x e))
    | If_step1 : ∀ n e1 e2,
        n ≠ 0 ->
        pure_step (If (Val (Nat n)) e1 e2) e1
    | If_step2 : ∀ e1 e2,
        pure_step (If (Val (Nat 0)) e1 e2) e2
    | Let_step : ∀ x v e,
        pure_step (Let x (Val v) e) (subst x v e)
    | LetUnit_step : ∀ e,
        pure_step (LetUnit (Val Unit) e) e
    | LetProd_step : ∀ x1 x2 v1 v2 e,
        pure_step (LetProd x1 x2 (Val (Pair v1 v2)) e) (subst x1 v1 $ subst x2 v2 e).

Inductive head_step : expr -> heap -> expr -> heap -> list expr -> Prop :=
    | Pure_step : ∀ e e' h,
        pure_step e e' -> head_step e h e' h []
    | Send_step : ∀ h c y buf,
        h !! (other c) = Some buf ->
        head_step (Send (Val (Chan c)) (Val y)) h (Val (Chan c)) (<[ other c := buf ++ [y] ]> h) []
    | Recv_step : ∀ h c y buf,
        h !! c = Some (y::buf) ->
        head_step (Recv (Val (Chan c))) h (Val (Pair (Chan c) y)) (<[ c := buf ]> h) []
    | Close_step : ∀ c h,
        h !! c = Some [] ->
        head_step (Close (Val (Chan c))) h (Val Unit) (delete c h) []
    | Fork_step : ∀ v (h : heap) i,
        h !! (i,true) = None ->
        h !! (i,false) = None ->
        head_step
          (Fork (Val v)) h
          (Val $ Chan (i, true)) (<[ (i,true) := [] ]> $ <[ (i,false) := [] ]> h)
          [App (Val v) (Val (Chan (i, false)))].

Inductive ctx1 : (expr -> expr) -> Prop :=
    | Ctx_App_l : ∀ e, ctx1 (λ x, App x e)
    | Ctx_App_r : ∀ v, ctx1 (λ x, App (Val v) x)
    | Ctx_Send_l : ∀ e, ctx1 (λ x, Send x e)
    | Ctx_Send_r : ∀ v, ctx1 (λ x, Send (Val v) x)
    | Ctx_Recv : ctx1 (λ x, Recv x)
    | Ctx_Let : ∀ s e, ctx1 (λ x, Let s x e)
    | Ctx_LetUnit : ∀ e, ctx1 (λ x, LetUnit x e)
    | Ctx_LetProd : ∀ s1 s2 e, ctx1 (λ x, LetProd s1 s2 x e)
    | Ctx_If : ∀ e1 e2, ctx1 (λ x, If x e1 e2)
    | Ctx_Fork : ctx1 (λ x, Fork x)
    | Ctx_Close : ctx1 (λ x, Close x).

Inductive ctx : (expr -> expr) -> Prop :=
    | Ctx_nil : ctx (λ x, x)
    | Ctx_cons : ∀ k1 k2, ctx1 k1 -> ctx k2 -> ctx (λ x, (k1 (k2 x))).

Inductive ctx_step : expr -> heap -> expr -> heap -> list expr -> Prop :=
  | Ctx_step : ∀ k e h e' h' ts,
      ctx k -> head_step e h e' h' ts -> ctx_step (k e) h (k e') h' ts.

Inductive step : list expr -> heap -> list expr -> heap -> Prop :=
  | Head_step : ∀ e e' h h' i ts es,
      ctx_step e h e' h' ts ->
      es !! i = Some e ->
      step es h (<[i := e']> es ++ ts) h'.

(* Closure of the step relation; this is used in the theorem statement. *)
Inductive steps : list expr -> heap -> list expr -> heap -> Prop :=
  | Trans_step : ∀ e1 e2 e3 s1 s2 s3,
      step e1 s1 e2 s2 ->
      steps e2 s2 e3 s3 ->
      steps e1 s1 e3 s3
  | Empty_step : ∀ e1 s1,
      steps e1 s1 e1 s1.