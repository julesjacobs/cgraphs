From diris.microgv Require Export langtools.

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
with val :=
  | FunV : string -> expr -> val
  | UnitV : val
  | PairV : val -> val -> val
  | SumV : nat -> val -> val
  | BarrierV : nat -> val.


(* Type system *)
(* ----------- *)

Inductive linearity := Lin | Unr.

CoInductive type :=
  | FunT : linearity -> type -> type -> type
  | UnitT : type
  | PairT : type -> type -> type
  | SumT n : (fin n -> type) -> type.

CoInductive unr : type -> Prop :=
  | Fun_unr t1 t2 : unr (FunT Unr t1 t2)
  | Unit_unr : unr UnitT
  | Pair_unr t1 t2 : unr t1 -> unr t2 -> unr (PairT t1 t2)
  | Sum_unr n ts : (∀ i, unr (ts i)) -> unr (SumT n ts).

(* We define linear environment splitting here.
   On paper this is implicit in Γ1,Γ2 ⊢ e : A.
   In Coq we have to explicitly say env_split Γ Γ1 Γ2, and typed Γ e A. *)
Definition env := gmap string type.

Definition env_unr (Γ : env) :=
  ∀ x t, Γ !! x = Some t -> unr t.

Definition disj (Γ1 Γ2 : env) :=
  ∀ i t1 t2, Γ1 !! i = Some t1 -> Γ2 !! i = Some t2 -> t1 = t2 ∧ unr t1.

Definition env_split (Γ : env) (Γ1 : env) (Γ2 : env) :=
  Γ = Γ1 ∪ Γ2 ∧ disj Γ1 Γ2.

Definition env_bind (Γ' : env) (x : string) (t : type) (Γ : env) :=
  Γ' = <[ x := t ]> Γ ∧ ∀ t', Γ !! x = Some t' -> unr t'.

Definition env_var (Γ : env) (x : string) (t : type) :=
  ∃ Γ', Γ = <[ x := t ]> Γ' ∧ env_unr Γ'.


Inductive typed : env -> expr -> type -> Prop :=
  | Var_typed Γ x t :
    env_var Γ x t ->
    typed Γ (Var x) t
  | Fun_typed Γ Γ' x e t1 t2 l :
    env_bind Γ' x t1 Γ ->
    (l = Unr -> env_unr Γ) ->
    typed Γ' e t2 ->
    typed Γ (Fun x e) (FunT l t1 t2)
  | App_typed Γ Γ1 Γ2 e1 e2 t1 t2 l :
    env_split Γ Γ1 Γ2 ->
    typed Γ1 e1 (FunT l t1 t2) ->
    typed Γ2 e2 t1 ->
    typed Γ (App e1 e2) t2
  | Unit_typed Γ :
    env_unr Γ ->
    typed Γ Unit UnitT
  | Pair_typed Γ Γ1 Γ2 e1 e2 t1 t2 :
    env_split Γ Γ1 Γ2 ->
    typed Γ1 e1 t1 ->
    typed Γ2 e2 t2 ->
    typed Γ (Pair e1 e2) (PairT t1 t2)
  | LetPair_typed Γ Γ1 Γ2 e1 e2 t1 t2 t :
    env_split Γ Γ1 Γ2 ->
    typed Γ1 e1 (PairT t1 t2) ->
    typed Γ2 e2 (FunT Lin t1 (FunT Lin t2 t)) ->
    typed Γ (LetPair e1 e2) t
  | Sum_typed Γ n (ts : fin n -> type) i e :
    typed Γ e (ts i) ->
    typed Γ (Sum i e) (SumT n ts)
  | MatchSumN_typed n Γ Γ1 Γ2 t (ts : fin n -> type) es e :
    env_split Γ Γ1 Γ2 ->
    (n = 0 -> env_unr Γ2) ->
    typed Γ1 e (SumT n ts) ->
    (∀ i, typed Γ2 (es i) (FunT Lin (ts i) t)) ->
    typed Γ (MatchSum n e es) t
  | Fork_typed Γ e t1 t2 :
    typed Γ e (FunT Lin (FunT Lin t2 t1) UnitT) ->
    typed Γ (Fork e) (FunT Lin t1 t2).


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
    pure_step (MatchSum n (Val $ SumV i v) es) (App (es i) (Val v)).

Inductive ctx1 : (expr -> expr) -> Prop :=
  | Ctx_App_l e : ctx1 (λ x, App x e)
  | Ctx_App_r e : ctx1 (λ x, App e x)
  | Ctx_Pair_l e : ctx1 (λ x, Pair x e)
  | Ctx_Pair_r e : ctx1 (λ x, Pair e x)
  | Ctx_LetPair e : ctx1 (λ x, LetPair x e)
  | Ctx_Sum i : ctx1 (λ x, Sum i x)
  | Ctx_MatchSum n es : ctx1 (λ x, MatchSum n x es)
  | Ctx_Fork : ctx1 (λ x, Fork x).

Inductive ctx : (expr -> expr) -> Prop :=
  | Ctx_id : ctx id
  | Ctx_comp k1 k2 : ctx1 k1 -> ctx k2 -> ctx (k1 ∘ k2).

Inductive obj := Thread (e : expr) | Barrier.
Definition cfg := gmap nat obj.

Inductive local_step : nat -> cfg -> cfg -> Prop :=
  | Pure_step i k e e' :
    ctx k -> pure_step e e' ->
    local_step i {[ i := Thread (k e) ]} {[ i := Thread (k e') ]}
  | Exit_step i v :
    local_step i {[ i := Thread (Val v) ]} ∅
  | Fork_step i j n k v :
    i ≠ j -> i ≠ n -> j ≠ n -> ctx k ->
    local_step i {[ i := Thread (k (Fork (Val v))) ]}
                 {[ i := Thread (k (Val $ BarrierV n));
                    j := Thread (App (Val v) (Val $ BarrierV n));
                    n := Barrier ]}
  | Sync_step i j n k1 k2 v1 v2 :
    i ≠ j -> i ≠ n -> j ≠ n -> ctx k1 -> ctx k2 ->
    local_step n {[ i := Thread (k1 (App (Val $ BarrierV n) (Val v1)));
                    j := Thread (k2 (App (Val $ BarrierV n) (Val v2)));
                    n := Barrier ]}
                 {[ i := Thread (k1 $ Val v2);
                    j := Thread (k2 $ Val v1) ]}.

Inductive step : nat -> cfg -> cfg -> Prop :=
  | Frame_step ρ ρ' ρf i :
    ρ ##ₘ ρf -> ρ' ##ₘ ρf ->
    local_step i ρ ρ' -> step i (ρ ∪ ρf) (ρ' ∪ ρf).

Definition step' ρ ρ' := ∃ i, step i ρ ρ'.
Definition steps := rtc step'.

