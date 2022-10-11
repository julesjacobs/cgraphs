From cgraphs.locks.lambdalockpp Require Export langtools.
From cgraphs.cgraphs Require Import util.

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
  (* Barriers *)
  | ForkBarrier : expr -> expr
  (* Locks *)
  | NewGroup : expr
  | DropGroup : expr -> expr
  | NewLock : nat -> expr -> expr
  | DropLock : nat -> expr -> expr
  | ForkLock : expr -> expr -> expr
  | Acquire : nat -> expr -> expr
  | Release : nat -> expr -> expr -> expr
  | Wait : nat -> expr -> expr
with val :=
  | FunV : string -> expr -> val
  | UnitV : val
  | PairV : val -> val -> val
  | SumV : nat -> val -> val
  | BarrierV : nat -> val
  | LockGV : nat -> list nat -> val.


(* Type system *)
(* ----------- *)

Inductive linearity := Lin | Unr.

Inductive lockstate := Opened | Closed.
Inductive lockownership := Owner | Client.
Definition lockcap : Type := lockownership * lockstate.
Inductive lockownership_split : lockownership -> lockownership -> lockownership -> Prop :=
  | lo_split_1 : lockownership_split Owner Client Owner
  | lo_split_2 : lockownership_split Owner Owner Client
  | lo_split_3 : lockownership_split Client Client Client.
Inductive lockstate_split : lockstate -> lockstate -> lockstate -> Prop :=
  | ls_split_1 : lockstate_split Opened Closed Opened
  | ls_split_2 : lockstate_split Opened Opened Closed
  | ls_split_3 : lockstate_split Closed Closed Closed.
Definition lockcap_split l1 l2 l3 :=
  lockownership_split l1.1 l2.1 l3.1 ∧ lockstate_split l1.2 l2.2 l3.2.

CoInductive type :=
  | FunT : linearity -> type -> type -> type
  | UnitT : type
  | PairT : type -> type -> type
  | SumT n : (fin n -> type) -> type
  | LockGT : list (lockcap * type) -> type.

Definition lockcaps_split (xs1 xs2 xs3 : list (lockcap * type)) : Prop :=
  Forall3 (λ '(l1,t1) '(l2, t2) '(l3, t3), t1 = t2 ∧ t2 = t3 ∧ lockcap_split l1 l2 l3) xs1 xs2 xs3.

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

Definition finlist {T:Type} {n:nat} (f : fin n -> T) (xs : list T) :=
  n = length xs ∧ ∀ i, Some (f i) = xs !! (i : nat).

Inductive typed : env -> expr -> type -> Prop :=
  (* Base language *)
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
  (* Barriers *)
  | Fork_typed Γ e t1 t2 :
    typed Γ e (FunT Lin (FunT Lin t2 t1) UnitT) ->
    typed Γ (ForkBarrier e) (FunT Lin t1 t2)
  (* Locks *)
  | NewGroup_typed Γ :
    env_unr Γ ->
    typed Γ NewGroup (LockGT [])
  | DropGroup_typed Γ e :
    typed Γ e (LockGT []) ->
    typed Γ (DropGroup e) UnitT
  | NewLock_typed Γ i e t xs :
    typed Γ e (LockGT xs) ->
    typed Γ (NewLock i e) (LockGT (insert2 i ((Owner,Opened),t) xs))
  | DropLock_typed Γ i e xs t :
    xs !! i = Some ((Client,Closed),t) ->
    typed Γ e (LockGT xs) ->
    typed Γ (DropLock i e) (LockGT (delete i xs))
  | Wait_typed Γ i e xs t :
    (* Needs precondition *)
    xs !! i = Some ((Owner,Closed),t) ->
    (∀ j ownership state t', xs !! j = Some ((ownership,state),t') ->
        (state = Closed) ∧ (j < i -> ownership = Owner)) ->
    typed Γ e (LockGT xs) ->
    typed Γ (Wait i e) (PairT (LockGT (delete i xs)) t)
  | Acquire_typed Γ i e xs t a :
    (* Needs precondition *)
    xs !! i = Some ((a,Closed),t) ->
    (∀ j ownership state t', j < i -> xs !! j = Some ((ownership,state),t') -> state = Closed) ->
    typed Γ e (LockGT xs) ->
    typed Γ (Acquire i e) (PairT (LockGT (<[ i := ((a,Opened),t) ]> xs)) t)
  | Release_typed Γ Γ1 Γ2 i e1 e2 xs t a :
    xs !! i = Some ((a,Opened),t) ->
    env_split Γ Γ1 Γ2 ->
    typed Γ1 e1 (LockGT xs) ->
    typed Γ2 e2 t ->
    typed Γ (Release i e1 e2) (LockGT (<[ i := ((a,Closed),t) ]> xs))
  | ForkLock_typed Γ Γ1 Γ2 e1 e2 xs1 xs2 xs3 :
    env_split Γ Γ1 Γ2 ->
    lockcaps_split xs1 xs2 xs3 ->
    typed Γ1 e1 (LockGT xs1) ->
    typed Γ2 e2 (FunT Lin (LockGT xs2) UnitT) ->
    typed Γ (ForkLock e1 e2) (LockGT xs3).

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
  | ForkBarrier e => ForkBarrier (rec e)
  | NewGroup => NewGroup
  | DropGroup e => DropGroup (rec e)
  | NewLock i e => NewLock i (rec e)
  | DropLock i e => DropLock i (rec e)
  | Acquire i e => Acquire i (rec e)
  | Release i e1 e2 => Release i (rec e1) (rec e2)
  | Wait i e => Wait i (rec e)
  | ForkLock e1 e2 => ForkLock (rec e1) (rec e2)
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
  | Ctx_ForkBarrier : ctx1 (λ x, ForkBarrier x)
  | Ctx_DropGroup : ctx1 (λ x, DropGroup x)
  | Ctx_NewLock i : ctx1 (λ x, NewLock i x)
  | Ctx_DropLock i : ctx1 (λ x, DropLock i x)
  | Ctx_ForkLock_l e : ctx1 (λ x, ForkLock x e)
  | Ctx_ForkLock_r e : ctx1 (λ x, ForkLock e x)
  | Ctx_Acquire i : ctx1 (λ x, Acquire i x)
  | Ctx_Release_l i e : ctx1 (λ x, Release i x e)
  | Ctx_Release_r i e : ctx1 (λ x, Release i e x)
  | Ctx_Wait i : ctx1 (λ x, Wait i x).

Inductive ctx : (expr -> expr) -> Prop :=
  | Ctx_id : ctx id
  | Ctx_comp k1 k2 : ctx1 k1 -> ctx k2 -> ctx (k1 ∘ k2).

Definition locksbundle := gmap nat (nat * option val).
Inductive obj := Thread (e : expr) | Barrier | LockG (refcnt : nat) (lcks : locksbundle).
Definition cfg := gmap nat obj.

(*
xs = {#a ↦ lock1, #b ↦ lock2}
ls = [#a, #b]

xs = {#a ↦ lock1, #b ↦ lock2, #c ↦ (0,None), #d ↦ lock3}
ls0 = [#d, #a]
ls = [#a, #c, #b]
ls' = [#a, #c, #b]

Lock order: #d, #a, #c, #b
*)

Definition incr_all_refcounts (xs : locksbundle) (ls : list nat) : locksbundle :=
  foldr (alter (λ '(refcnt,o), (refcnt+1,o))) xs ls.

Inductive local_step : nat -> cfg -> cfg -> Prop :=
  (* Base language *)
  | Pure_step i k e e' :
    ctx k -> pure_step e e' ->
    local_step i {[ i := Thread (k e) ]} {[ i := Thread (k e') ]}
  | Exit_step i :
    local_step i {[ i := Thread (Val UnitV) ]} ∅
  (* Barriers *)
  | Fork_step i j n k v :
    i ≠ j -> i ≠ n -> j ≠ n -> ctx k ->
    local_step i {[ i := Thread (k (ForkBarrier (Val v))) ]}
                 {[ i := Thread (k (Val $ BarrierV n));
                    j := Thread (App (Val v) (Val $ BarrierV n));
                    n := Barrier ]}
  | Sync_step i j n k1 k2 v1 v2 :
    i ≠ j -> i ≠ n -> j ≠ n -> ctx k1 -> ctx k2 ->
    local_step n {[ i := Thread (k1 (App (Val $ BarrierV n) (Val v1)));
                    j := Thread (k2 (App (Val $ BarrierV n) (Val v2)));
                    n := Barrier ]}
                 {[ i := Thread (k1 $ Val v2);
                    j := Thread (k2 $ Val v1) ]}
  (* Locks *)
  | NewGroup_step k i n :
    i ≠ n -> ctx k ->
    local_step i {[ i := Thread (k NewGroup) ]}
                 {[ i := Thread (k (Val $ LockGV n []));
                    n := LockG 1 ∅ ]}
  | DeleteGroup_step n :
    local_step n {[ n := LockG 0 ∅ ]} ∅
  | DropGroup_step k i n refcnt xs :
    i ≠ n -> ctx k ->
    local_step n {[ i := Thread (k (DropGroup (Val $ LockGV n [])));
                    n := LockG (S refcnt) xs ]}
                 {[ i := Thread (k (Val $ UnitV));
                    n := LockG refcnt xs ]}
  | NewLock_step k n i refcnt xs ls ii jj :
    i ≠ n -> ctx k ->
    xs !! jj = None ->
    local_step n {[ i := Thread (k (NewLock ii (Val $ LockGV n ls)));
                    n := LockG refcnt xs ]}
                 {[ i := Thread (k (Val $ LockGV n (insert2 ii jj ls)));
                    n := LockG refcnt (<[ jj := (0,None) ]> xs) ]}
  | DropLock_step o k i n refcnt xs ls ii jj refcntii :
    i ≠ n -> ctx k ->
    ls !! ii = Some jj ->
    xs !! jj = Some (S refcntii, o) ->
    local_step n {[ i := Thread (k (DropLock ii (Val $ LockGV n ls)));
                    n := LockG refcnt xs ]}
                 {[ i := Thread (k (Val $ LockGV n (delete ii ls)));
                    n := LockG refcnt (<[ jj := (refcntii,o) ]> xs) ]}
  | Acquire_step v k i n refcnt ii jj refcntii xs ls :
    i ≠ n -> ctx k ->
    ls !! ii = Some jj ->
    xs !! jj = Some (refcntii, Some v) ->
    local_step n {[ i := Thread (k (Acquire ii (Val $ LockGV n ls)));
                    n := LockG refcnt xs ]}
                 {[ i := Thread (k (Val $ PairV (LockGV n ls) v));
                    n := LockG refcnt (<[ jj := (refcntii, None) ]> xs) ]}
  | Release_step v k i n refcnt ii jj refcntii xs ls :
    i ≠ n -> ctx k ->
    ls !! ii = Some jj ->
    xs !! jj = Some (refcntii, None) ->
    local_step n {[ i := Thread (k (Release ii (Val $ LockGV n ls) (Val v)));
                    n := LockG refcnt xs ]}
                 {[ i := Thread (k (Val $ LockGV n ls));
                    n := LockG refcnt (<[ jj := (refcntii, Some v) ]> xs) ]}
  | Wait_step v k i n ii jj refcnt xs ls :
    i ≠ n -> ctx k ->
    ls !! ii = Some jj ->
    xs !! jj = Some (0, Some v) ->
    local_step n {[ i := Thread (k (Wait ii (Val $ LockGV n ls)));
                    n := LockG refcnt xs ]}
                 {[ i := Thread (k (Val $ PairV (LockGV n (delete ii ls)) v));
                    n := LockG refcnt (delete jj xs) ]}
  | ForkLock_step v k i j n refcnt xs ls :
      i ≠ j -> i ≠ n -> j ≠ n -> ctx k ->
      local_step n {[ i := Thread (k (ForkLock (Val $ LockGV n ls) (Val v)));
                      n := LockG refcnt xs ]}
                   {[ i := Thread (k (Val $ LockGV n ls));
                      j := Thread (App (Val v) (Val $ LockGV n ls));
                      n := LockG (S refcnt) (incr_all_refcounts xs ls) ]}.


Inductive step : nat -> cfg -> cfg -> Prop :=
  | Frame_step ρ ρ' ρf i :
    ρ ##ₘ ρf -> ρ' ##ₘ ρf ->
    local_step i ρ ρ' -> step i (ρ ∪ ρf) (ρ' ∪ ρf).

Definition step' ρ ρ' := ∃ i, step i ρ ρ'.
Definition steps := rtc step'.

