From diris.microgv Require Export langdef.

(* The definition of the set of barrier references in an expression. *)
Fixpoint expr_refs e :=
  match e with
  | Val v => val_refs v
  | Var x => ∅
  | Fun x e => expr_refs e
  | App e1 e2 => expr_refs e1 ∪ expr_refs e2
  | Unit => ∅
  | Pair e1 e2 => expr_refs e1 ∪ expr_refs e2
  | LetPair e1 e2 => expr_refs e1 ∪ expr_refs e2
  | Sum i e => expr_refs e
  | MatchSum n e es => expr_refs e ∪ fin_union n (expr_refs ∘ es)
  | Fork e => expr_refs e
  end
with val_refs v :=
  match v with
  | FunV x e => expr_refs e
  | UnitV => ∅
  | PairV v1 v2 => val_refs v1 ∪ val_refs v2
  | SumV i v => val_refs v
  | BarrierV i => {[ i ]}
  end.

(* Paper definition 2 *)
Definition expr_waiting e j := ∃ k v, ctx k ∧ e = k (App (Val $ BarrierV j) (Val v)).

Definition waiting (ρ : cfg) (i j : nat) :=
  match ρ !! i, ρ !! j with
  | Some (Thread e), Some Barrier => expr_waiting e j
  | Some Barrier, Some (Thread e) => i ∈ expr_refs e ∧ ¬ expr_waiting e i
  | _,_ => False
  end.

(* These definitions are not explicitly given in the paper, but we factor them out in Coq *)
Definition can_step (ρ : cfg) (i : nat) := ∃ ρ', step i ρ ρ'.
Definition inactive (ρ : cfg) (i : nat) := ρ !! i = None.

(* Paper definition 3 *)
Record deadlock (ρ : cfg) (s : nat -> Prop) := {
  dl_nostep i : s i -> ¬ can_step ρ i;
  dl_waiting i j : waiting ρ i j -> s i -> s j;
}.

(* Paper definition 4 *)
Definition deadlock_free (ρ : cfg) :=
  ∀ s, deadlock ρ s -> ∀ i, s i -> inactive ρ i.

(* Paper definition 5 *)
Inductive reachable (ρ : cfg) : nat -> Prop :=
  | Can_step_reachable i :
      can_step ρ i -> reachable ρ i
  | Waiting_reachable i j :
      waiting ρ i j -> reachable ρ j -> reachable ρ i.

(* Paper definition 6 *)
Definition fully_reachable (ρ : cfg) :=
  ∀ i, inactive ρ i ∨ reachable ρ i.

(* Paper definition 8 *)
Definition global_progress (ρ : cfg) :=
  (∀ i, inactive ρ i) ∨ (∃ i, can_step ρ i).

(* Paper definition 9 *)
Definition type_safety (ρ : cfg) :=
  ∀ i, inactive ρ i ∨ can_step ρ i ∨ ∃ j, waiting ρ i j.
