From cgraphs.locks Require Export langdef.

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
  | ForkBarrier e => expr_refs e
  | NewLock e => expr_refs e
  | ForkLock e1 e2 => expr_refs e1 ∪ expr_refs e2
  | Acquire e => expr_refs e
  | Release e1 e2 => expr_refs e1 ∪ expr_refs e2
  | Wait e => expr_refs e
  | Drop e => expr_refs e
  end
with val_refs v :=
  match v with
  | FunV x e => expr_refs e
  | UnitV => ∅
  | PairV v1 v2 => val_refs v1 ∪ val_refs v2
  | SumV i v => val_refs v
  | BarrierV i => {[ i ]}
  | LockV i => {[ i ]}
  end.

Definition obj_refs x :=
  match x with
  | Thread e => expr_refs e
  | Barrier => ∅
  | Lock refcnt o =>
      match o with
      | Some v => val_refs v
      | None => ∅
      end
  end.


Inductive expr_head_waiting : expr -> nat -> Prop :=
  | Barrier_waiting j v :
    expr_head_waiting (App (Val $ BarrierV j) (Val v)) j
  | ForkLock_waiting j v :
    expr_head_waiting (ForkLock (Val $ LockV j) (Val v)) j
  | Acquire_waiting j :
    expr_head_waiting (Acquire (Val $ LockV j)) j
  | Release_waiting j v :
    expr_head_waiting (Release (Val $ LockV j) (Val v)) j
  | Wait_waiting j :
    expr_head_waiting (Wait (Val $ LockV j)) j
  | Drop_waiting j :
    expr_head_waiting (Drop (Val $ LockV j)) j.

(* Paper definition 2 *)
Definition expr_waiting e j :=
  ∃ k e', ctx k ∧ e = k e' ∧ expr_head_waiting e' j.

Definition waiting (ρ : cfg) (i j : nat) :=
  (∃ e, ρ !! i = Some (Thread e) ∧ expr_waiting e j) ∨
  (∃ y, ρ !! j = Some y ∧ i ∈ obj_refs y ∧ ∀ e, y = Thread e -> ¬ expr_waiting e i).

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
