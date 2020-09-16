From iris.proofmode Require Import base tactics classes.

Inductive instr :=
  | Add : instr
  | Sub : instr
  | Cmp0 : instr
  | Jump : nat -> instr
  | Label : nat -> instr.

Definition prog := list instr.

Inductive ty := IntT | BoolT.

Inductive typed : prog -> list ty -> list (list ty) -> list bool -> Prop :=
  | Add_typed : ∀ p s l b,
    typed p (IntT :: IntT :: s) l b -> typed (p ++ [Add]) (IntT :: s) l b
  | Sub_typed : ∀ p s l b,
    typed p (IntT :: IntT :: s) l b -> typed (p ++ [Sub]) (IntT :: s) l b
  | Cmp0_typed : ∀ p s l b,
    typed p (IntT :: IntT :: s) l b -> typed (p ++ [Cmp0]) (BoolT :: s) l b
  | Jump_typed : ∀ p s s' l b i,
    typed p s l b -> l !! i = Some s -> typed (p ++ [Jump i]) s' l b
  | Label_typed : ∀ p s l b i,
    typed p s l b -> typed (p ++ [Label i]) s l (<[ i := true ]> b)
  | Fresh_typed : ∀ p s s' l b,
    typed p s l b -> typed p s (l ++ [s']) (b ++ [false]).

Definition closed_program_typed p := ∃ l b, typed p [] l b ∧ ∀ i s, b !! i = Some s -> s = true.


n : int
p : program
s : stack
L : labels
T : todo labels

Definition invariant s Δ K := ∃ I E, (E & I ⊢ b : ⟨ s ⟩) ∧ I - E = Δ ∧ K ⊂ I.

{ invariant s Δ K ∧ e : t }
compile e
{ invariant (t::s) Δ K }

{ invariant s Δ K}
l <- fresh
{ invariant s (Δ ∪ {l}) (K ∪ {l ~> s'} }

{ invariant s (Δ ∪ {l}) K ∧ (l ~> s) ∈ K }
label l
{ invariant s Δ K }

{ invariant s Δ K ∧ i : ⟨ s ~> s' ⟩ }
tell i
{ invariant s' Δ K }


{ invariant s (Δ ∪ {l}) K ∧ (l ~> s) ∈ K ∧ { invariant s Δ K } c() { invariant s' Δ' K'} }
attach l c
{ invariant s' Δ' K' }

ifte c e1 e2


{ invariant s Δ K }
compile c
{ invariant (bool::s) Δ K }
lthen <- fresh
{ invariant (bool::s) (Δ ∪ {lthen}) (K ∪ {lthen ~> ??} }
tell (ifne lthen)
{ invariant s (Δ ∪ {lthen}) (K ∪ {lthen ~> ??} }
lend <- fresh
{ invariant s (Δ ∪ {lthen,lend}) (K ∪ {lthen ~> ??, lend ~> ??} }
compile e2
{ invariant (t::s) (Δ ∪ {lthen,lend}) (K ∪ {lthen ~> ??, lend ~> ??} }
label lthen
{ invariant (t::s) (Δ ∪ {lend}) (K ∪ {lthen ~> ??, lend ~> ??} }
tell (jump lend)
{ invariant s (Δ ∪ {lend}) (K ∪ {lthen ~> ??, lend ~> ??} }
compile e1
{ invariant (t::s) (Δ ∪ {lend}) (K ∪ {lthen ~> ??, lend ~> ??} }
label lend
{ invariant (t::s) Δ (K ∪ {lthen ~> ??, lend ~> ??} }
{ invariant (t::s) Δ K }


{ invariant s Δ K ∧ e : t }
compile e
{ invariant (t::s) Δ K }

{ invariant s Δ K }
l <- fresh
{ ∃ Δ', Δ' = Δ ⊔ {l} ∧ invariant s Δ' (K ∪ {l ~> s'} }

{ Δ' = Δ ⊔ {l} ∧ invariant s Δ' K ∧ (l ~> s) ∈ K }
label l
{ invariant s Δ K }

{ invariant s Δ K ∧ i : ⟨ s ~> s' ⟩ }
tell i
{ invariant s' Δ K }
