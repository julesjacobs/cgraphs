From diris.multiparty Require Import langdef.

Inductive val := .
Inductive action := Send (participant : nat) | Recv (participant : nat).

CoInductive prot : Type := {
  (* Tells us if we are allowed to do a particular action at this point,
     and if so, with which values, and how the protocol continues. *)
  message : action -> option (val -> option prot);

  (* Tells us if we are allowed to close at this point *)
  closes : bool
}.

(*
  Version that uses Prop instead of bool.
  Note that all recursive occurrences are positive.
*)
Inductive option' (T : Type) :=
  | Opt (P : Prop) : (P -> T) -> option' T.

CoInductive prot' : Type := {
  message' : action -> option' (val -> option' prot);
  close' : Prop
}.

Variable spec : nat -> Prop.
Check (∃ P, P -> ∃ x:nat, spec x).

Inductive option'' (T : Type) :=
  | Opt' (b : bool) : (b = true -> T) -> option'' T.

Definition pset (A : Type) := A -> Prop.
Definition pmap {A B} (f : A -> B) : pset A -> pset B :=
  λ s b, ∃ a, s a ∧ b = f a.

Lemma foo {A B} (f : A -> B) (s : pset A) :
  ∀ a, s a -> pmap f s (f a).
Proof.
  intros a Ha.
  unfold pmap. eauto.
Qed.

(* Question: can this be generalized to iProp? *)
(* And take a greatest fixed point instead of guarded fixed point? *)

Inductive request := Send (v : val) | Recv.
Inductive response : request -> Type :=
  | RespSend v : response (Send v)
  | RespRecv : val -> response Recv.

CoInductive prot : Type := {
  action : forall r:request, option' (response r -> option' prot)
}.

(* Request-Response r : Action *)
(* Resources: P(r) -∗ Q(r) *)

obj : Object
st : State
act : Action
(↦) : Object -> State -> iProp
pre : State -> Action -> iProp
post : State -> Action -> Value -> iProp
transf : State -> Action -> Value -> State

{ (obj ↦ st) ∗ (pre st act) }
  perform obj act
{ v. (obj ↦ transf st act v) ∗ (post st act v) }


(*
  message : action -> M -> option (val -> M -> option prot);
*)