From stdpp Require Export gmap.
Require Export cgraphs.multiparty.langdef.


(* This file contains the definitions of section 5 in the paper. *)



(* The auxiliary definitions of section 5 *)
(* ====================================== *)
(* These are not spelled out in detail in the paper, *)

(* The set of objects in the system (threads and channels), called V in the paper. *)
Inductive object := Thread (_:nat) | Chan (_:session).

(* Stuff required to be able to form finite sets of objects (gset object). *)
Canonical Structure objectO := leibnizO object.
Global Instance object_eqdecision : EqDecision object.
Proof.
  intros [n|n] [m|m]; unfold Decision; destruct (decide (n = m));
  subst; eauto; right; intro; simplify_eq.
Qed.
Global Instance object_countable : Countable object.
Proof.
  refine (inj_countable' (λ l, match l with
  | Thread n => inl n
  | Chan n => inr n
  end) (λ l, match l with
  | inl n => Thread n
  | inr n => Chan n
  end) _); by intros [].
Qed.

(* We define the set of references of expressions, values, buffers, and finally, objects. *)
(* These definitions are not spelled out in the paper, because they are rather boring. *)
Fixpoint expr_refs (e : expr) : gset object :=
  match e with
  | Val v => val_refs v
  | Var x => ∅
  | Pair e1 e2 => expr_refs e1 ∪ expr_refs e2
  | Inj b e1 => expr_refs e1
  | App e1 e2 => expr_refs e1 ∪ expr_refs e2
  | UApp e1 e2 => expr_refs e1 ∪ expr_refs e2
  | Lam s e1 => expr_refs e1
  | ULam s e1 => expr_refs e1
  | Send p e1 i e2 => expr_refs e1 ∪ expr_refs e2
  | Recv p e1 => expr_refs e1
  | Let s e1 e2 => expr_refs e1 ∪ expr_refs e2
  | LetUnit e1 e2 => expr_refs e1 ∪ expr_refs e2
  | LetProd s1 s2 e1 e2 => expr_refs e1 ∪ expr_refs e2
  | MatchVoid e1 => expr_refs e1
  | MatchSum e1 s e2 e3 => expr_refs e1 ∪ expr_refs e2 ∪ expr_refs e3
  | InjN i e => expr_refs e
  | MatchSumN n e f => expr_refs e ∪ fin_union n (expr_refs ∘ f)
  | If e1 e2 e3 => expr_refs e1 ∪ expr_refs e2
  | Spawn n f => fin_union n (expr_refs ∘ f)
  | Close e1 => expr_refs e1
  | Relabel π e1 => expr_refs e1
  end
with val_refs (v : val) : gset object :=
  match v with
  | UnitV => ∅
  | NatV n => ∅
  | PairV v1 v2 => val_refs v1 ∪ val_refs v2
  | InjV b v1 => val_refs v1
  | InjNV i v1 => val_refs v1
  | FunV s e1 => expr_refs e1
  | UFunV s e1 => expr_refs e1
  | ChanV (c,b) _ => {[ Chan c ]}
  end.

Definition map_union `{Countable K, Countable A} {V} (f : V -> gset A) (m : gmap K V) :=
  map_fold (λ k v s, f v ∪ s) ∅ m.

Definition buf_refs (buf : list entryT) := foldr (λ '(i,v) s, val_refs v ∪ s) ∅ buf.

Definition bufs_refs (bufss : bufsT participant participant entryT) : gset object :=
  map_union (map_union buf_refs) bufss.

(* This is the final refs definition we need to formulate the theorems. *)
(* This is simply called `refs` in the paper. *)
Definition obj_refs (es : list expr) (h : heap) (x : object) : gset object :=
  match x with
  | Thread n => from_option expr_refs ∅ (es !! n)
  | Chan c => bufs_refs (gmap_slice h c)
  end.

(* This defines when a thread is blocked on a channel. *)
(* This is spelled blocked_(es,h)(Thread(i),Session(c)) in the paper. *)
Definition thread_blocked (es : list expr) (h : heap) (i c : nat) :=
  ∃ p q k π, ctx k ∧
    es !! i = Some (k (Recv p (Val (ChanV (c,q) π)))) ∧
    is_Some (h !! (c,q)) ∧
    pop (π p) (c,q) h = None.

(* This is the definition of active set. In Coq, we use a predicate rather than a set. *)
(* We have in Coq that `active es h x` holds whenever in the paper `x ∈ active(es,h)`. *)
Definition active (es : list expr) (h : heap) (x : object) :=
  match x with
  | Thread i => ∃ e, es !! i = Some e ∧ e ≠ Val UnitV
  | Chan i => ∃ p, is_Some (h !! (i,p))
  end.


(* The main definitions from section 5 *)
(* =================================== *)

(* Definition 5.1 *)
(*
  A subset [s] of the threads & channels is in a partial deadlock (/ memory leak) if:
  - All of the threads in the subset are blocked on one of the channels in the subset.
  - All of the endpoints of the channels in the subset are held by one of the threads or channels in the subset.
*)
Record deadlock (es : list expr) (h : heap) (s : gset object) := {
  dl_nonempty : s ≠ ∅;
  dl_active x : x ∈ s -> active es h x;
  dl_threadb i : Thread i ∈ s -> ¬ can_stepi i es h;
  dl_threadw i c : Thread i ∈ s -> thread_blocked es h i c -> Chan c ∈ s;
  dl_chan c x : Chan c ∈ s -> Chan c ∈ obj_refs es h x -> x ∈ s
}.

(* Definition 5.2 *)
Definition deadlock_free es h := ∀ s, ¬ deadlock es h s.

(* Definition 5.3 *)
(* A thread is reachable if it can step, or if it is blocked on a reachable channel. *)
(* A channel is reachable if a reachable object holds a reference to it. *)
Inductive reachable (es : list expr) (h : heap) : object → Prop :=
  | Thread_step_reachable i : can_stepi i es h → reachable es h (Thread i)
  | Thread_blocked_reachable i c : reachable es h (Chan c) → thread_blocked es h i c → reachable es h (Thread i)
  | Chan_ref_reachable c x : (Chan c) ∈ obj_refs es h x → reachable es h x → reachable es h (Chan c).

(* Definition 5.4 *)
Definition fully_reachable es h := ∀ x, active es h x -> reachable es h x.