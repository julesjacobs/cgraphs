From iris.proofmode Require Import base tactics classes.
From diris.multiparty Require Export mutil.
From diris.cgraphs Require Export util.

Definition session := nat.
Definition participant := nat.
Definition endpoint := (session * participant)%type.

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
    | Send : participant -> expr -> expr -> expr
    | Recv : participant -> expr -> expr
    | Let : string -> expr -> expr -> expr
    | LetUnit : expr -> expr -> expr
    | LetProd : string -> string -> expr -> expr -> expr
    | MatchVoid : expr -> expr
    | MatchSum : expr -> string -> expr -> expr -> expr
    | If : expr -> expr -> expr -> expr
    | Spawn n : (fin n -> expr) -> expr
    | Close : expr -> expr.

Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

CoInductive session_type' (T : Type) :=
    | SendT : participant -> T -> session_type' T -> session_type' T
    | RecvT : participant -> T -> session_type' T -> session_type' T
    | EndT : session_type' T.
Arguments SendT {_} _ _ _.
Arguments RecvT {_} _ _ _.
Arguments EndT {_}.
Instance sendt_params : Params (@SendT) 1 := {}.
Instance recvt_params : Params (@RecvT) 1 := {}.

CoInductive session_type_equiv `{Equiv T} : Equiv (session_type' T) :=
    | cteq_EndT : EndT ≡ EndT
    | cteq_SendT t1 t2 s1 s2 p : t1 ≡ t2 -> s1 ≡ s2 -> SendT p t1 s1 ≡ SendT p t2 s2
    | cteq_RecvT t1 t2 s1 s2 p : t1 ≡ t2 -> s1 ≡ s2 -> RecvT p t1 s1 ≡ RecvT p t2 s2.
Existing Instance session_type_equiv.

Lemma session_type_reflexive `{Equiv T} :
    Reflexive (≡@{T}) -> Reflexive (≡@{session_type' T}).
Proof.
    intros ?. cofix IH. intros []; constructor; done.
Defined.

Lemma session_type_symmetric `{Equiv T} :
    Symmetric (≡@{T}) -> Symmetric (≡@{session_type' T}).
Proof.
    intros ?. cofix IH. intros ??[]; constructor; done.
Defined.

Lemma session_type_transitive `{Equiv T} :
    Transitive (≡@{T}) -> Transitive (≡@{session_type' T}).
Proof.
    intros ?. cofix IH. intros ???[]; inversion_clear 1; constructor; by etrans.
Defined.

Global Instance session_type_equivalence `{Equiv T} :
    Equivalence (≡@{T}) -> Equivalence (≡@{session_type' T}).
Proof.
    split.
    - apply session_type_reflexive. apply _.
    - apply session_type_symmetric. apply _.
    - apply session_type_transitive. apply _.
Qed.

Global Instance sendt_proper `{Equiv T} p : Proper ((≡) ==> (≡) ==> (≡)) (@SendT T p).
Proof. by constructor. Qed.
Global Instance recvt_proper `{Equiv T} p : Proper ((≡) ==> (≡) ==> (≡)) (@RecvT T p).
Proof. by constructor. Qed.

Definition session_type_id {T} (s : session_type' T) : session_type' T :=
    match s with
    | SendT p t s' => SendT p t s'
    | RecvT p t s' => RecvT p t s'
    | EndT => EndT
    end.

Lemma session_type_id_id {T} (s : session_type' T) :
    session_type_id s = s.
Proof.
    by destruct s.
Qed.

Lemma session_type_equiv_alt `{Equiv T} (s1 s2 : session_type' T) :
    session_type_id s1 ≡ session_type_id s2 -> s1 ≡ s2.
Proof.
    intros.
    rewrite -(session_type_id_id s1).
    rewrite -(session_type_id_id s2).
    done.
Defined.

Lemma session_type_equiv_end_eq `{Equiv T} (s : session_type' T) :
    s ≡ EndT -> s = EndT.
Proof.
    by inversion 1.
Qed.

Canonical Structure session_type'O (T:ofe) := discreteO (session_type' T).

CoInductive type :=
    | UnitT : type
    | VoidT : type
    | NatT : type
    | PairT : type -> type -> type
    | SumT : type -> type -> type
    | FunT : type -> type -> type
    | UFunT : type -> type -> type
    | ChanT : session_type' type -> type.

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
Existing Instance type_equiv.

Global Instance type_equivalence : Equivalence (≡@{type}).
Proof.
    split.
    - cofix IH. intros []; constructor; done || apply session_type_reflexive, _.
    - cofix IH. intros ??[]; constructor; done || by apply (session_type_symmetric _).
    - cofix IH. intros ???[]; inversion_clear 1; constructor;
      by etrans || by eapply (session_type_transitive _).
Qed.

Canonical Structure typeO := discreteO type.
Notation session_type := (session_type' type).
Notation session_typeO := (session_type'O typeO).

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

Definition consistent n (σs : fin n -> session_type) : Prop.
Admitted.

Record disj_union n (Γ : envT) (fΓ : fin n -> envT) : Prop := {
  du_disj p q : p ≠ q -> disj (fΓ p) (fΓ q);
  du_left p x t : (fΓ p) !! x ≡ Some t -> Γ !! x ≡ Some t;
  du_right x t : Γ !! x ≡ Some t -> ∃ p, (fΓ p) !! x ≡ Some t
}.

Lemma disj_union_Proper_impl n Γ Γ' fΓ :
  Γ ≡ Γ' -> disj_union n Γ fΓ → disj_union n Γ' fΓ.
Proof.
  intros H []. split; eauto; setoid_rewrite <-H; eauto.
Qed.

Instance disj_union_Proper n : Proper ((≡) ==> (=) ==> (≡)) (disj_union n).
Proof.
    intros ??????.
    split; subst; eauto using disj_union_Proper_impl.
    symmetry in H. eauto using disj_union_Proper_impl.
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
    | Send_typed : ∀ Γ1 Γ2 e1 e2 t r p,
        disj Γ1 Γ2 ->
        typed Γ1 e1 (ChanT (SendT p t r)) ->
        typed Γ2 e2 t ->
        typed (Γ1 ∪ Γ2) (Send p e1 e2) (ChanT r)
    | Recv_typed : ∀ Γ e t r p,
        typed Γ e (ChanT (RecvT p t r)) ->
        typed Γ (Recv p e) (PairT (ChanT r) t)
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
    | Spawn_typed : ∀ n Γ fΓ σs f,
        consistent n σs ->
        disj_union n Γ fΓ ->
        (∀ p, typed (fΓ p) (f p) (FunT (ChanT (σs p)) UnitT)) ->
        typed Γ (Spawn n f) UnitT
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
  | Send p e1 e2 => Send p (subst x a e1) (subst x a e2)
  | Recv p e1 => Recv p (subst x a e1)
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
  | Spawn ps f => Spawn ps (λ p, subst x a (f p))
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

Definition heap := gmap endpoint (gmap participant (list val)).

Definition init_chan n : gmap participant (list val) :=
    fin_gmap n (λ i, []).
Definition init_chans n : gmap participant (gmap participant (list val)) :=
    fin_gmap n (λ i, init_chan n).

Definition init_threads (c : session) (n : nat) (fv : fin n -> val) : list expr :=
    fin_list n (λ i, App (Val (fv i)) (Val (ChanV (c, fin_to_nat i)))).

Inductive head_step : expr -> heap -> expr -> heap -> list expr -> Prop :=
    | Pure_step : ∀ e e' h,
        pure_step e e' -> head_step e h e' h []
    | Send_step : ∀ h c p q y, (* p is us, q is the one we send to *)
                               (* send puts the value in the bufs of the other *)
                               (* since we are participant p, we put it in that buffer *)
        head_step (Send q (Val (ChanV (c,p))) (Val y)) h
                  (Val (ChanV (c,p))) (alter (alter (λ buf, buf ++ [y]) p) (c,q) h) []
        (* We could instead to the following:
           (that would move some of the work from the preservation proof to the progress proof.) *)
        (*
        h !! (c,q) = Some bufs ->
        bufs !! p = Some buf ->
        head_step (Send q (Val (ChanV (c,p))) (Val y)) h
                  (Val (ChanV (c,p))) (<[ (c,q) := <[ p := buf ++ [y] ]> bufs ]> h) []
        *)
    | Recv_step : ∀ h c p q y bufs buf, (* p is us, q is the one we recv from *)
        h !! (c,p) = Some bufs -> (* recv takes the value out of its own bufs *)
        bufs !! q = Some (y::buf) -> (* since the recv is from p, we take it out of that buffer *)
        head_step (Recv q (Val (ChanV (c,p)))) h
                  (Val (PairV (ChanV (c,p)) y)) (<[ (c,p) := <[ q := buf ]> bufs ]> h) []
    | Close_step : ∀ c p h,
        (* We can add these conditions: that would move some of the work from the
           preservation proof to the progress proof. *)
        (* h !! (c,p) = Some bufs -> *)
        (* (∀ q, bufs !! q = Some []) -> *)
        head_step (Close (Val (ChanV (c,p)))) h
                  (Val UnitV) (delete (c,p) h) []
    | Spawn_step : ∀ (h : heap) c n f fv,
        (∀ p, h !! (c,p) = None) ->
        (∀ p, f p = Val (fv p)) ->
        head_step
          (Spawn n f) h
          (Val UnitV) (gmap_unslice (init_chans n) c ∪ h)
          (init_threads c n fv).

Inductive ctx1 : (expr -> expr) -> Prop :=
    | Ctx_App_l e : ctx1 (λ x, App x e)
    | Ctx_App_r v : ctx1 (λ x, App (Val v) x)
    | Ctx_Pair_l e : ctx1 (λ x, Pair x e)
    | Ctx_Pair_r v : ctx1 (λ x, Pair (Val v) x)
    | Ctx_Inj b : ctx1 (λ x, Inj b x)
    | Ctx_UApp_l e : ctx1 (λ x, UApp x e)
    | Ctx_UApp_r v : ctx1 (λ x, UApp (Val v) x)
    | Ctx_Send_l p e : ctx1 (λ x, Send p x e)
    | Ctx_Send_r p v : ctx1 (λ x, Send p (Val v) x)
    | Ctx_Recv p : ctx1 (λ x, Recv p x)
    | Ctx_Let s e : ctx1 (λ x, Let s x e)
    | Ctx_LetUnit e : ctx1 (λ x, LetUnit x e)
    | Ctx_LetProd s1 s2 e : ctx1 (λ x, LetProd s1 s2 x e)
    | Ctx_MatchVoid : ctx1 (λ x, MatchVoid x)
    | Ctx_MatchSum s e1 e2 : ctx1 (λ x, MatchSum x s e1 e2)
    | Ctx_If e1 e2 : ctx1 (λ x, If x e1 e2)
    | Ctx_Spawn n (f : fin n -> expr) (p : fin n) :
        ctx1 (λ x, Spawn n (λ q, if decide (p = q) then x else f q))
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