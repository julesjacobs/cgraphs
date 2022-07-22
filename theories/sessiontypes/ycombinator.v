From iris.proofmode Require Import base tactics classes.
From cgraphs.sessiontypes Require Import langdef.

Section ycombinator.
  (* We define the y-combinator for creating recursive functions t1 -> t2. *)
  Variable t1 t2 : type.

  Definition gT := UFunT t1 t2.
  Definition fT := UFunT gT gT.
  CoFixpoint xT := UFunT xT gT.

  Lemma unfold_xT : xT = UFunT xT gT.
    by rewrite <-type_id_id at 1.
  Qed.

  Definition y1 := ULam "x" (UApp (Var "f") (ULam "v" (UApp (UApp (Var "x") (Var "x")) (Var "v")))).
  Definition y := ULam "f" (UApp y1 y1).

  Lemma Var_typed' x xT : typed {[x := xT]} (Var x) xT.
  Proof.
    replace {[x := xT]} with (∅ ∪ {[x := xT]} : envT) by rewrite left_id //.
    eapply Var_typed; eauto.
    eapply Γunrestricted_empty.
  Qed.

  Lemma Γunrestricted_singleton x xT : unrestricted xT -> Γunrestricted {[x := xT]}.
  Proof.
    intros ???. destruct (decide (x = x0)); subst.
    - rewrite lookup_singleton. intros. simplify_eq. done.
    - rewrite lookup_singleton_ne; eauto. intros. simplify_eq.
  Qed.

  Lemma singleton_disj x y xT yT :
    String.eqb x y = false ∨ (xT = yT ∧ unrestricted xT) -> disj {[x := xT]} {[y := yT]}.
  Proof.
    intros ??????.
    eapply lookup_singleton_Some in H0 as [].
    eapply lookup_singleton_Some in H1 as [].
    subst. rewrite String.eqb_refl in H.
    destruct H; simplify_eq. destruct H; subst. eauto.
  Qed.

  Lemma fT_unrestricted : unrestricted fT.
  Proof. constructor. Qed.
  Lemma xT_unrestricted : unrestricted xT.
    rewrite <-type_id_id. constructor.
  Qed.

  Ltac check := eauto using Γunrestricted_singleton, Γunrestricted_empty, fT_unrestricted, xT_unrestricted, singleton_disj.

  Lemma ctx_dup (Γ : envT) : Γ = Γ ∪ Γ.
  Proof.
    eapply map_eq. intro.
    rewrite lookup_union. destruct (_!!_); eauto.
  Qed.

  Lemma y1_typed : typed {[ "f" := fT ]} y1 (UFunT xT gT).
  Proof.
    unfold y1.
    eapply ULam_typed; check.
    eapply UApp_typed; check.
    - eapply Var_typed'.
    - eapply ULam_typed; check.
      eapply UApp_typed; check.
      + rewrite ->ctx_dup at 1.
        eapply UApp_typed; check.
        * rewrite ->unfold_xT at 1. eapply Var_typed'.
        * eapply Var_typed'.
      + eapply Var_typed'.
  Qed.

  Lemma y_typed : typed ∅ y (UFunT fT gT).
  Proof.
    unfold y.
    eapply ULam_typed; check.
    rewrite left_id. rewrite ->ctx_dup at 1.
    eapply UApp_typed; check.
    - eapply y1_typed.
    - rewrite unfold_xT. eapply y1_typed.
  Qed.
End ycombinator.