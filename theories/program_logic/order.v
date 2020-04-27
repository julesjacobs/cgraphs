From iris.proofmode Require Import base tactics classes.

Inductive comparison := LT | GT | EQ.

Fixpoint cmp a b :=
    match a,b with
    | true::a, true::b | false::a, false::b => cmp a b
    | [],[] => EQ
    | false::_, _ | _,true::_ => LT
    | true::_, _ | _,false::_ => GT
    end.

Definition inv_comparison a :=
    match a with
    LT => GT | GT => LT | EQ => EQ
    end.

Lemma cmp_inv a b : cmp a b = inv_comparison (cmp b a).
Proof.
    revert b; induction a; intros; destruct b; destr_bool; auto.
Qed.

Lemma cmp_eq a b : cmp a b = EQ <-> a = b.
Proof.
    revert b; induction a; intros; destruct b; destr_bool;
    rewrite ?IHa; split; intros; simplify_eq; reflexivity.
Qed.

Lemma cmp_app x a b : cmp (x ++ a) (x ++ b) = cmp a b.
Proof.
    induction x; simpl; destr_bool.
Qed.

Definition below x := x ++ [false].
Definition above x := x ++ [true].

Lemma below_cmp x : cmp (below x) x = LT.
Proof.
    replace (cmp (below x) x) with (cmp (x ++ [false]) (x ++ [])).
    { rewrite cmp_app. reflexivity. }
    f_equal. apply app_nil_r.
Qed.