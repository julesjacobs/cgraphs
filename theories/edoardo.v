Require Export Arith String List Omega.
Export ListNotations.
Global Generalizable All Variables.

(*
# Contents

- Inductive data types
- Proofs and tactics
- Data types in canonical representation

# Tactics

Below you can find an overview of the basic tactics of Coq. Most of these
tactics will be discussed in the lecture, but not all. You should carefully read
them and try to use them in the exercises.

## Tactics for basic logic

- `assumption` : the assumption rule of logic, it finishes goals if the goal
   appears among the hypotheses.

   ------------ `assumption`
    H : P |- P

- `intros x` : performs implication or forall introduction.

    H : P |- Q
   ------------ `intros H`
    |- P -> Q

    x : A |- Q x
   ----------------------  `intros x`
    |- forall x : A, Q x

  Note that intros can be chained, e.g. one can write `intros x y H1 H2`.

- `revert` : performs implication or forall elimination (in a way that is in
  opposite direction of `intros`).

     |- P -> Q
    ------------ `revert H`
     H : P |- Q

     |- forall x : A, P x
    ---------------------- `revert x` (if `x` does not appear in any hypothesis)
     x : A |- P x

  This tactic is most commonly used to _generalize the induction hypothesis_,
  i.e. before an induction proof to make sure that the induction hypothesis is
  suitably generalized.

  Note that reverts can be chained, e.g. one can write `revert x y H1`.

- `apply` : performs implication or forall elimination.

     |- Pi a1 .. an          |- Pm a1 .. an
    ---------------------------------------------------------------------------- 'apply H`
     H : forall x1 .. xn, (P1 x1 .. xn) -> ... -> (Pm x1 .. xn) -> (Q x1 .. xn)
     |- Q a0 .. an

- `assert` : performs implication elimination.

     |- P    H : P |- Q
    --------------------  `assert P as H`
           |- Q

- `specialize` : performs forall elimination.

     H : P a |- Q
    ------------------------ `specialize (H a)`
     H : forall x, P x |- Q

  Note that specialize can be chained, e.g. one can write `specialize H a b`

- `split` : performs conjunction introduction.

     |- P1     |- P2
    ----------------- `split`
       |- P1 /\ P2

- `left` : performs (left-) disjunction introduction.

     |- P1
    ------------- `left`
     |- P1 \/ P2

- `right` : performs (right-) disjunction introduction.

     |- P2
    ------------- `right`
     |- P1 \/ P2

- `destruct` performs elimination of inductive types, in particular, it can
  be used for conjunction and disjunction elimination as follows:

  For conjunction elimination:

     H : P1, H2 : P2 |- Q
    ---------------------- `destruct H as [H1 H2]`
     H : P1 /\ P2 |- Q

  For disjunction elimination:

     H : P1 |- Q    H : P2 |- Q
    ---------------------------- `destruct H as [H1|H2]`
     H : P1 \/ P2 |- Q

## Computation

- `simpl` : simplifies the goal by computation. For example, given a goal that
  contains `S x + y` it will turn it into the same goal but with all occurrences
  of `S x + y` replaces by `S (x + y)`.

  Alternatively, an hypothesis `H` can be simplified by computation by writing
  `simpl in H`.

- `unfold` : unfold a definition into its body. For example, when having

    Definition foo := bar.

  Then `unfold foo` will replace all occurrences of `foo` in the goal by `bar.
  As for `simpl`, one can perform the tactic to a hypothesis `H` by writing
  `unfold foo in H`.

## Equality

- `reflexivity` : proves goals of the shape `x = x`

    ------- reflexivity
     x = x

- `discriminate` : discharges goals with an hypothesis of the shape

    --------------------------
     H : c1 ... = c2 ... |- Q

  Where `c1` and `c2` are different constructors (e.g. `true` and `false, or
  `O` and `S`).

- `injection` : performs injectivity of constructors.

   Given the following goal, where `c` is a constructor of an inductive data
   type (for example, `S` or `cons`):

      H1 : x0 = y0, .., Hn : xn = yn |- Q
     ------------------------------------- `injection H as H1 .. Hn`
      H : c x0 .. xn = c y0 .. yn |- Q

- `rewrite` substitutes all occurrences of an equality.

     H : x = y |- Q y
    ------------------ `rewrite H`
     H : x = y |- P x

     H : x = y |- Q x
    ------------------ `rewrite <-H`
     H : x = y |- P y

  The rewrite tactic can also be used in hypotheses, e.g. `rewrite H1 in H2`.

- `f_equal` : proves an equality by proving that all arguments of a function
   are equal.

     |- x0 = y0   ...   |- xn = yn
    ------------------------------- `f_equal`
     |- f x0 .. xn = f y0 ... yn

## Inductive data types

- `destruct` : performs a case analysis. For example, given a natural number
  `n`, one can write `destruct n as [|n']`, which will generate two goals, one
  for the case `n = O` and one for the case `n = S n'`.

- `induction` : performs induction. For example, given a natural number
  `n`, one can write `induction n as [|n' IH]`, which will generate two goals,
  the base case, and the inductive case, in which the induction hypothesis is
  called `IH`.
*)

(* # Introduction *)
(*
The underlying theory of Coq is based on the Calculus of Inductive Constructions
(CIC). CIC is a language that can be used as:

- A typed functional programming language
- A language to represent mathematical statements
- A language to represent proofs

As we will see during the summer school, by the Curry Howard Correspondence, all
of the above concepts are in fact unified, because CIC is a

  higher-order dependently typed programming language

In this lecture, we will not go much into the details of the Curry Howard
Correspondence, but focus more on a practical use of  Coq to formalize
programming language semantics.
*)

(* # Inductive types *)
(*
An important aspect of Coq is to keep the underlying theory, the CIC, small.
This is achieved is not building in the standard data types that we see in
ordinary programming languages, but instead define these data types in terms of
unified constructs. Specifically, in Coq, these data types (and many more) can
be defined by means of inductive types. In the first part of this lecture, I
will give an introduction to inductive types, ans show how these can be used for
programming and proving.

Mote, all of the inductive types that we will define are also in the Coq
standard library. In order to not confuse the standard library results with our
own definitions, we put our own definitions in a module. That way, after we
close the module, we can use the results from the Coq standard library for
subsequent lectures.
*)
Module lecture.

(* ## Booleans *)
(*
Let us start with one of the simplest data types, the Booleans. In Coq, these
can de defined through the following definition:
*)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(*
The lines above introduces a new type called `bool` with _constructors_ `false`
and `true`. Similar to functional programming languages like OCaml and Haskell,
we can now define operations by pattern matching.
*)

Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(*
What makes Coq different from ordinary functional programming languages is that
we can now prove properties about these operations. For example:
*)
Lemma andb_true_l : forall b : bool, andb true b = b.
Proof.
  intros b. (* introduce the forall quantifier, and name the variable b *)
  simpl. (* simplify the goal *)
  reflexivity. (* both side of the equation are equal *)
Qed.

(*
Of course, the above property was rather boring, it followed immediately by
definition of the function `andb`. Proofs like above, are often called _proof by
computation_. Let us now consider something slightly more interesting, where we
will see a new proof technique: proof by _case distinction_.
*)

Lemma andb_true_r : forall b : bool, andb b true = b.
Proof.
  intros b.
  simpl. (* This does not simplify anything, the reason for it is that `andb` is
  defined by pattern matching on the first argument. *)

  (* We are now going to use a new proof technique: _proof by case distinction_.
  In this case, since `b` is of type `bool` we know that it is either `true` or
  `false`. In Coq we can make such a case distinction using the `destruct`
  tactic. *)
  destruct b.
  (* After this, we get two goals: for `true` and for `false. We can use the
  bullets `-`, `+` and `*` to structure the subproofs for these cases. *)
  - (* case `b = true` *)
    simpl.
    reflexivity.
  - (* case `b = false` *)
    simpl.
    reflexivity.
Qed.

(*
Now let us the combination of both proof techniques to prove another result.
*)
Lemma andb_comm : forall b1 b2 : bool, andb b1 b2 = andb b2 b1.
Proof.
  intros b1 b2.
  destruct b1.
  - destruct b2.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
  - destruct b2.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Qed.

(*
As we see, the above proof is pretty lengthy and contains a lot of repetition.
We will now carry out the proof in a shorter and more concise manner.

First observe that our proofs is composed of a sequence of _tactics_ (like
`intros`, `simpl`, `destruct` and `reflexivity`), each of those separated by a
period.  The period executes the tactic, and produces a number of subgoals (or
zero, for example when using `reflexivity`, which are then shown to the user.

Apart from periods, tactics in Coq can also be sequenced using the semicolon
operator:

  tac1; tac2.

The semantics of this kind of sequencing is a bit different than that of
`tac1. tac2.`: it will apply `tac2` to all subgoals generated by `tac1`, and
does not explicitly show goals for the intermediate results. Let us see this
kind of sequencing in action:
*)

Lemma andb_comm_short_proof : forall b1 b2 : bool, andb b1 b2 = andb b2 b1.
Proof.
  intros b1 b2.
  destruct b1; destruct b2; simpl; reflexivity.
Qed.

Lemma andb_assoc : forall b1 b2 b3 : bool,
  andb b1 (andb b2 b3) = andb (andb b1 b2) b3.
Proof.
  intros b1 b2 b3.
  destruct b1; simpl; reflexivity.
(* Question: why do we not need to perform a case analysis on `b2` or `b3`? *)
Qed.

(* # Exercise *)
(*
Prove the following lemmas, first try to prove them using the period as
sequencing operator, and then try to optimize the proof to use the semicolon.
*)
Lemma andb_false_l : forall b : bool, andb false b = false.
Proof. Admitted.

Lemma andb_false_r : forall b : bool, andb b false = false.
Proof. Admitted.

Lemma andb_diag : forall b, andb b b = b.
Proof. Admitted.

Lemma orb_true_l : forall b : bool, orb true b = true.
Proof. Admitted.

Lemma orb_true_r : forall b : bool, orb b true = true.
Proof. Admitted.

Lemma orb_false_l : forall b : bool, orb false b = b.
Proof. Admitted.

Lemma orb_false_r : forall b : bool, orb b false = b.
Proof. Admitted.

Lemma orb_diag : forall b, orb b b = b.
Proof. Admitted.

Lemma orb_comm : forall b1 b2 : bool, orb b1 b2 = orb b2 b1.
Proof. Admitted.

Lemma orb_assoc : forall b1 b2 b3 : bool,
  orb b1 (orb b2 b3) = orb (orb b1 b2) b3.
Proof. Admitted.

Lemma orb_andb_distr : forall b1 b2 b3,
  andb b1 (orb b2 b3) = orb (andb b1 b2) (andb b1 b3).
Proof. Admitted.

(*
So far we have seen two proof techniques: proof by computation (using the
`simpl` tactic) and proof by case distinction (using the `destruct` tactic).
We will now see a new technique: _proof by contradiction_. Before doing that,
let us take  a look at the way logical negation is defined in Coq:

  ~P := P -> False

So, as we see here, in order to prove `~P`, we have to prove that under the
assumption of `P` we can prove `False`, i.e. under the assumption of `P`, we
can prove _anything_.
*)

Lemma true_neq_false : true <> false.
Proof.
  unfold not. (* unfold the definition of negation, which is called `not`, using
  the `unfold` tactic. *)

  intros H. (* introduce the assumption `H : true = false`. *)

  (* But what to do next? So far we have only proved equalities, but now we have
  a contradicting equality as an assumption. The reason that this assumption is
  contradictory is that both sides of the equality involve different
  constructors. If we end up in such a situation, we can use the `discriminate`
  tactic to prove anything (include `False`). *)
  discriminate.
Qed.

Lemma andb_true_inv : forall b1 b2,
  andb b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
  intros b1 b2 H.
  (* Since `andb` is defined by pattern matching on the first argument, we
  perform a case analysis on `b1`. *)
  destruct b1.
  - (* case `b1 = true` *)
    simpl in H. (* The `simpl` tactic can also be used to simplify hypotheses.
    We use it to turn `H : andb true b2 = true` into `H : b2 = true`. *)
    split. (* conjunctions can be introduced using the `split` tactic *)
    + reflexivity.
    + assumption. (* This goal precisely matches a hypothesis, so we can use the
      `assumption` tactic. *)
  - (* case `b1 = false` *)
    (* Like in the first case, we proceed by simplifying `H`. *)
    simpl in H.
    (* This yields `false = true`, which is contradictory. We can now thus use
    the `discriminate` tactic to discharge the goal. *)
    discriminate.
Qed.

(*
Let us take a look at another example, for which we will define the XOR
operation on Booleans, which is true iff exactly one of the arguments is true.
*)
Definition xorb (b1 b2 : bool) :  bool :=
  match b1, b2 with
  | true, false => true
  | false, true => true
  | _, _ => false
  end.

Lemma xorb_inj_l : forall b1 b2 b3 : bool,
  xorb b1 b2 = xorb b1 b3 -> b2 = b3.
Proof.
  intros b1 b2 b3 H.
  (* Since xor is defined by pattern matching on both arguments, we proceed
  by making a case distinction on all Boolean variables. *)
  destruct b1, b2, b3; simpl in H.
  (* This gives `2^3 = 8`, but as we can see, these can be classified into
  two kinds:
  - Trivial goals: `true = true` and `false = false`.
  - Contradictory goals, where we have either the hypothesis `false = true` or
    `true = false`.
  Of course, we could prove each of these goals individually, but that gets
  pretty boring. So, instead we will make use of of another tactic combinator:

    tac1 || tac2

  This operator will try to run the tactic `tac1` and in case it fails, it will
  run `tac2` instead.
  *)

Restart. (* Let us start over *)

  intros b1 b2 b3 H.
  destruct b1, b2, b3; simpl in H; discriminate || reflexivity.
Qed.

(* ### Exercises *)
(* Prove the following lemmas. Note that one can "cheat" by finishing proofs
with the `Admitted` command. We do this for exercises, and the idea is that
you finish the proofs. *)
Lemma xorb_diag_is_true : forall b : bool, xorb b b = b -> b = false.
Proof. Admitted.

Lemma orb_false_inv : forall b1 b2 : bool,
  orb b1 b2 = false -> b1 = false /\ b2 = false.
Proof. Admitted.

Lemma xorb_comm : forall b1 b2, xorb b1 b2 = xorb b2 b1.
Proof. Admitted.

Lemma xorb_assoc : forall b1 b2 b3 : bool,
  xorb b1 (xorb b2 b3) = xorb (xorb b1 b2) b3.
Proof. Admitted.

Lemma xorb_true_inv : forall b1 b2 : bool,
  xorb b1 b2 = true -> b1 <> b2.
Proof. Admitted.

Lemma xorb_false_inv : forall b1 b2 : bool,
  xorb b1 b2 = false -> b1 = b2.
Proof. Admitted.

(* ## Natural numbers *)
Module nat_defs.
(*
Another very commonly used data type is the natural numbers 0, 1, 2, 3, ... Ome
can define the natural numbers `nat` in Coq as the Peano numerals:
*)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(*
The type `nat` has two constructors, `O`, which represents the natural number
`0`, and the constructor `S n`, which represents the natural number `n + 1`.
Using this data type, we can construct any natural number, for example:

  1 = S O
  2 = S (S O)
  3 = S (S (S O))
  4 = S (S (S (S O)))

And so on. What is different from the type `bool` of Booleans, that we have just
seen, is that the `nat` is _recursive_: the constructor `S` has an argument of
type `nat`.

An important feature of recursive inductive types in Coq is that we can define
functions by structural recursion, for example:
*)

Fixpoint plus (n1 n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S n1' => S (plus n1' n2)
  end.

(*
The above function implements addition of Peano natural numbers, simply by
merging together the `S` constructors.

It is important to note that the function is structurally recursive on the
argument `n1`, i.e. the size of the argument `n1` reduces in each recursive
call. For reasons of soundness of the logic, all functions in Coq should be
total. Since it is undecidable to check whether a function is total, Coq imposes
this restriction by requiring each recursive function to be structurally
recursive. The following definitions are thus not allowed:
*)

Fail Fixpoint foo (n : nat) := S (foo n).
Fail Fixpoint bar (n : nat) := S (bar (S n)).

(*
Both of these attempts result in the error:

  Recursive call to foo has principal argument equal to "n" instead of
  a sub-term of "n".

Indeed, this function would not terminate, try to simplify `foo 0`, for example.

In similar style as we have defined addition, we can define multiplication. Note
that this function is structurally recursive in its first argument, and thus Coq
allows it. *)
Fixpoint mult (n1 n2 : nat) : nat :=
  match n1 with
  | O => O
  | S n1' => plus n2 (mult n1' n2)
  end.
End nat_defs.

(*
Now that we have defined some operations on natural numbers, let us try to see
whether we can prove some properties about them.

Note that since we closed the module `nat_defs` above, its content is hidden,
which allows us to use the natural numbers from Coq's instead. For these we have
the usual notations, like `0`, `1`, `2`, and so on for the literals, and `+`
and `*` for the addition and multiplication.
*)

Lemma plus_0_l : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

(*
This proof was simple: since `plus` is defined by recursion on the first
argument, we can just prove the lemma by computation. Now let us try the version
with 0 for the second argument.
*)

Lemma plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n.
  simpl. (* Does not do anything, there is no constructor in match position *)

  (* We could try to proceed by case distinction on n, which is done using
  the destruct tactic. The syntax `as [|n']` is used to name the argument of
  the constructor `S`. *)
  destruct n as [|n'].
  - simpl. reflexivity. (* So good so far. *)
  - simpl. (* Now we end up with `S (n' + 0) = S n'`, which did not make the
    situation much better. We quite clearly need something more here... *)

Restart.
  intros n.

  (* Perform proof by induction. *)
  induction n as [|n' IH].
  - simpl. reflexivity.
  - simpl.
    rewrite IH. (* replaces the LHS of `IH : n' + 0 = n` with the RHS. *)

    (* Now we have the same goal as before, but with the additional hypothesis

      IH : n' + 0 = n'

    That is to say, we now that the property holds for the smaller natural
    number `n'`. Thus gives us enough information to finish the proof. *)
    reflexivity.
Qed.

(*
In summary, in the above we have seen two new techniques:

- _Proof by induction_ : using the tactic `induction n as [|n IH]` we can
  perform induction on a natural number `n`. It will produce two subgoals, one
  for the base case, and one for the inductive case. The induction hypothesis
  will be called `IH`.
- _Proof by rewriting_ : using the tactic `rewrite H` we can substitute an
  equality `H : x = y` into the goal.
*)

Lemma plus_S_r : forall n1 n2, n1 + S n2 = S (n1 + n2).
Proof.
  intros n1 n2.
  induction n1 as [|n1 IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.

Restart.

(*
Instead of `rewrite`, we will now demonstrate another tactic: `f_equal`, which
makes use of the fact that `p = q` implies `S p = S q`.
*)

  intros n1 n2.
  induction n1 as [|n1 IH].
  - simpl. reflexivity.
  - simpl.
    f_equal.
    assumption.
Qed.

(*
Think carefully on which argument we should do induction.
*)
Lemma plus_assoc : forall n1 n2 n3 : nat,
  n1 + (n2 + n3) = (n1 + n2) + n3.
Proof.
  intros n1 n2 n3.
  induction n1 as [|n1 IH].
  - simpl. reflexivity.
  - simpl. f_equal. assumption.
Qed.

(*
In the below, we will see that we can reuse lemmas that we have proved before.
This is important, as otherwise proofs become quickly unmanageable.
*)
Lemma plus_comm : forall n1 n2 : nat, n1 + n2 = n2 + n1.
Proof.
  intros n1 n2.
  induction n1 as [|n1 IH].
  - simpl.
    rewrite plus_0_r. (* The goal `n2 = n2 + 0` is an instance of the lemma
    `plus_0_r` that we proved before. We can use the `rewrite` tactic not just
    with hypotheses, but also with lemmas. *)
    reflexivity.
  - simpl.
    rewrite plus_S_r. (* In this case, we make use of the lemma `plus_S_r` that
    we just proved. *)
    rewrite IH. reflexivity.
Qed.

(*
Now that we have seen some proofs by induction, the `induction` tactic may seem
like a good opportunity to prove any lemma. However, that is not always a good
idea. As the lemma that we consider next will show, reuse of lemmas, instead of
blindly performing induction, is very important. The lemma below can be proven
simply by making use of the properties we have proven so far: associativity and
commutativity of addition.
*)
Lemma plus_rearrange : forall n m p q : nat,
  (n + m) + p + q = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* The situation here becomes a bit tricky: if we would just write
  `rewrite plus_comm` it will trigger the rewrite at some arbitrary position in
  the goal. More precisely, since `plus_comm` is university quantified:

    plus_comm : forall n1 n2 : nat, n1 + n2 = n2 + n1

  It fits any occurrence of plus in the goal. To work around that, we first
  specialize the lemma, and then rewrite. This is done by partially applying the
  lemma, as shown below. *)
  rewrite (plus_comm n).

  (* For associativity we have the same problem, so we perform the same trick. *)
  rewrite (plus_assoc (m + n)).

  reflexivity.
Qed.

(*
To convince yourself, you could give it a try to prove the lemma above by
induction, and you will see that it gets very difficult.
*)

(*
In order to practice some more with proof by induction, we will now define the
function `beq_nat : nat -> nat -> bool` that computes whether two natural
numbers are equal.

Note that this function is very different from the equality `=`, which is a
statement in logic/mathematics, and not a computable function. (The type of
`n1 = n2` is `Prop`, Coq's type of propositions, whereas the type of
`beq_nat n1 n2` is `bool`. We will prove:

  n1 = n2 <-> beq_nat n1 n2 = true
*)
Fixpoint beq_nat (n1 n2 : nat) : bool :=
  match n1, n2 with
  | O, O => true
  | S n1', S n2' => beq_nat n1' n2'
  | _, _ => false
  end.

(*
For proving the left to right direction, we first introduce a helper lemma.
*)
Lemma beq_nat_refl : forall n : nat, beq_nat n n = true.
Proof.
  intros n.
  induction n as [|n IH].
  - simpl. reflexivity.
  - simpl. assumption.
Qed.

Lemma eq_beq_nat : forall n1 n2, n1 = n2 -> beq_nat n1 n2 = true.
Proof.
  intros n1 n2 H.
  rewrite H.
  rewrite beq_nat_refl.
  reflexivity.
Qed.

(*
The right to left direction will be a but more involved, as we will see.
*)
Lemma beq_nat_eq : forall n1 n2, beq_nat n1 n2 = true -> n1 = n2.
Proof.
  intros n1 n2 H.
  induction n1 as [|n1 IH].
  - simpl in H. destruct n2 as [|n2].
    + reflexivity.
    + discriminate.
  - simpl in H. destruct n2 as [|n2].
    + discriminate.
    + (* Now we have to prove `S n1 = S n2`, but our induction hypothesis

        IH : beq_nat n1 (S n2) = true -> n1 = S n2

      Does not really help; it is too weak. If we look at the definition of
      `beq_nat` we see that `n2` also decreases in each recursive call. In our
      proof, we however fixed `n2` before doing the induction, and to that end,
      the induction hypothesis is too specific.  *)

Restart.

  intros n1 n2 H.
  revert n2 H. (* We fix this problem by generalizing over `n2` and `H` before
  performing the induction. As we will see, that will give a stronger induction
  hypothesis that applies to any `n2`. Generalization is done using Coq's
  `revert` tactic. *)
  induction n1 as [|n1 IH].
  - intros n2 H.
    simpl in H. destruct n2 as [|n2].
    + reflexivity.
    + discriminate.
  - intros n2 H.
    simpl in H. destruct n2 as [|n2].
    + discriminate.
    + (* Now we see that the induction hypothesis is:

         IH : forall n2 : nat, beq_nat n1 n2 = true -> n1 = n2

      This suffices to prove the goal. *)
      f_equal. apply IH. assumption.
Qed.

(*
The technique of generalizing the goal before performing induction is called
_generalizing the induction hypothesis_. It is often needed.

In the following lemma, we demonstrate Coq's `injection` tactic, which
simplifies a hypothesis using injectivity of constructors. *)
Lemma plus_inj_l : forall n1 n2 n3 : nat,
  n1 + n2 = n1 + n3 -> n2 = n3.
Proof.
  intros n1 n2 n3 H. induction n1 as [|n1 IH].
  - simpl in H.
    assumption.
  - simpl in H.
    apply IH.
    injection H as H. (* The `injection` tactic applies the fact that
    constructors of inductive data types are injective. For the case of natural
    numbers that means:

      S p = S q -> p = q

    *)
    assumption.
Qed.

(* ### Exercise (easy to moderate) *)
(*
Prove the lemmas below.  For each of the lemmas carefully take into account:
- Can you derive it from results you have proven already?
- If not, do you have to perform induction? If so, on which variable?
- Do you need to generalize the induction hypothesis?
*)
Lemma mult_0_l : forall n,
  0 * n = 0.
Proof. Admitted.

Lemma mult_0_r : forall n,
  n * 0 = 0.
Proof. Admitted.

Lemma plus_swap : forall n1 n2 n3 : nat,
  n1 + (n2 + n3) = n2 + (n1 + n3).
Proof. Admitted.

Lemma mult_S_r : forall n1 n2 : nat,
  n1 * S n2 = n1 + n1 * n2.
Proof. Admitted.


Lemma mult_comm : forall n1 n2 : nat,
  n1 * n2 = n2 * n1.
Proof. Admitted.


Lemma plus_mult_distr_l : forall n1 n2 n3 : nat,
  (n1 + n2) * n3 = n1 * n3 + n2 * n3.
Proof. Admitted.


Lemma mult_assoc : forall n1 n2 n3 : nat,
  n1 * (n2 * n3) = (n1 * n2) * n3.
Proof. Admitted.

Lemma double_inj : forall n m,
  n + n = m + m ->
  n = m.
Proof. Admitted.

Lemma plus_inj_r : forall n1 n2 n3 : nat,
  n1 + n3 = n2 + n3 -> n1 = n2.
Proof. Admitted.

(* ### Exercise (easy) *)
(*
Recall the mathematical definition of the factorial function:

    factorial(0) = 1
    factorial(n) = n * factorial(n - 1)     (if n > 0)

Translate this into a corresponding function in Coq.
*)

(*
Fixpoint factorial (n : nat) : nat :=
  ...
*)

(* ### Exercise (moderate) *)
(*
A small island in the middle of the Pacific Ocean has coins of just two values:

- 3 cents
- 5 cents

It is claimed that using any amount of 8 cents or more can be composed of a
combination of these 3 cent and 5 cent coins. Prove this.

Hint: in this proof you may use the `omega` tactic, which solves goals involving
propositional logic, the operations `=` and `+`, and multiplication by constant
natural numbers.
*)

Lemma coin_problem : forall x, exists y z, x + 8 = 3 * y + 5 * z.
Admitted.
End lecture.

(* # Advanced data structures *)
(* ## Finite maps *)
(*
In the last part of this course we will look into a way of representing finite
maps (aka finite partial functions) from natural numbers to elements of some
type `A`. This means that we want to define a type `map A` and the following
operations:

  mlookup : map A -> nat -> option A
  mempty : map A
  msingleton : nat -> A -> map A
  minsert : nat -> A -> map A -> map A
  mdelete : nat -> map A -> map A

These operations should enjoy their expected properties, for example:

  mlookup (minsert i y m) i = Some y
  i <> j -> mlookup (minsert i y m) j = mlookup m j

The naive way of encoding finite maps is by means of association lists, i.e. as
lists of key value lists. In Coq that would be:
*)

Definition assoc_list (A : Type) : Type := list (prod nat A).

Print prod.
(*
Inductive prod (A B : Type) : Type :=
  | pair : A -> B -> A * B
*)

Print list.
(*
Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A
*)

(*
However, this encoding is not ideal, and suffers from some problems. First of
all, the same finite maps can be represented by different association lists.
For example, the map `0 |-> a, 3 |-> b` can be represented by the following
association lists:

  [(0,a); (3,b)]
  [(3,b); (0,a)]

This situation is not desired, since it means that the following property does
_not_ hold:

  m1 = m2 <-> forall i, mlookup m1 i = mlookup m2 i

To see that it does not hold, take

  m1 = [(0,a); (3,b)]
  m2 = [(3,b); (0,a)]

Now it is clear to see that the property does not hold.

Similarly, another issue of the representation through association lists is that
the same key could appear multiple times in the same association list, e.g.:

  [(0,a); (0,b)]

When implementing `mlookup` we have to make an arbitrary choice with key/value
pair to pick. Also, other operations get a bit tricky on how to consider
duplicate key pairs.

So, a natural question comes up:

  Can we represent finite maps in a different way so that these problems
  fo not occur?

As we will see, the answer is "yes". To get there, let's first take a look at
another attempt:
*)

Definition map_raw (A : Type) := list (option A).

Print option.
(*
Inductive option (A : Type) : Type :=
  | Some : A -> option A
  | None : option A
*)

(*
The idea of this representation is that at each index `i` of the list we have
`Some a` iff `i |-> a` is in the map, and use `None`s for unused positions. For
example, we represent the map `0 |-> a, 3 |-> b` as

  [Some a; None; None; Some b]

With the above representation of finite maps in hand, we can now define the
lookup function as:
*)

Fixpoint mlookup_raw {A} (m : map_raw A) (i : nat) : option A :=
  match m with
  | nil => None
  | x :: m =>
     match i with
     | 0 => x
     | S i => mlookup_raw m i
     end
  end.

(*
This new representation solves the problem of duplicate keys value pairs, simply
because at each position in the list, there can be at most one value. However,
this representation still suffers from the problem that there are duplicate
representations of the same map. For example, the map in the previous example
could also be represented by:

  [Some a; None; None; Some b; None]
  [Some a; None; None; Some b; None; None]

So, in order to have the property

  m1 = m2 <-> forall i, mlookup m1 i = mlookup m2 i

We have to make sure that there is no sequence of `None`s at the end of the
list. We will do this by considering the "subtype of `raw_map`s that do not have
a sequence of `None`s at the end". But how to represent subtypes in Coq? As
we will see below, we do this as follows:

1. Define a predicate that carved out the _well-formed_ `raw_map`s, i.e. those
   that do not have a sequence of `None`s at the end.
2. Construct the subtype of _well-formed` `raw_map`s.

Before going into details about the second point, we will first define the
well-formedness predicate. For reasons that will become apparent later, we do
this by defining a Boolean function `map_wf`:
*)

Definition is_Some {A} (x : option A) : bool :=
  match x with
  | Some _ => true
  | None => false
  end.

Fixpoint map_wf {A} (may_be_nil : bool) (m : map_raw A) : bool :=
  match m with
  | [] => may_be_nil
  | x :: m => map_wf (is_Some x) m
  end.

(*
We use the parameter `may_be_nil` to keep track of whether the previous element
was a `Some`. Only if that is the case, the list may be `nil`.

Now, to define our actual `map` type, we want to consider the elements of type
`map_raw` that are well-formed. We achieve this by defining a dependently typed
record that consists of:

- The raw map `m : map_raw`
- A proof that the raw map `m` is well-formed.

The second becomes part is a bit more subtle. We have defined the well-formedness
predicate as a Boolean function, whereas proofs in Coq as of type `Prop`. To
make things work, we thus need to turn the Boolean into a `Prop`. We do this by
defining a function `is_True : bool -> Prop`:
*)

Coercion is_True (b : bool) : Prop :=
  if b then True else False.

(*
The keyword `Coercion` is used to instruct Coq to automatically insert the
function whenever it sees a `bool` but needs a `Prop`. We can now for example
write things like:
*)

Check (true : Prop).
Check (true /\ 0 = 0).

(*
When we instruct Coq to display coercions (by setting `Set Printing Coercions`),
we see that the above terms actually expand to:

  is_True true : Prop
  is_True true /\ 0 = 0

With the coercion `is_True` in hand, we can now define the dependently typed
record as follows:
*)

Record map (A : Type) := make_map {
  map_car : map_raw A;
  map_prf : map_wf true map_car
}.

(*
Now let is take a look at the record `map` that we have just defined. As part of
this, we get a constructor:

  make_map : forall (A : Type) (m : map_raw A), map_wf true m -> map A

And two projections to get out the raw map and the proof, respectively:

  map_car : forall (A : Type), map A -> map_raw A
  map_prf : forall (A : Type) (m : map A), map_wf true (map_car A m)

The following commands make sure that the type argument `A` becomes implicit,
so that we do not have to write it explicitly all the time.
*)
Arguments make_map {_} _ _.
Arguments map_car {_} _.
Arguments map_prf {_} _.

(*
With the projection `map_car` in hands, it is straightforward to lift the
function `mlookup_raw` to the record `map` of raw maps together with a proof of
well-formedness: we just project out the raw map:
*)
Definition mlookup {A} (m : map A) (i : nat) : option A :=
  mlookup_raw (map_car m) i.

(*
Now that we have the type of maps defined, and the basic operation for looking
up elements in place, we will start by proving the desired property:

  (forall i, mlookup m1 i = mlookup m2 i) -> m1 = m2

We will do this in two stages:

1. Lemma `map_raw_eq`: Prove that for any `m1 m2 : raw_map A` we have

     map_wf b m1 ->
     map_wf b m2 ->
     (forall i, mlookup_raw m1 i = mlookup_raw m2 i) ->
     m1 = m2

2. Lemma `map_eq`: Show that the desired property follows from (1).
*)

(*
Stage 1: We prove the property by induction on one of the raw maps, followed by
a case distinction on the other. We can pick either `m1` or `m2` for the
induction, because the choice does not really matter by symmetry, after all.

For the base cases, we will first prove the helper lemma `map_wf_nil` as below.
This lemma states that whenever we have a well-formed raw map, and looking up
always yields `None`, then the raw map should be nil. This property is proven
by induction.
*)
Lemma map_wf_nil {A} (b : bool) (m : map_raw A) :
  map_wf b m ->
  (forall i, mlookup_raw m i = None) ->
  m = [].
Proof.
  revert b. induction m as [|x m2 IH]; intros b Hwf Hlookup; simpl in *.
  - reflexivity.
  - assert (m2 = []).
    { apply (IH (is_Some x)). apply Hwf. intros i. apply (Hlookup (S i)). }
    subst m2.
    assert (x = None).
    { apply (Hlookup 0). }
    subst x.
    simpl in *.
    destruct Hwf.
Qed.

(*
We can now prove the actual property for raw maps. Remember to use the above
helper lemma in the base cases.
*)
Lemma map_raw_eq {A} (b : bool) (m1 m2 : map_raw A) :
  map_wf b m1 ->
  map_wf b m2 ->
  (forall i, mlookup_raw m1 i = mlookup_raw m2 i) -> m1 = m2.
Proof.
  revert b m2.
  induction m1 as [|x m1 IH]; intros b m2 Hm1 Hm2 Hlookup.
  - symmetry. apply (map_wf_nil b).
    + apply Hm2.
    + simpl in *. intros i. symmetry. apply Hlookup.
  - destruct m2 as [|y m2].
    + apply (map_wf_nil b). assumption. assumption.
    + assert (x = y).
      { apply (Hlookup 0). }
      subst. simpl in *. f_equal.
      apply (IH (is_Some y)). assumption. assumption.
      intros i. apply (Hlookup (S i)).
Qed.

(*
Stage 2: We will prove the property for maps, that is:

  (forall i, mlookup m1 i = mlookup m2 i) -> m1 = m2

Unfortunately, even while having the helping lemma `map_raw_eq` that we just
proved at hand, this direction still does not follow immediately. The problem
is that maps are essentially tuples

  m : raw_map A
  H : is_True (map_car true m)

Now if we want to establish that two maps `(m1,H1)` and `(m2,H2)` are equal, we
do not just have to show that the underlying raw maps `m1` and `m2` are equal
(which we obtain from `map_raw_eq`), but we also have to show that the proofs
`H1` and `H2` are equal. So, concretely, after using the equality that `m1` and
`m2` are equal, we have to show that given:

  m1 : map_raw A
  H1 : is_True (map_car true m1)
  H2 : is_True (map_car true m1)

We have to show `H1 = H2`. Intuitively, this may sound obvious, but it is not.
As you will see in the Homotopy Type Theory lectures, the property below, which
is typically refered to as _proof irrelevance_ does in general not hold:

  forall (P : Prop) (H1 H2 : P), H1 = H2

Fortunately, in our case we are lucky, we are not considering an arbitrary
proposition `P`, but something of the shape `is_True b`. Due to that, we can
actually prove this property by making a case analysis on `b`:
*)
Lemma is_True_proof_irrel (b : bool) (H1 H2 : is_True b) :
  H1 = H2.
Proof.
  destruct b; simpl in *.
  - (* Now we `H1, H2 : True`. By a simple case analysis, we can show that
    each proof of `True` is equal to `I`, the constructor of `True`. By
    Curry-Howard, think of `True` as the unit type, and indeed, the only
    constructor of the unit type is `tt`. *)
    destruct H1. destruct H2. reflexivity.
  - (* Now we have `H1, H2 : False`. This is a contradiction. *)
    destruct H1.
Qed.

(*
The desired property, but written as a bi-implication so that we also have the
opposite direction. Note that the opposite direction of is trivial: we rewrite
the equality and use reflexivity.
*)
Lemma map_eq {A} (m1 m2 : map A) :
  m1 = m2 <-> forall i, mlookup m1 i = mlookup m2 i.
Proof.
  split.
  - intros ->. reflexivity.
  - unfold mlookup. intros Hlookup.
    destruct m1 as [m1 H1], m2 as [m2 H2]; simpl in *.
    assert (m1 = m2).
    { apply (map_raw_eq true). apply H1. apply H2. apply Hlookup. }
    subst m2.
    f_equal. apply is_True_proof_irrel.
Qed.

(*
So, the take home message is that when we want to represent subtypes and have
sensible results for equality we should:

1. Define a Boolean-valued predicate that expresses well-formedness.
2. Define a dependently typed record that includes a proof of well-formedness.

The use of a Boolean-valued well-formedness predicate is crucial: it ensures that
any any two proofs of the well-formedness property are equal, as we have proven
in the lemma `is_True_proof_irrel`. *)

(*
## Operations on maps

We will now proceed to define all of the map operations, namely:

  mempty : map A
  msingleton : nat -> A -> map A
  minsert : nat -> A -> map A -> map A
  mdelete : nat -> map A -> map A

The definitions of all of these operations proceeds in the following way:

1. Define the operation on raw maps.
2. Prove that the operation on raw maps preserves well-formedness.
3. Lift the operation from raw maps to maps.
4. Prove the desired properties involving `mlookup_raw` on raw maps.
5. Lift those properties to a version involving `mlookup`.
*)

(* ## The empty map *)

Definition mempty_raw {A} : map_raw A := nil.

Lemma mempty_raw_wf {A} : map_wf true (@mempty_raw A).
Proof. simpl. constructor. Qed.

Definition mempty {A} : map A := make_map mempty_raw mempty_raw_wf.

Lemma mempty_raw_lookup {A} (i : nat) : mlookup_raw (@mempty_raw A) i = None.
Proof. simpl. reflexivity. Qed.

Lemma mempty_lookup {A} (i : nat) : mlookup (@mempty A) i = None.
Proof. unfold mlookup, mempty, map_car. apply mempty_raw_lookup. Qed.

(* ## The singleton operation *)

Fixpoint msingleton_raw {A} (i : nat) (y : A) : map_raw A :=
  match i with
  | 0 => [Some y]
  | S i => None :: msingleton_raw i y
  end.

(* ### Exercise *)
(*
Prove the properties of `msingleton` below.
*)
Lemma msingleton_raw_wf {A} (b : bool) (i : nat) (y : A) :
  map_wf b (msingleton_raw i y).
Proof. Admitted.

Definition msingleton {A} (i : nat) (x : A) : map A :=
  make_map (msingleton_raw i x) (msingleton_raw_wf true i x).

Lemma msingleton_raw_lookup {A} (i : nat) (y : A) :
  mlookup_raw (msingleton_raw i y) i = Some y.
Proof. Admitted.

Lemma msingleton_raw_lookup_ne {A} (i j : nat) (y : A) :
  i <> j -> mlookup_raw (msingleton_raw i y) j = None.
Proof.
  revert i. induction j; intros i; destruct i; simpl in *; eauto.
  intros []; eauto.
Admitted.

Lemma msingleton_lookup {A} (i : nat) (y : A) :
  mlookup (msingleton i y) i = Some y.
Proof.
  induction i; eauto.
Admitted.

Lemma msingleton_lookup_ne {A} (i j : nat) (y : A) :
  i <> j -> mlookup (msingleton i y) j = None.
Proof. Admitted.

(* ## The insert operation *)

Fixpoint minsert_raw {A} (i : nat) (y : A) (m : map_raw A) {struct m} : map_raw A :=
  match m with
  | [] => msingleton_raw i y
  | x :: m =>
    match i with
    | 0 => Some y :: m
    | S i => x :: minsert_raw i y m
    end
  end.

(* ### Exercise *)
(*
Prove the properties of `minsert` below.
*)
Lemma map_wf_mono {A} (b : bool) (m : map_raw A) : map_wf b m -> map_wf true m.
Proof.
  destruct b; eauto.
  induction m; eauto.
  simpl. eauto.
Qed.

Lemma minsert_raw_wf {A} (b : bool) (i : nat) (y : A) (m : map_raw A) :
  map_wf b m -> map_wf b (minsert_raw i y m).
Proof.
  revert m b. induction i; intros m b.
  - destruct m; simpl.
    + eauto.
    + destruct o; simpl; eauto using map_wf_mono.
  - intros H. destruct m; simpl; eauto using msingleton_raw_wf.
Qed.

Definition minsert {A} (i : nat) (x : A) (m : map A) : map A :=
  match m with
  | make_map m Hm => make_map (minsert_raw i x m) (minsert_raw_wf true i x m Hm)
  end.

Lemma minsert_raw_lookup {A} (i : nat) (y : A) (m : map_raw A) :
  mlookup_raw (minsert_raw i y m) i = Some y.
Proof. Admitted.

Lemma minsert_raw_lookup_ne {A} (i j : nat) (y : A) (m : map_raw A) :
  i <> j ->
  mlookup_raw (minsert_raw i y m) j = mlookup_raw m j.
Proof.
  revert j i. induction m; destruct i; destruct j; simpl; eauto.
  - intros. exfalso. eauto.
  - intros H. apply msingleton_raw_lookup_ne. omega.
  - intros. exfalso. eauto.
Qed.

Lemma minsert_lookup {A} (i : nat) (y : A) (m : map A) :
  mlookup (minsert i y m) i = Some y.
Proof. Admitted.

Lemma minsert_lookup_ne {A} (i j : nat) (y : A) (m : map A) :
  i <> j ->
  mlookup (minsert i y m) j = mlookup m j.
Proof. Admitted.

(* ## The delete operation *)
Fixpoint mcons {A} (x : option A) (m : map_raw A) : map_raw A :=
  match x with
  | None =>
     match m with
     | [] => []
     | _ => None :: m
     end
  | _ => x :: m
  end.

Fixpoint mdelete_raw {A} (i : nat) (m : map_raw A) {struct m} : map_raw A :=
  match m with
  | [] => []
  | x :: m =>
    match i with
    | 0 => mcons None m
    | S i => mcons x (mdelete_raw i m)
    end
  end.

Lemma mcons_lookup_0 {A} (x : option A) (m : map_raw A) :
  mlookup_raw (mcons x m) 0 = x.
Proof. destruct x, m; reflexivity. Qed.

Lemma mcons_lookup_S {A} (x : option A) (m : map_raw A) (i : nat) :
  mlookup_raw (mcons x m) (S i) = mlookup_raw m i.
Proof. destruct x, m; reflexivity. Qed.

Arguments mcons : simpl never.
(* The `Arguments`command with the `simpl never` flag makes sure that `simpl`
does not unfold `mcons`. This will make some proofs easier, as we rather rewrite
using the lemmas `mcons_lookup_0` and `mcons_lookup_S` to avoid matches to
appear in the goal. *)

Lemma mcons_wf {A} (b : bool) (x : option A) (m : map_raw A) :
  map_wf b m -> map_wf b (mcons x m).
Proof. destruct m, x; simpl; auto. Qed.

(* ### Exercise *)
(*
Prove the properties of `mdelete` below.
*)
Lemma mdelete_raw_wf {A} (b : bool) (i : nat) (m : map_raw A) :
  map_wf b m -> map_wf true (mdelete_raw i m).
Proof.
  revert i b. induction m; simpl; eauto; intros i b.
  destruct i; eauto using mcons_wf, map_wf_mono.
Admitted.

Definition mdelete {A} (i : nat) (m : map A) : map A :=
  match m with
  | make_map m Hm => make_map (mdelete_raw i m) (mdelete_raw_wf true i m Hm)
  end.

Lemma mdelete_raw_lookup {A} (i : nat) (m : map_raw A) :
  mlookup_raw (mdelete_raw i m) i = None.
Proof. Admitted.

Lemma mdelete_raw_lookup_ne {A} (i j : nat) (m : map_raw A) :
  i <> j ->
  mlookup_raw (mdelete_raw i m) j = mlookup_raw m j.
Proof.
  revert i j. induction m; intros i j; destruct i,j; simpl; eauto.
  - intros H. exfalso. eauto.
  - intros _. rewrite mcons_lookup_S. reflexivity.
  - intros _. rewrite mcons_lookup_0. reflexivity.
  - intros H. rewrite mcons_lookup_S. apply IHm. eauto.
Admitted.

Lemma mdelete_lookup {A} (i : nat) (m : map A) :
  mlookup (mdelete i m) i = None.
Proof. Admitted.

Lemma mdelete_lookup_ne {A} (i j : nat) (m : map A) :
  i <> j ->
  mlookup (mdelete i m) j = mlookup m j.
Proof. Admitted.