(**
In this exercise, we prove the correctness of a spin lock module.
*)
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.

Definition newlock : val := λ: <>,
  ref #false.
Definition try_acquire : val := λ: "l",
  CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" "l" :=
    if: try_acquire "l" then #() else "acquire" "l".
Definition release : val := λ: "l",
  "l" <- #false.

(**
As shown, the spin lock is implemented as a reference to a Boolean. If the
Boolean is [true], it means some thread has acquired the lock/entered the
critical section. We initiate the lock with the value [false], which means that
the lock is initially in the unlocked state.

The most interesting function of the spin lock is [acquire], which checks if the
lock is in the unlocked state, and if not, changes the lock into [true]. Since
multiple threads could try to acquire the lock at the same time, we use the
[CAS l v w] (compare-and-set) instruction. This instruction atomically checks
if the value of the reference [l] is equal to [v], and if so, changes it into
[w] and returns [true]. If the value of [l] is unequal to [v], it leaves the
value of [l] as if, and returns [false].
[CAS l v w] is actually a short-hand for [Snd (CmpXchg l v w)], where [CmpXchg]
also returns the old value in [l] before the operation took place.
*)

(**
We will prove the following lock specification in Iris:

  {{{ R }}} newlock #() {{{ lk, RET lk; is_lock lk R }}}.
  {{{ is_lock lk R }}} acquire lk {{{ RET #(); R }}}
  {{{ is_lock lk R ∗ R }}} release lk {{{ RET #(); True }}}.

Here, [is_lock lk R] is a representation predicate which says that a lock at
location [lk] guards the payload [R] described as an Iris proposition.
*)

Section proof.
  Context `{!heapG Σ}.

  (** The invariant of the lock:

  - It owns the memory location [l ↦ #b], which contain a Boolean [b],
  - If the Boolean [b] is [false] (the lock is in the unlocked state),
    then the payload [R] of the lock holds.
  *)
  Definition lock_inv (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ #b ∗ if b then True else R)%I.

  (** Invariants in Iris are named by a *namespace* so that several invariants
  can be opened at the same time, while guaranteeing that no invariant is opened
  twice at the same time (which would be unsound). Here, this is irrelevant,
  since acquiring and releasing a lock only requires to open one invariant.

  The namespace [lockN] of the lock invariant:
  *)
  Definition lockN : namespace := nroot .@ "lock".
  Definition is_lock (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: loc, ⌜ lk = #l ⌝ ∧ inv lockN (lock_inv l R))%I.

  (** The main proofs. *)
  Lemma newlock_spec (R : iProp Σ):
    {{{ R }}} newlock #() {{{ lk, RET lk; is_lock lk R }}}.
  Proof.
    iIntros (Φ) "HR HΦ". iApply wp_fupd.
    wp_lam. wp_alloc l as "Hl".
    (** Use the Iris rule [inv_alloc] for allocating a lock. We put both the
    resources [HR : R] and the points-to [l ↦ #false] into the lock. *)
    iMod (inv_alloc lockN _ (lock_inv l R) with "[HR Hl]") as "#Hinv".
    { iNext. iExists false. iFrame. }
    iModIntro. iApply "HΦ". iExists l. eauto.
  Qed.

  (** *Exercise*: finish the proof below. *)
  Lemma try_acquire_spec lk R :
    {{{ is_lock lk R }}} try_acquire lk
    {{{ b, RET #b; if b is true then R else True }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec.
    (** We have to "focus on" the atomic [CmpXchg] operation before we can
    open the invariant. *)
    wp_bind (CmpXchg _ _ _).
    (** Using the tactic [iInv] we open the invariant. *)
    iInv lockN as (b) "[Hl HR]" "Hclose".
    (** The post-condition of the WP is augmented with an *update* modality
    [ |={⊤ ∖ ↑lockN,⊤}=> ... ], which keeps track of the fact that we opened
    the invariant named [lockN]. We can introduce this update modality by
    closing the lock using the hypothesis:

      "Hclose" : ▷ lock_inv l R ={⊤ ∖ ↑lockN,⊤}=∗ True

    *)
    destruct b.
    - wp_cmpxchg_fail. iMod ("Hclose" with "[Hl]") as "_".
      { iNext. iExists true. iFrame. }
      iModIntro. wp_proj.
      iApply "HΦ". done.
    - wp_cmpxchg_suc. iMod ("Hclose" with "[Hl]") as "_".
      { iNext. iExists true. iFrame. }
      iModIntro. wp_proj.
      iApply "HΦ". done.
  Qed.

  (** *Exercise*: prove the spec of [acquire]. Since [acquire] is a recursive
  function, you should use the tactic [iLöb] for Löb induction. Use the tactic
  [wp_apply] to use [try_acquire_spec] when appropriate. *)
  Lemma acquire_spec lk R :
    {{{ is_lock lk R }}} acquire lk {{{ RET #(); R }}}.
  Proof.
    iIntros (Φ) "#Hl Post".
    iLöb as "IH".
    wp_rec. wp_apply (try_acquire_spec with "Hl").
    iIntros ([]) "Hb".
    - wp_pures. iApply "Post". iFrame.
    - wp_pures. iApply "IH". iNext. iApply "Post".
  Qed.  

  (** *Exercise*: prove the spec of [release]. At a certain point in this proof,
  you need to open the invariant. For this you can use:

    iInv lockN as (b) "[Hl HR]" "Hclose".

  In the same way as in the proof of [try_acquire]. You also need to close the
  invariant. *)
  Lemma release_spec lk R :
    {{{ is_lock lk R ∗ R }}} release lk {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[#Hl HR] Post".
    wp_lam. iDestruct "Hl" as (l) "[-> Hinv]".
    iInv lockN as (b) "[Hl _]" "Hclose".
    wp_store. iMod ("Hclose" with "[Hl HR]") as "_".
    - iNext. iExists false. iFrame.
    - iApply "Post". done. 
  Qed.
End proof.
