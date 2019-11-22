From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

(** A library defining binary [minimum] and [maximum] functions, together with
their expected specs. These operations come up often when working manipulating
array indices (checking for bounds). *)

Definition minimum : val :=
  λ: "m" "n", if: "m" < "n" then "m" else "n".

Definition maximum : val :=
  λ: "m" "n", if: "m" < "n" then "n" else "m".

Lemma minimum_spec `{!heapG Σ} s E (Φ : val → iProp Σ) (m n : Z) :
  ▷ Φ #(m `min` n) -∗
  WP minimum #m #n @ s;E {{ Φ }}.
Proof.
  iIntros "HΦ". wp_lam. wp_pures. case_bool_decide; wp_pures.
  - rewrite Z.min_l; [ done | by lia ].
  - rewrite Z.min_r; [ done | by lia ].
Qed.

Lemma minimum_spec_nat `{!heapG Σ} s E (Φ : val → iProp Σ) (m n : nat) :
  ▷ Φ #(m `min` n)%nat -∗
  WP minimum #m #n @ s;E {{ Φ }}.
Proof. iIntros "HΦ". iApply minimum_spec. by rewrite Nat2Z.inj_min. Qed.

Lemma maximum_spec `{!heapG Σ} s E (Φ : val → iProp Σ) (m n : Z) :
  ▷ Φ #(m `max` n) -∗
  WP maximum #m #n @ s;E {{ Φ }}.
Proof.
  iIntros "HΦ". wp_lam. wp_pures. case_bool_decide; wp_pures.
  - rewrite Z.max_r; [ done | by lia ].
  - rewrite Z.max_l; [ done | by lia ].
Qed.

Lemma maximum_spec_nat `{!heapG Σ} s E (Φ : val → iProp Σ) (m n : nat) :
  ▷ Φ #(m `max` n)%nat -∗
  WP maximum #m #n @ s;E {{ Φ }}.
Proof. iIntros "HΦ". iApply maximum_spec. by rewrite Nat2Z.inj_max. Qed.
