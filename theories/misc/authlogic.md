Record auth := Auth {
  auth_auth_proj : excl heapT;
  auth_frag_proj : heapT;
}.

Σ =-= Σ1 ⋅ Σ2 := Σ1 ##ₘ Σ2 ∧ Σ = Σ1 ∪ Σ2

e =-= e1 ⋅ e2 := match e1, e2 with
                 | None, None => e = None
                 | Some x, None | None, Some x => e = Some x
                 | Some _, Some _ => False
                 end

(Auth Σa Σf) =-= (Auth Σa1 Σf1) ⋅ (Auth Σa2 Σf2) :=
  Σa =-= Σa1 ⋅ Σa2 ∧
  Σf =-= Σf1 ⋅ Σf2 ∧
  (if Σa is Some Σa' then Σf ⊆ Σa' else True).

P ∗ Q := λ r, ∃ r1 r2, (r =-= r1 ⋅ r2) ∧ P r1 ∧ P r2

own_auth Σ := λ r, r = (Some Σ, ∅)
own_frag Σ := λ r, r = (None, Σ)

✓_global (Auth Σa Σf) := (Σa = Some Σf).

|==> P := λ r1, ∀ rf, (∃ r, r =-= r1 ⋅ rf ∧ ✓_global r) →
             ∃ r2, (∃ r', r' =-= r2 ⋅ rf ∧ ✓_global r') ∧ P r2

            P ⊢ |==> P
(|==> |==> P) ⊢ |==> P
 R ∗ (|==> P) ⊢ |==> (R ∗ P)
     (|==> P) ⊢ (|==> Q)         if P ⊢ Q

Proof of R ∗ (|==> P) ⊢ |==> (R ∗ P)
Assume
  r =-= r1 ⋅ r2
  R r1
  (|==> P) r2

We should prove

  (|==> (R ∗ P)) r

That means

  ∀ rf, (∃ r', r' =-= r ⋅ rf ∧ ✓_global r') →
             ∃ rr, (∃ r', r' =-= rr ⋅ rf ∧ ✓_global r') ∧ (R * P) rr

Assume

  r' =-= r ⋅ rf  of te wel r' := r2 ⋅ (r1 ⋅ rf)
  ✓_global r'

We should prove

  ∃ rr, (∃ r', r' =-= rr ⋅ rf ∧ ✓_global r') ∧ (R * P) rr

rf_new := r1 ⋅ rf


#1
  own_auth {[ l := 4 ]} ⊢ |==> own_auth ∅

  r1 := (Some {[ l := 4 ]}, ∅)
  rf := (None, {[ l := 4 ]})

  r2 := (Some ∅, ∅) // ternary relation fails
  r' := (Some ∅, {[ l := 4 ]})

#2
  own_auth {[ l := 4 ]} ⊢ |==> emp

  r1 := (Some {[ l := 4 ]}, ∅)
  rf := (None, {[ l := 4 ]})

  r2 := (None, ∅)
  r' := (None, {[ l := 4 ]}) // global fails

#3
  own_frag {[ l := 4 ]} ⊢ |==> emp

  r1 := (None, {[ l := 4 ]})
  rf := (Some {[ l := 4 ]}, ∅)
  r2 := (None, ∅)
  r' := (Some {[ l := 4 ]}, ∅) // global fails

rf = Auth None {[ l := z ]}

⌜ Σ1 ##ₘ Σ2 ⌝ ∧ own_frag (Σ1 ∪ Σ2) ⊣⊢ own_frag Σ1 ∗ own_frag Σ2

own_frag Σ1 ∗ own_auth Σ2 ⊢ Σ1 ⊆ Σ2

allocation:
  Σ !! l = None →
  own_auth Σ ⊢ |==> own_auth (<[l:=x]> Σ) ∗ own_frag {[ l:=x ]}

deallocation:
  own_auth Σ ∗ own_frag {[ l:=x ]} ⊢ |==> own_auth (delete l Σ)

update:
  own_auth Σ ∗ own_frag {[ l:=x ]} ⊢
    |==> own_auth (<[l:=y]> Σ) ∗ own_frag {[ l := y ]}

adequacy
  (own_auth Σ1 ⊢ |==> ∃ Σ2, own_auth Σ2 ∧ ⌜ φ Σ2 ⌝) →
  φ Σ1


|==> P := λ r1, ∀ rf, (∃ r, r =-= r1 ⋅ rf ∧ ✓_global r) →
             ∃ r2, (∃ r', r' =-= r2 ⋅ rf ∧ ✓_global r') ∧ P r2



proof of adequacy

assume (own_auth Σ1 ⊢ |==> ∃ Σ2, own_auth Σ2 ∧ ⌜ φ Σ2 ⌝)
that means
  ∀ r, (own_auth Σ1) r →
       (|==> ∃ Σ2, own_auth Σ2 ∧ ⌜ φ Σ2 ⌝) r
that means
  (|==> ∃ Σ2, own_auth Σ2 ∧ ⌜ φ Σ2 ⌝) (Some Σ1, ∅)
that means
  ∀ rf, (∃ r, r =-= (Some Σ1, ∅) ⋅ rf ∧ ✓_global r) →
     ∃ Σ2, (∃ r', r' =-= (Some Σ2,∅) ⋅ rf ∧ ✓_global r') ∧ φ Σ2
that means
  ∃ Σ2, (∃ r', r' =-= (Some Σ2,∅) ⋅ (None, Σ1) ∧ ✓_global r') ∧ φ Σ2
that means
  φ Σ1

Definition invariant (chans : heap) (threads : list expr) : hProp :=
  ∃ Σ, own_auth Σ ∗
      (([∗ list] e∈threads, ptyped0 e UnitT) ∗
      heap_typed chans Σ) Σ.



Require Import iris.algebra.auth.

Definition myauth := auth (gmap endpoint (excl chan_type))







P ⊢ |==> P
|==> ■ P ⊢ P
[ P ] ⊢ □ [ P ]


(* P ↔ Q -> P = Q *)
Lemma iProp_ext P Q :
  ■ ((P -∗ Q) ∧ (Q -∗ P)) ⊢ P === Q.
  ∀ x, (∀ y, P y -> Q (y)) ∧ (∀ y, Q y -> P (y)) -> ∀ y, P y ↔ Q y.
  P = l ↦ v
  Q = False