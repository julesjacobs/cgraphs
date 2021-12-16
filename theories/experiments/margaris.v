From iris Require Import bi.

Parameter ZZ : Set.
Parameter oZ : ZZ.
Parameter pZ sZ : ZZ -> ZZ.
Hypothesis Zps : ∀ x : ZZ, pZ (sZ x) = x.
Hypothesis Zsp : ∀ x : ZZ, sZ (pZ x) = x.
Hypothesis ZZ_ind_margaris : ∀ Q : ZZ -> Prop,
  Q oZ -> (∀ y, Q y <-> Q (sZ y)) -> ∀ x, Q x.

