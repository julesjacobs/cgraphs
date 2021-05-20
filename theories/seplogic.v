From stdpp Require Export gmap.
From iris.bi Require Export interface.
From iris.algebra Require Import excl gmap auth.
From iris.proofmode Require Export tactics.
Require Export diris.langdef.
Require Export diris.logic.bi.
Require Export diris.util.
Require Export diris.logic.bupd.


Canonical Structure chan_typeO := leibnizO chan_type.

Notation heapT := (gmap endpoint chan_type).
Notation heapT_UR := (gmapUR endpoint (exclR chan_typeO)).

Notation hProp := (uPred heapT_UR).

Definition own (l : endpoint) (t : chan_type) : hProp :=
  uPred_ownM {[ l := Excl t ]}.

Notation "⌜⌜ p ⌝⌝" := (<affine> ⌜ p ⌝)%I : bi_scope.