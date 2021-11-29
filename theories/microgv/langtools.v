From iris.proofmode Require Export base tactics classes.
From diris.cgraphs Require Export util.
From Coq.Logic Require Export FunctionalExtensionality Classical.
From diris Require Export seplogic.
From stdpp Require Export gmap.

Ltac inv H := inversion H; clear H; simplify_eq.