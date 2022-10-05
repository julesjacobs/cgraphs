From iris.proofmode Require Export base tactics classes.
From cgraphs.cgraphs Require Export util.
From Coq.Logic Require Export FunctionalExtensionality Classical.
From cgraphs Require Export seplogic.
From stdpp Require Export gmap.
Require Export cgraphs.cgraphs.genericinv.

Ltac inv H := inversion H; clear H; simplify_eq.