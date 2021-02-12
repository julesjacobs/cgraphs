Require Import List.
Import ListNotations.

Inductive expr :=
  | Tru : expr
  | Fls : expr
  | Var : nat -> expr
  | If : expr -> expr -> expr -> expr
  | Lam : nat -> expr -> expr
  | App : expr -> expr -> expr.

Inductive type :=
  | Bool : type
  | Fun : type -> type -> type.

Inductive typed : list (nat*type) -> expr -> type -> Prop :=
  | T_Bool_Tru : forall Gamma, typed Gamma Tru Bool
  | T_Bool_Fls : forall Gamma, typed Gamma Fls Bool
  | T_Var : forall Gamma1 x t Gamma2,
      typed (Gamma1 ++ [(x,t)] ++ Gamma2) (Var x) t
  | T_If : forall Gamma t e1 e2 e3,
      typed Gamma e1 Bool -> typed Gamma e2 t -> typed Gamma e3 t -> typed Gamma (If e1 e2 e3) t
  | T_Lam : forall Gamma t1 t2 e x,
      typed (Gamma ++ [(x,t1)]) e t2 -> typed Gamma (Lam x e) (Fun t1 t2)
  | T_App : forall Gamma e1 e2 t1 t2,
      typed Gamma e1 (Fun t1 t2) -> typed Gamma e2 t1 -> typed Gamma (App e1 e2) t2.

Lemma exchange Gamma1 Gamma2 x1 t1 x2 t2 e t :
  typed (Gamma1 ++ [(x1,t1);(x2,t2)] ++ Gamma2) e t -> typed (Gamma1 ++ [(x2,t1);(x1,t2)] ++ Gamma2) e t.
Proof.
  generalize Gamma1 Gamma2 t.
  induction e; intros.
  - inversion H. constructor.
  - inversion H. constructor.
  - inversion H. subst.
    admit.
  - inversion H. constructor.
    + apply IHe1. assumption.
    + apply IHe2. assumption.
    + apply IHe3. assumption.
  - inversion H. subst. constructor.
    replace ((Gamma0 ++ [(x1, t1); (x2, t2)] ++ Gamma3) ++ [(n, t3)]) with
            (Gamma0 ++ [(x1, t1); (x2, t2)] ++ (Gamma3 ++ [(n, t3)]))
            in H4 by (rewrite !app_assoc; reflexivity).
    apply IHe in H4.
    rewrite-> !app_assoc in *.
    assumption.
  - inversion H. econstructor.
    + apply IHe1. eassumption.
    + eapply IHe2. eassumption.
Qed.


We moeten bewijzen dat als Γ ⊢ x:T, dan geldt ook Γ' ⊢ x:T waarbij Γ' hetzelde is als Γ maar met twee variabelen omgewisseld. De var-regel zegt dat Γ ⊢ x:T alleen geldt als Γ = Γ1, x:T, Γ2. Dat zegt dus dat x:T ergens in de lijst te vinden moet zijn. Als je nu twee variabelen in de lijst omwisselt is dit nog steeds waar: je kunt x:T dan nog steeds ergens vinden.

Als je het helemaal formeel wil doen zoals in Coq is het ietsje irritanter. Er kunnen bij Γ' een aantal dingen gebeurd zijn: de variabelen die omgewisseld zijn kunnen in Γ1 zitten, een van de twee kan x zelf zijn, en ze kunnen in Γ2 zitten. Hier krijg je dus een aantal gevallen:
- eerste variabele zit in Γ1, tweede zit in Γ1
- eerste variabele zit in Γ1, tweede is x zelf
- eerste variabele zit in Γ1, tweede zit in Γ2
- eerste variabele is x zelf, tweede zit in Γ2
- eerste variabele zit in Γ2, tweede zit in Γ2
In Coq zul je al die gevallen af moeten gaan, en in elk geval iets moeten bewijzen over de lijst van variabelen in de context.

De andere case waar iets gebeurt is T-Abs, als de expressie (λx, e) is. Hierbij krijg je dus een aanname over e, namelijk dat het voor e geldt dat het getypeerd blijft als je variabelen omwisselt.
We moeten onder deze aanname bewijzen dat als Γ ⊢ (λx, e):T geldt, dan geldt ook Γ' ⊢ (λx, e):T waarbij Γ' hetzelfde is als Γ maar met twee variabelen omgewisseld. Volgens de regels kan Γ ⊢ (λx, e):T alleen gelden als T een functietype T1 → T2 is, en als Γ,x:T1 ⊢ e:T2 geldt.
We willen bewijzen dat Γ' ⊢ (λx, e):T geldt, en dat betekent dat we moeten bewijzen dat Γ',x:T1 ⊢ e:T2 geldt. Volgens de inductiehypothese mogen we hier variabelen omwisselen, dus we kunnen Γ' terug omwisselen tot Γ. En dan moeten we bewijzen dat Γ,x:T1 ⊢ e:T2 geldt, en dat hebben we als aanname.

Ik heb een bewijs in Coq gemaakt. Bij de T-Var case heb ik een admit gezet (je zou die zelf kunnen proberen als je zin heb). Bij de T-App is het bewijs wel klaar, en daar kun je met Coq eens doorheen stappen om te zien wat er gebeurt.