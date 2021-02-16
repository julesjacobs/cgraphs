Inductive expr :=
  | Pred : expr -> expr
  | Inl : expr -> expr
  | Inr : expr -> expr
  | Unit : expr.
  (* and more... *)

Inductive steps : expr -> expr -> Prop := . (* step relation... *)

CoInductive conat_eq : expr -> expr -> Prop :=
  | zero_eq e1 e2 :
    steps (Pred e1) (Inl Unit) ->
    steps (Pred e2) (Inl Unit) ->
    conat_eq e1 e2
  | succ_eq e1 e2 e1' e2' :
    steps (Pred e1) (Inr e1') ->
    steps (Pred e2) (Inr e2') ->
    conat_eq e1' e2' ->
    conat_eq e1 e2.