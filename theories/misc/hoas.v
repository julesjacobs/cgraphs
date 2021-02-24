Inductive hoas :=
  | App : hoas -> hoas -> hoas
  | Lam : (hoas -> hoas) -> hoas.


Inductive F x :=
  | App : x -> x -> F x
  | Lam : (x -> x) -> F x.


Definition hoas := forall t, (t -> F t) -> t.

Inductive hoas' := F hoas'.

Inductive hoas :=
  | App : hoas -> hoas -> hoas
  | Lam : (hoas -> hoas) -> hoas.

