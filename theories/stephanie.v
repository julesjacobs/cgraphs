own_vertex o π S

Inductive owner := Thread nat | Chan nat

o : owner
π : frac
S : gmap endpoint chan_type

S1 ##ₘ S2 -> own_vertex o π1 S1 ∗ own_vertex o π2 S2 ⊣⊢ own_vertex o (π1 + π2) (S1 ∪ S2)

Δ : gmap endpoint (chan_type * owner)




Σ : gmap endpoint chan_type

own_auth Δ


chan c: [v1,v2,v3...][v1',v2',...]
           t            t1'

thread1  own_vertex (Thread 1) 1 S1         (App e1 e2)   own_vertex (Thread 1) 1/2 S1_A ∗ own_vertex (Thread 1) 1/2 S1_B
thread2  ...
...

chan1    own_vertex (Chan 1) 1 S1        own_vertex (Chan 1) 1 ∅
chan2


own_vertex o π S

own_vertex o π S   with π < 1

own_vertex o 1 ∅


gmap owner (gmap endpoint chan_type)


X := gmap endpoint (chan_type * owner)
M_old := (option X, X)

iProp := T -> Prop

(Some A, B)

A !! o = Some(S')

B !! o = Some(π, S)

X_auth := gmap owner (gmap endpoint chan_type))
X_frac := gmap owner (frac * (gmap endpoint chan_type))
M := (option X_auth, X_frac)

own_auth A         A : X_auth
own_frac B         B : X_frac

owm : M -> iProp
own m := λ m', m = m'

own (Some A, A) -- top level

own_auth A := own (Some A, ∅) : iProp
own_frac B := owm (None, B) : iProp

In terms of own_auth A, we want to define own_graph Δ, or own_graph Σ.
In terms of own_frac B, we want to define own_vertex o π S.

S : gmap endpoint chan_type
own_vertex o π S := own_frac {[ o := (π, S) ]}

X_auth := gmap owner (gmap endpoint chan_type))

Δ := gmap endpoint (chan_type, owner)
Σ := gmap endpoint chan_type

own_graph Δ := ... own_auth (...) ... P Δ ...
--or--
own_graph Σ := ∃ A, own_auth A ∗ ⌜⌜ valid Σ A ⌝⌝

Σ : gmap endpoint chan_type
A : gmap owner (gmap endpoint chan_type))
valid Σ A := ... acyclic G ...

∀ ep ct, Σ !! ep = Some ct -> ∃! o, A !! o = Some S ∧ S !! ep = Some ct
∀ o S, A !! o = Some S -> S ⊆ Σ

G : gset (owner * owner)
acyclic : G -> Prop

A : gmap owner (gmap endpoint chan_type))
  = gmap (owner * endpoint) chan_type
  ~ gmap (owner * nat) (bool * chan_type)
  ~ gmap (owner * owner) (bool * chan_type)
  = labeled graph



∀ o S ep, A !! o = Some S ∧ ep ∈ dom S -> (o, Chan ep.1) ∈ G ∧ (Chan ep.1, o) ∈ G
(Thread i, Thread i') ∈ G -> False
(Thread i, Chan j) ∈ G -> ∃ S, A !! (Thread i) = Some S ∧ ∃ ct b, S !! (j,b) = Some ct
(Chan j, Thread i) ∈ G -> ...
(Chan i, Chan j) ∈ G -> ...



Inductive owner := Thread nat | Chan nat.
endpoint := nat * bool


o --- o'
      |
      |
      o''

