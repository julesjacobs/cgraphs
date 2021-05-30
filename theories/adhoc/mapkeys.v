map_kmap f m !! y = None ↔ ∀ x, m !! x = None ∨ f x ≠ y

is_Some (map_kmap f m !! y) ↔ ∃ x, is_Some (m !! x) ∧ f x = y

map_kmap f m !! y = Some v ↔ ∃ x, m !! x = Some v ∧ f x = y

map_kmap f ∅ = ∅

map_kmap f m = ∅ ↔ m = ∅

map_kmap id m = m

map_kmap (f ∘ g) m = map_kmap f (map_kmap g m)

map_kmap f (g <$> m) = g <$> (map_kmap f m)

map_kmap f (<[i:=x]> m) = <[f i:=x]> (map_kmap f m)

map_kmap f (delete x m) = delete (f x) (map_kmap f m)

map_kmap f (m1 ∪ m2) = map_kmap f m1 ∪ map_kmap f m2

map_kmap f (m1 ∖ m2) = map_kmap f m1 ∖ map_kmap m2

map_kmap f m1 ##ₘ map_kmap f m2 ↔ m1 ##ₘ m2

map_kmap f m1 ⊆ map_kmap f m2 ↔ m1 ⊆ m2


f i ∈ dom (map_kmap f m) ↔ i ∈ dom m

j ∈ dom (map_kmap f m) ↔ ∃ i, j = f i ∧ i ∈ dom m
