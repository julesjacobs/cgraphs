# Operational semantics

- Use finite map as configuration
- Need can_stepi for partial deadlock freedom
  + How to generalize this? For partial partial deadlock freedom?
- Use only one binder: lambda

# Type system

- Function type parameterized by lin/unr

# Theorems

- Define theorem statements in the language definition

# Substitution lemma

- Use substitution resource to avoid case splitting

# TODO

- Generalize env_*** notions to generalize over different type systems (co-contextual, normal, no shadowing, etc.)
- Prove preservation
  + Add generic lemma for delete
  + Prove sync case
- Prove reachability
  + Define the reachability predicate
  + Think about partial partial deadlock freedom
- Encode session types
  + Types
  + Operations
  + Admissibility of more efficient rules