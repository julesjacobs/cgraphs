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

- Implement runtime type system
- Prove lemmas about runtime type system:
  + Substitution
  + Replacement
  + Pure preservation
  + Pure progress
- Define invariant
- Prove preservation
- Prove reachability
- Encode session types
  + Types
  + Operations
  + Admissibility of more efficient rules