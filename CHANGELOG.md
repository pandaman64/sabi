# Unreleased

# 2020/05/14 "MIRification Continued"
## Added

- Added heap access modifier to the semantics of place
  - Modifier denotes how the access changes the reborrow tree

## Changed

- Explicitly mentioned fixed parameters (such as gamma) in the predicate
  - This could give us more useful induction formula
  - The fixed parameters are placed left to the turnstile in the semantics

## Learned

- Add `for` to inductive predicate for fixed parameters

# 2020/05/13 "The Great MIRification"
## Added

- Added `tag_kind` type denotes the type of a reference. Currently `Unique` only
- Added `tags` which tracks issued tags

## Changed

- Expression types now mimic MIR's ones (`exp` -> `place`, `operand`, `rvalue`)
  - In particular, `rvalue` became non-recursive
- Variables now refer to a memory location, and the variable context is fixed throughout the execution
  - You need to pre-allocate a location for each variable in the program

## Learned

- How to use rule inversions
  - Do NOT trust auto-generated `then show ?case`. If you are going to perform a complicated case analysis, removing `then` is a good idea
  - I wonder why Isabelle doesn't let us assume equivalent-but-simpler propositions while proving via rule inversions

# 2020/05/06
## Added

- Implements Unique
  - Big-step semantics of expressions with side-effects
  - Small-step semantics of commands
- Example: shows XYX reference is invalid
- Example: swap
