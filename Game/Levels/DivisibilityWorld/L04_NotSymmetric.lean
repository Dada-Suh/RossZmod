import Game.Metadata

World "DivisibilityWorld"
Level 4

Title "The statement is false"

Introduction "
Here is a printed claim.

  For all a and b: if a divides b, then b divides a.

Every level so far asked you to prove something true.

This one does not.
"

Statement : ¬ (∀ a b : Z, Z.Divides a b → Z.Divides b a) := by
  Hint "Assume the claim, then break it. `intro h`"
  intro h
  Hint "1 divides 0. Feed that to h."
  have h1 : Z.Divides (1 : Z) (0 : Z) := ⟨0, by rw [Z.mul_zero]⟩
  have h2 := h 1 0 h1
  Hint "h2 says 0 divides 1. Extract its witness and see what it claims."
  obtain ⟨k, hk⟩ := h2
  rw [Z.zero_mul] at hk
  exact Z.zero_ne_one hk.symm

Conclusion "
The counterexample was 1 and 0.

Read the statement!
"

NewTactic intro exact obtain rw
NewTheorem Z.zero_mul Z.zero_ne_one Z.mul_zero
