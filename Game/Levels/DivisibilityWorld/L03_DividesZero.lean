import Game.Metadata

World "DivisibilityWorld"
Level 3

Title "Everything divides zero"

Introduction "
Does 7 divide 0?

Read the definition. Do not trust your instinct.
"

Statement (a : Z) : Z.Divides a 0 := by
  Hint "You need some k with 0 = a * k."
  exact ⟨0, by rw [Z.mul_zero]⟩

Conclusion "
Every integer divides zero. Zero included.

Zero, however, divides only zero. The relation is not symmetric, and that
asymmetry is why it is called divisibility and not equality.
"

NewTheorem Z.mul_zero
