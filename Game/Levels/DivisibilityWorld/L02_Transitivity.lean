import Game.Metadata

World "DivisibilityWorld"
Level 2

Title "Transitivity"

Introduction "
If a divides b, and b divides c, does a divide c?

Extract two witnesses. Build one.
"

Statement (a b c : Z) (hab : Z.Divides a b) (hbc : Z.Divides b c) :
    Z.Divides a c := by
  Hint "obtain both"
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  Hint "c = b * l, and b = a * k. Substitute."
  exact ⟨k * l, by rw [hl, hk, Z.mul_assoc]⟩

Conclusion "
The witness was the product of the witnesses. Divisibility composes.
"

NewTheorem Z.mul_assoc
