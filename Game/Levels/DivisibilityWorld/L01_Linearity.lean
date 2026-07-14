import Game.Metadata

World "DivisibilityWorld"
Level 1

Title "Linearity"

Introduction "
Divides a b unfolds to: exists k, b = a * k.

To USE one, extract with obtain.
To PROVE one, supply a witness.
"

Statement (a b c x y : Z) (hb : Z.Divides a b) (hc : Z.Divides a c) :
    Z.Divides a (b * x + c * y) := by
  Hint "obtain the witnesses"
  obtain ⟨k, hk⟩ := hb
  obtain ⟨l, hl⟩ := hc
  Hint "name the witness"
  exact ⟨k * x + l * y, by rw [hk, hl, Z.mul_add, Z.mul_assoc, Z.mul_assoc]⟩

Conclusion "
Have and want, enforced by a compiler.
"

TacticDoc obtain "Splits an existential into witness and property."
TacticDoc rw "Rewrites using an equation."
TacticDoc exact "Provides the term directly."

NewTactic obtain rw exact
NewTheorem Z.mul_add Z.mul_assoc
