import Game.Metadata

World "DivisibilityWorld"
Level 2

Title "Transitivity"

Introduction "
# Level 2

If `a` divides `b`, and `b` divides `c`, does `a` divide `c`?

You already know the answer's yes. The fun part is that the proof is basically Level 1 again — same moves, so try it before reading the hints.
"

Statement (a b c : Z) (hab : Z.Divides a b) (hbc : Z.Divides b c) :
    Z.Divides a c := by
  Hint "👉 Crack open both with `obtain`."
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  Hint "🤔 We've got `b = a * k` and `c = b * l`. Sub the first into the second and the witness pops right out. 👉 Try `exact ⟨k * l, by rw [hl, hk, Z.mul_assoc]⟩`"
  exact ⟨k * l, by rw [hl, hk, Z.mul_assoc]⟩

Conclusion "
Nice. 🎉

The witness turned out to be just the two witnesses multiplied together. Divisibility chains, and the chaining is literally multiplication.
"

NewTheorem Z.mul_assoc
