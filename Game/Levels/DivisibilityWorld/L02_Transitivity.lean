import Game.Metadata

World "DivisibilityWorld"
Level 2

Title "Transitivity"

Introduction "
# Level 2

If `a` divides `b`, and `b` divides `c`, does `a` divide `c`?

This should feel *very* similar to how we proved linearity.
"

Statement (a b c : Z) (hab : Z.Divides a b) (hbc : Z.Divides b c) :
    Z.Divides a c := by
  Hint "👉 Unpack both hypotheses with `obtain`."
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  Hint "🤔 We have `b = a * k` and `c = b * l`. Substitute the first into the second. 👉 Try `exact ⟨k * l, by rw [hl, hk, Z.mul_assoc]⟩`"
  exact ⟨k * l, by rw [hl, hk, Z.mul_assoc]⟩

Conclusion "
Level completed! 🎉

The witness was the **product of the witnesses**. Divisibility composes.
"

NewTheorem Z.mul_assoc
