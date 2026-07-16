import Game.Metadata

World "DivisibilityWorld"
Level 3

Title "Everything divides zero"

Introduction "
# Level 3

Does 7 divide 0?

🤔 Careful — go check the definition instead of trusting your gut. `Divides a b` means `∃ k, b = a * k`. So we just need some `k` with `0 = 7 * k`. Hmm.
"

Statement (a : Z) : Z.Divides a 0 := by
  Hint "👉 What's the one `k` that makes `a * k = 0` no matter what `a` is? Try `exact ⟨0, by rw [Z.mul_zero]⟩`"
  exact ⟨0, by rw [Z.mul_zero]⟩

Conclusion "
Done. 🎉

Turns out every integer divides zero — yes, including zero itself. But watch out: it only goes one way. Zero divides *only* zero, so divisibility isn't symmetric. Easy to trip on that one.
"

NewTheorem Z.mul_zero
