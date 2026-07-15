import Game.Metadata

World "DivisibilityWorld"
Level 3

Title "Everything divides zero"

Introduction "
# Level 3

Does 7 divide 0?

🤔 **Read the definition, not your instinct.** `Divides a b` says `∃ k, b = a * k`.
So we need a `k` with `0 = 7 * k`.
"

Statement (a : Z) : Z.Divides a 0 := by
  Hint "👉 What single `k` makes `a * k = 0` for *every* `a`? Try `exact ⟨0, by rw [Z.mul_zero]⟩`"
  exact ⟨0, by rw [Z.mul_zero]⟩

Conclusion "
Level completed! 🎉

Every integer divides zero. **Zero included.**

💡 **Pro-tip**

But zero divides only zero. Divisibility is not symmetric.
"

NewTheorem Z.mul_zero
