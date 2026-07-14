import Game.Metadata

World "DivisibilityWorld"
Level 1

Title "Linearity"

Introduction "
# Level 1

Welcome to Divisibility World! We'll start with the workhorse of the entire game.

## Divisibility

The definition says:

`Divides a b` means `∃ k, b = a * k`

That existential is the whole story. To **use** a divisibility, we extract its witness. To **prove** one, we supply a witness.

## The `obtain` tactic

We have two divisibilities, `hb` and `hc`, but each is locked inside an existential. 👉 Specifically, try

`obtain ⟨k, hk⟩ := hb`

This unpacks `hb` into a witness `k` and the fact `hk : b = a * k`.
"

Statement (a b c x y : Z) (hb : Z.Divides a b) (hc : Z.Divides a c) :
    Z.Divides a (b * x + c * y) := by
  Hint "👉 Try `obtain ⟨k, hk⟩ := hb` to unpack the first divisibility."
  obtain ⟨k, hk⟩ := hb
  Hint "Now do the same with `hc`."
  obtain ⟨l, hl⟩ := hc
  Hint "🤔 We want `∃ k, b * x + c * y = a * k`, and Lean will not let us postpone naming that k. We must produce it first. Since `b = a * k` and `c = a * l`, we get `b * x + c * y = a * (k * x + l * y)`. 👉 Try `exact ⟨k * x + l * y, by rw [hk, hl, Z.mul_add, Z.mul_assoc, Z.mul_assoc]⟩`"
  exact ⟨k * x + l * y, by rw [hk, hl, Z.mul_add, Z.mul_assoc, Z.mul_assoc]⟩

Conclusion "
We've proven our first theorem! 🎉

💡 **Pro-tip**

Notice what Lean forced on us. We had to name the witness *before* we could prove anything about it. In Ross we call this **Have/Want**. Here it isn't advice. It's a compiler error.
"

TacticDoc obtain "Unpacks an existential. `obtain ⟨k, hk⟩ := h` splits `h : ∃ k, P k` into a witness and a proof."
TacticDoc rw "Rewrites the goal using an equation."
TacticDoc exact "Closes the goal by supplying the term directly."

NewTactic obtain rw exact
NewTheorem Z.mul_add Z.mul_assoc
