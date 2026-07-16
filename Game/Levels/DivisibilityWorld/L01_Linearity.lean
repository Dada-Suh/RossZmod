import Game.Metadata

World "DivisibilityWorld"
Level 1

Title "Linearity"

Introduction "
# Level 1

Okay, first level. This one's the workhorse — basically every later proof leans on it, so it's worth getting comfortable here.

## Divisibility

Here's the definition:

`Divides a b` means `∃ k, b = a * k`

So a divisibility is really just a hidden `k`. To **use** one, we dig the `k` out. To **prove** one, we hand over a `k`. That's the whole game, honestly.

## The `obtain` tactic

We've got two divisibilities sitting there, `hb` and `hc`, but the `k`s are locked inside. 👉 Try

`obtain ⟨k, hk⟩ := hb`

That cracks `hb` open into a witness `k` and the fact `hk : b = a * k`.
"

Statement (a b c x y : Z) (hb : Z.Divides a b) (hc : Z.Divides a c) :
    Z.Divides a (b * x + c * y) := by
  Hint "👉 Crack open the first one: `obtain ⟨k, hk⟩ := hb`"
  obtain ⟨k, hk⟩ := hb
  Hint "Same move on `hc`."
  obtain ⟨l, hl⟩ := hc
  Hint "🤔 The goal wants `∃ k, b * x + c * y = a * k`, and Lean won't let us stall — we have to name that `k` up front. Since `b = a * k` and `c = a * l`, a little algebra gives `b * x + c * y = a * (k * x + l * y)`. So the witness is `k * x + l * y`. 👉 Try `exact ⟨k * x + l * y, by rw [hk, hl, Z.mul_add, Z.mul_assoc, Z.mul_assoc]⟩`"
  exact ⟨k * x + l * y, by rw [hk, hl, Z.mul_add, Z.mul_assoc, Z.mul_assoc]⟩

Conclusion "
First theorem down. 🎉

Notice the thing Lean made you do: you had to *name the witness* before you could prove anything about it. That's exactly the Have/Want thing from Ross — except here it's not advice, it's the compiler refusing to move on. Kind of nice, actually.
"

TacticDoc obtain "Cracks open an existential. `obtain ⟨k, hk⟩ := h` splits `h : ∃ k, P k` into a witness and a proof."
TacticDoc rw "Rewrites the goal using an equation."
TacticDoc exact "Closes the goal by handing over the term directly."

NewTactic obtain rw exact
NewTheorem Z.mul_add Z.mul_assoc
