import Game.Metadata

World "DivisibilityWorld"
Level 4

Title "One is not equal to zero"

Introduction "
# Level 4

Time for a fact so obvious it feels silly to prove.

`1 ≠ 0`

🤔 But here's the thing — *which axiom actually rules this out?* Scan the list. Ring axioms, order axioms, Well-Ordering.

Picture the ring with exactly one element, where `0 = 1` and that's the whole universe. Associativity? Fine. Commutativity, distributivity? Fine. Trichotomy? Sure, everything's zero. Well-Ordering? Holds, vacuously.

**Every single axiom survives in that tiny world. Except one.** Let's find it.

## Proof by contradiction

We assume `1 = 0` and chase it until something breaks. 👉 Start with `intro h`
"

Statement : (1 : Z) ≠ 0 := by
  Hint "👉 Assume the opposite and see what happens: `intro h`"
  intro h
  Hint "🔍 Peek at the axiom `pos_nonempty` — it promises there's at least one positive integer. Let's grab it. 👉 Try `obtain ⟨w, hw⟩ := Z.pos_nonempty`"
  obtain ⟨w, hw⟩ := Z.pos_nonempty
  Hint "🤔 Now watch: if `1 = 0`, then `w = w * 1 = w * 0 = 0`. So our positive number is secretly zero. 👉 Try `have hzero : w = 0 := by rw [← Z.mul_one w, h, Z.mul_zero]`"
  have hzero : w = 0 := by rw [← Z.mul_one w, h, Z.mul_zero]
  Hint "Land it. 👉 `rw [hzero] at hw`, then `exact Z.not_pos_zero hw`"
  rw [hzero] at hw
  exact Z.not_pos_zero hw

Conclusion "
Got it. 🎉

So the whole proof came down to `pos_nonempty` — the axiom that just says *some positive integer exists*. It's the one nobody ever bothers to write down, and I didn't either at first. But pull it out and the one-element ring satisfies everything else, which means every theorem in this game would also be true of a set with a single point in it. Kind of wild that this one boring line is what keeps ℤ from collapsing.
"

NewTactic intro
NewTheorem Z.pos_nonempty Z.not_pos_zero Z.mul_one Z.mul_zero
