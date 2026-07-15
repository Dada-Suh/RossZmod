import Game.Metadata

World "DivisibilityWorld"
Level 4

Title "One is not equal to zero"

Introduction "
# Level 4

Here is a fact you have used since you were four.

`1 ≠ 0`

🤔 **But why?** Look at the axioms. Ring axioms, order axioms, Well-Ordering.
Which one rules out a world where `1 = 0`?

Consider the ring with a single element, where `0 = 1` and nothing else exists.
Associativity holds. Commutativity holds. Distributivity holds. Trichotomy holds,
since everything is zero. Well-Ordering holds vacuously.

**Every axiom survives. Except one.**

## Proof by contradiction

We assume the opposite and derive `False`. 👉 Try `intro h`
"

Statement : (1 : Z) ≠ 0 := by
  Hint "👉 Assume the opposite: `intro h`"
  intro h
  Hint "🔍 The axiom `pos_nonempty` says a positive integer exists. 👉 Try `obtain ⟨w, hw⟩ := Z.pos_nonempty`"
  obtain ⟨w, hw⟩ := Z.pos_nonempty
  Hint "🤔 If `1 = 0`, then `w = w * 1 = w * 0 = 0`. 👉 Try `have hzero : w = 0 := by rw [← Z.mul_one w, h, Z.mul_zero]`"
  have hzero : w = 0 := by rw [← Z.mul_one w, h, Z.mul_zero]
  Hint "Finish it. 👉 `rw [hzero] at hw` then `exact Z.not_pos_zero hw`"
  rw [hzero] at hw
  exact Z.not_pos_zero hw

Conclusion "
Level completed! 🎉

💡 **Pro-tip**

The axiom that did the work was `pos_nonempty`: *some positive integer exists.*

It is the most boring axiom on the list. Nobody ever cites it. And without it,
every theorem in this game is true of a set with exactly one element.

The axioms you never think about are the ones holding up the floor.
"

NewTactic intro have
NewTheorem Z.pos_nonempty Z.not_pos_zero Z.mul_one Z.mul_zero
