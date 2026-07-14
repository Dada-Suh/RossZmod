# Ross ℤ Game

Number theory as a Lean 4 game, built from the axioms used at the
Ross Mathematics Program.

## The axiom system

- Ring axioms, with **left distributivity only**. Right distributivity is a theorem.
- Order axioms. No assumption that 1 is positive.
- Well-Ordering. **No induction tactic.**
- **No Mathlib.** The integers are an opaque type with eight axioms attached.

The starvation is the point. A player who can call `omega` has learned nothing.

## Worlds

1. **Divisibility** — linearity, transitivity
2. **Bézout** — division algorithm by WOP, gcd as least positive combination
3. **Congruence** — equivalence relation, compatibility with + and ×
4. **Units** — invertibility, and a level where the goal is to *disprove* a false statement
5. **CRT** — the isomorphism, Euler, Fermat

## Play

https://adam.math.hhu.de/#/g/Dada-Suh/RossZmod

## Status

Divisibility world in progress.

Built at the Ross Mathematics Program, 2026.
