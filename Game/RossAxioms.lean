import GameServer.Commands

axiom Z : Type

namespace Z

axiom add : Z → Z → Z
axiom mul : Z → Z → Z
axiom neg : Z → Z
axiom zero : Z
axiom one : Z

noncomputable instance : Add Z := ⟨add⟩
noncomputable instance : Mul Z := ⟨mul⟩
noncomputable instance : Neg Z := ⟨neg⟩
noncomputable instance : OfNat Z 0 := ⟨zero⟩
noncomputable instance : OfNat Z 1 := ⟨one⟩

axiom add_assoc (a b c : Z) : (a + b) + c = a + (b + c)
axiom add_comm  (a b : Z)   : a + b = b + a
axiom add_zero  (a : Z)     : a + 0 = a
axiom add_neg   (a : Z)     : a + (-a) = 0
axiom mul_assoc (a b c : Z) : (a * b) * c = a * (b * c)
axiom mul_comm  (a b : Z)   : a * b = b * a
axiom mul_one   (a : Z)     : a * 1 = a
axiom mul_add   (a b c : Z) : a * (b + c) = a * b + a * c
axiom Pos : Z → Prop
axiom pos_nonempty : ∃ x : Z, Pos x
axiom pos_add {a b : Z} : Pos a → Pos b → Pos (a + b)
axiom pos_mul {a b : Z} : Pos a → Pos b → Pos (a * b)
axiom trichotomy (a : Z) : Pos a ∨ a = 0 ∨ Pos (-a)
axiom not_pos_zero : ¬ Pos (0 : Z)

def Divides (a b : Z) : Prop := ∃ k, b = a * k

infix:50 " ∣ " => Divides

theorem zero_add (a : Z) : 0 + a = a := by
  rw [add_comm, add_zero]

theorem add_left_cancel {a b c : Z} (h : a + b = a + c) : b = c := by
  have key : (-a) + (a + b) = (-a) + (a + c) := by rw [h]
  rw [← add_assoc, ← add_assoc] at key
  rw [add_comm (-a) a, add_neg, zero_add, zero_add] at key
  exact key

theorem mul_zero (a : Z) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  exact add_left_cancel h

theorem right_distrib (a b c : Z) : (b + c) * a = b * a + c * a := by
  rw [mul_comm, mul_add, mul_comm a b, mul_comm a c]

theorem zero_mul (a : Z) : 0 * a = 0 := by
  rw [mul_comm, mul_zero]

theorem one_ne_zero : (1 : Z) ≠ 0 := by
  intro h
  obtain ⟨w, hw⟩ := pos_nonempty
  have hzero : w = 0 := by
    rw [← mul_one w, h, mul_zero]
  rw [hzero] at hw
  exact not_pos_zero hw
end Z

TheoremDoc Z.mul_add as "mul_add" in "Axioms"
TheoremDoc Z.mul_assoc as "mul_assoc" in "Axioms"
TheoremDoc Z.mul_comm as "mul_comm" in "Axioms"
TheoremDoc Z.add_zero as "add_zero" in "Axioms"
TheoremDoc Z.add_comm as "add_comm" in "Axioms"
TheoremDoc Z.add_assoc as "add_assoc" in "Axioms"
TheoremDoc Z.mul_zero as "mul_zero" in "Theorems"
TheoremDoc Z.zero_mul as "zero_mul" in "Theorems"
TheoremDoc Z.zero_ne_one as "zero_ne_one" in "Axioms"
