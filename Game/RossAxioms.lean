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

def Divides (a b : Z) : Prop := ∃ k, b = a * k

end Z
