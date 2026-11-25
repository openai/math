import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineClass

/-! # Per-record budget of a binary address mask -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace AffineAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
  IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims

private theorem room_le (s : Tape) : room s ≤ 2 ^ size (shape s) := by
  induction s with
  | nil => decide
  | cons n s ih =>
    have le (r : ℕ) : r ≤ 2^r := by
      induction r with
      | zero => decide
      | succ r h => rw [pow_succ]; have := Nat.one_le_pow r 2 (by decide); omega
    have sz : n ≤ size (tally n) := by rw [size_tally,tally_length]; omega
    calc
      _ ≤ 2^size (tally n) * 2^size (shape s) :=
        Nat.mul_le_mul ((le n).trans (Nat.pow_le_pow_right (by decide) sz)) ih
      _ ≤ _ := by simp only [shape_cons,size_cons,pow_succ,pow_add]; omega

theorem Geometry.bits_le (g : Geometry) : g.bits ≤ 2*size g.desc + 3 := by
  have h := Nat.clog_le_of_le_pow (room_le g.field)
  change 2*Nat.clog 2 (room g.field)+3 ≤ 2*size (shape g.pre,shape g.field,shape g.post)+3
  simp only [size_prod]
  omega

/-- A fixed polynomial in the complete serialized mask descriptor. -/
def localPrice (d h : ℕ) := 40*(h+8)+(8*(h+8))^d

theorem Comparison.budget_le (z : Comparison) (d : ℕ)
    (h₁ : room z.first.field ^ 2 ≤ z.first.rows.count)
    (h₂ : room z.second.field ^ 2 ≤ z.second.rows.count) :
    z.budget d ≤ (z.first.rows.count+1)*localPrice d (size z.desc) := by
  let V := z.first.rows.count
  let h := size z.desc
  have secondV : z.second.rows.count = V := z.aligned.symm
  have sizes : size z.scalar ≤ h ∧ size z.first.desc ≤ h ∧ size z.second.desc ≤ h := by
    change _ ≤ size (z.scalar,z.first.desc,z.second.desc) ∧
      _ ≤ size (z.scalar,z.first.desc,z.second.desc) ∧ _ ≤ size (z.scalar,z.first.desc,z.second.desc)
    simp only [size_prod]
    omega
  have sq (a : ℕ) (ha : 1 ≤ a) (e : a^2 ≤ V) : (a+1)^2 ≤ 4*V := by
    nlinarith [Nat.mul_self_le_mul_self (show a+1 ≤ 2*a by omega)]
  have bits (g : Geometry) (e : size g.desc ≤ h) : g.bits+2 ≤ 2*h+5 := by
    have := g.bits_le
    omega
  have gb (g : Geometry) (e : size g.desc ≤ h) (v : g.rows.count = V) (s : room g.field^2 ≤ V) :
      g.budget ≤ (V+1)*(3*h+10) := by
    have square := sq _ (wide _ g.fieldSolid) s
    have row := Nat.mul_le_mul_left V (bits g e)
    unfold Geometry.budget
    rw [v]
    nlinarith
  have a := gb z.first sizes.2.1 rfl h₁
  have b := gb z.second sizes.2.2 secondV (secondV ▸ h₂)
  have c : z.heightBound + 1 ≤ 8*(h+8) := by
    unfold heightBound
    have := bits z.first sizes.2.1
    have := bits z.second sizes.2.2
    omega
  have cc := Nat.pow_le_pow_left c d
  have current : (V+1)*(z.heightBound + (z.heightBound+1)^d + 2) ≤
      (V+1)*(8*(h+8) + (8*(h+8))^d + 1) := Nat.mul_le_mul_left _ (by omega)
  have hh : h≤(V+1)*h := Nat.le_mul_of_pos_left _ (by omega)
  change h + z.first.budget + z.second.budget + (V+1)*(z.heightBound + (z.heightBound+1)^d + 2) + 1 ≤ _
  change _ ≤ (V+1)*(40*(h+8)+(8*(h+8))^d)
  nlinarith

end AffineAddress

end NearSquareRoot
end Computability
end OAI
