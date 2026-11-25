import OAI.Hierarchy.DescentOverlapTariff

namespace OAI
/-! # Cost of an overlap conversion between two occupied word formats -/
namespace Hierarchy.DescentSIMDLookup.Overlap
open ProtocolRAM DescentStaticWordColumn
noncomputable section

/-- The lookup index contains the alignment of the first requested digit as
well as the contents of the entire old word. -/
theorem lookup_paid (h U a : ℕ) (width : a+1 ≤ U) :
    (lanes h U+1)*2^(a*lanes h U) ≤ 2^(h/2) := by
  let A:=lanes h U
  have digits : A+a*A ≤ h/2 := by
    calc
      _ = A*(a+1) := by ring
      _ ≤ A*U := Nat.mul_le_mul_left _ width
      _ ≤ _ := lanes_fit h U
  calc
    _ ≤ 2^A*2^(a*A) := Nat.mul_le_mul_right _ A.lt_two_pow_self
    _ = 2^(A+a*A) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) digits

/-- A new word requests at most this many old words even if its first digit
begins partway through an old word. -/
theorem pieces_at_lanes (G h U V blocks : ℕ) (oldPos : 0<U) (oldRoom : 2*U ≤ h) :
    pieces G (lanes h U) (lanes h V*blocks)+1 ≤ 4*U*blocks+3 := by
  let A:=lanes h U
  let B:=lanes h V*blocks
  have occ:=occupancy h U oldPos oldRoom
  have live : 0<A:=occ.1
  have price : B ≤ (4*U*blocks)*A := by
    calc
      B ≤ h*blocks := Nat.mul_le_mul_right blocks (Nat.div_le_self ..)
      _ ≤ (4*A*U)*blocks := Nat.mul_le_mul_right _ occ.2
      _ = _ := by ring
  have cut : chunks B A ≤ 4*U*blocks+1 := by
    change (B+A-1)/A ≤ _
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul live).mpr
    rw [Nat.succ_mul,Nat.add_mul,Nat.one_mul]
    omega
  have used : pieces G A B ≤ chunks B A+1 := min_le_right ..
  change pieces G A B+1 ≤ 4*U*blocks+3
  omega

theorem lane_bill (base H G h U V blocks a w ratio : ℕ) (src : Bank)
    (width : a+1 ≤ U) (oldRoom : 2*U ≤ h) (newPos : 0<V) (newRoom : 2*V ≤ h)
    (blockPos : 0<blocks) (machine : w ≤ ratio*h) :
    let A:=lanes h U
    let B:=lanes h V*blocks
    (ticks base H G A B a src+7*names (program base H G A B a w src))*w ≤
      2048*((4*U*blocks+3)*2^(h/2)+H*chunks G A+H*chunks G B+1)*(ratio*h) := by
  dsimp only
  have oldPos : 0<U:=by omega
  have charged:=tariff base H G (lanes h U) (lanes h V*blocks) a w src
    (occupancy h U oldPos oldRoom).1 (Nat.mul_pos (occupancy h V newPos newRoom).1 blockPos)
  have lookup:=Nat.mul_le_mul (pieces_at_lanes G h U V blocks oldPos oldRoom) (lookup_paid h U a width)
  rw [←Nat.mul_assoc] at lookup
  have native:=Nat.mul_le_mul_left 2048
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right lookup (H*chunks G (lanes h U)))
      (H*chunks G (lanes h V*blocks))) 1)
  exact Nat.mul_le_mul (charged.trans native) machine

end
end Hierarchy.DescentSIMDLookup.Overlap

end OAI
