import OAI.Hierarchy.DescentOverlapTables

namespace OAI
/-! # The common input pitch pays for every table entry used to repack a profile -/
namespace Hierarchy.DescentSIMDLookup.Overlap
open ThreeFlat.Routing
open ThreeFlat.Routing.CallPool

private theorem polynomial (q : ℕ) (start : 16≤q) : (8*q+12)^2≤2^q := by
  obtain ⟨i,rfl⟩:=Nat.exists_eq_add_of_le start
  clear start
  induction i with
  | zero=>decide
  | succ i ih=>
    rw [show 16+(i+1)=(16+i)+1 by omega,pow_succ 2 (16+i)]
    nlinarith only [ih,Nat.zero_le i,Nat.zero_le (i*i)]

theorem original_pages (payload seats A B b : ℕ) (large : 64≤payload)
    (oldPitch : A≤payload) (newPitch : B≤payload) (oldBits : b*A≤payload/4) :
    (pieces seats A B+1)*(A+1)*2^(b*A)≤2^(payload/2) := by
  have count : chunks B A≤B+A := (Nat.div_le_self _ _).trans (Nat.sub_le ..)
  have p : pieces seats A B≤chunks B A+1:=Nat.min_le_right ..
  have first : pieces seats A B+1≤8*(payload/4)+12 := by omega
  have second : A+1≤8*(payload/4)+12 := by omega
  have pair : (pieces seats A B+1)*(A+1)≤2^(payload/4) :=
    (Nat.mul_le_mul first second).trans (by simpa only [pow_two] using polynomial (payload/4) (by omega))
  calc
    _ ≤ 2^(payload/4)*2^(payload/4) :=
      Nat.mul_le_mul pair (Nat.pow_le_pow_right (by decide) oldBits)
    _ = 2^(payload/4+payload/4) := (pow_add ..).symm
    _ ≤ 2^(payload/2) := Nat.pow_le_pow_right (by decide) (by omega)

theorem original_header_bits (payload b : ℕ) : b*lanes (payload/2) b≤payload/4 := by
  have h:=lanes_fit (payload/2) b
  rw [Nat.mul_comm b]
  simpa only [Nat.div_div_eq_div_mul] using h


theorem chunks_floor (seats pitch : ℕ) (pos : 0<pitch) : chunks seats pitch≤ seats/pitch+1 := by
  change (seats+pitch-1)/pitch≤_
  exact (Nat.div_le_div_right (Nat.sub_le ..)).trans_eq (Nat.add_div_right seats pos)

theorem floor_bill (seats pitch w c unit : ℕ) (rate : w≤c*pitch*unit) :
    (seats/pitch)*w≤c*seats*unit := by
  have used:=Nat.div_mul_le_self seats pitch
  calc
    _ ≤ (seats/pitch)*(c*pitch*unit) := Nat.mul_le_mul_left _ rate
    _ = c*((seats/pitch)*pitch)*unit := by ring
    _ ≤ _ := Nat.mul_le_mul_right unit (Nat.mul_le_mul_left c used)

end Hierarchy.DescentSIMDLookup.Overlap

end OAI
