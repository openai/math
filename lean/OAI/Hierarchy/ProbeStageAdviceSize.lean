import OAI.Hierarchy.ProbeStageScale

namespace OAI
/-! # Space for mask rows and saturation events in subdivision blocks -/

namespace Hierarchy.ProbeStage

/-- All occurrence lists for a block fit in a constant multiple of its
length, uniformly in the address height. -/
theorem occurrences_per_block {h d : ℕ} (hd : 1≤d) :
    radix h d^4 * (8*(4*h+2)) ≤ (288*d+16)*blockSize (radix h d) := by
  let B := radix h d
  let f := digit h d
  have pos : 0<B := radix_pos h d
  have divstate := Nat.div_add_mod h (9*d)
  have rem := Nat.mod_lt h (by omega : 0<9*d)
  have size : f+1 ≤ B := Nat.lt_two_pow_self
  have hb : h ≤ (9*d)*(f+1) := by dsimp [f,digit];rw [Nat.mul_add,Nat.mul_one];omega
  have high : h ≤ 9*d*B := hb.trans (Nat.mul_le_mul_left _ size)
  have reps : 8*(4*h+2) ≤ (288*d+16)*B := by nlinarith only [high,pos]
  have power : B^5 ≤ B^9 := Nat.pow_le_pow_right pos (by decide)
  change B^4 * (8*(4*h+2)) ≤ (288*d+16)*B^9
  calc
    _ ≤ B^4*((288*d+16)*B) := Nat.mul_le_mul_left _ reps
    _ = (288*d+16)*B^5 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ power

/-- The same bound applied to every block in the actual j-th matching.
Count the public occurrences and a counter for every color on one side. -/
theorem occurrences_at_depth {h d j : ℕ} (hd : 1≤d) (depth : j≤rounds d) :
    let B := radix h d
    B^j*blocks (2^widthLog h d j) B*(B^4*(8*(4*h+2))+B) ≤
      (288*d+17)*4^j*2^h := by
  let B := radix h d
  have per := occurrences_per_block (h:=h) hd
  have pos := radix_pos h d
  have mono : B ≤ blockSize B := by
    simpa [blockSize] using Nat.pow_le_pow_right pos (by decide : 1≤9)
  have cap : B^4*(8*(4*h+2))+B ≤ (288*d+17)*blockSize B := by
    change B^4*(8*(4*h+2)) ≤ (288*d+16)*blockSize B at per
    exact (add_le_add per mono).trans_eq (by ring)
  have all : B^j * blocks (2^widthLog h d j) B * blockSize B = 4^j * 2^h := by
    change (radix h d)^j * blocks (2^widthLog h d j) (radix h d) * blockSize (radix h d) = _
    rw [blocks_exact,blockSize_radix,Nat.mul_assoc,← pow_add,
      Nat.add_comm (blockLog h d j) (9*digit h d)]
    exact material_exact hd depth
  calc
    _ ≤ (B^j * blocks (2^widthLog h d j) B) * ((288*d+17)*blockSize B) :=
      Nat.mul_le_mul_left _ cap
    _ = (288*d+17) * (B^j*blocks (2^widthLog h d j) B*blockSize B) := by ring
    _ = _ := by rw [all];ring

/-- A uniform address width for each bank at all fixed subdivision depths. -/
def roomBits (h d : ℕ) := h+2*(rounds d+1)

theorem room_slots (h d : ℕ) : 2^roomBits h d = 4^(rounds d+1)*2^h := by
  rw [roomBits,pow_add,pow_mul,Nat.mul_comm]
  rfl

theorem room_extents {h d j : ℕ} (hd : 1≤d) (hj : j≤rounds d) :
    let E := 2^roomBits h d
    let B := radix h d
    let m := 2^widthLog h d j
    2^h≤E ∧ B^j≤E ∧ m≤E ∧ B≤E ∧ blocks m B≤E := by
  let B := radix h d
  let m := 2^widthLog h d j
  have pos := radix_pos h d
  have gr : 0<B^j := pow_pos pos j
  have mr : 0<m := pow_pos (by decide) _
  have nr : 2^h ≤ 2^roomBits h d := Nat.pow_le_pow_right (by decide) (by unfold roomBits;omega)
  have all : B^j*m ≤ 2^roomBits h d := by
    rw [room_slots]
    exact (material_exact hd hj).trans_le (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have mlim := (Nat.le_mul_of_pos_left m gr).trans all
  refine ⟨nr,(Nat.le_mul_of_pos_right _ mr).trans all,mlim,?_,?_⟩
  · exact (Nat.pow_le_pow_right (by decide) (Nat.div_le_self h (9*d))).trans nr
  · have blockpos : 0<blockSize B := pow_pos pos _
    have km : blocks m B≤m := (ceilDiv_le_iff_le_mul blockpos).mpr (Nat.le_mul_of_pos_left _ blockpos)
    exact km.trans mlim

end Hierarchy.ProbeStage

end OAI
