import OAI.Computability.VPVNP.PrimedInputRAMCapacity
import OAI.Computability.VPVNP.PrimedStackRAMMemory

/-!
# Word addresses for the entire primed parser

After the two input passes, the parser keeps its frames, marks, histogram
and depth word beyond the output rectangle. The same word width fits the
absolute call cursor and every partial histogram component.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Resources

open BurstRAM CursorBounds PrimedInputRAM PrimedStackRAM

/-- The live processor count absorbs the fixed histogram degree bound. -/
theorem labels_le_processors {B C n t : ℕ} (hB : C ≤ B) (hn : 0 < n) (ht : t ≤ n^C) :
    t ≤ processorCount B n := by
  calc
    t ≤ n^B := ht.trans (Nat.pow_le_pow_right hn hB)
    _ ≤ (2^(Nat.clog 2 n))^B := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) n) _
    _ = processorCount B n := by
      rw [← pow_mul, Nat.mul_comm]
      rfl

/-- Simultaneous address-space bounds at the paper's virtual scratch base. -/
theorem space {B n t : ℕ} (hB : 1 ≤ B) (hn : 1 ≤ n) (ht : t ≤ processorCount B n) :
    let r := addressWidth B n
    let R := processorCount B n
    let w := CursorBounds.wordBits B n
    2^(virtualBits B n) + positions n r + size R n n t ≤ 2^w ∧
      10*R*n + t < 2^w ∧ n^2 ≤ 2^w ∧ 2^(2*r) ≤ 2^w := by
  let r := addressWidth B n
  let R := processorCount B n
  let P := 2^(3*r)
  have hc : Nat.clog 2 n ≤ r := Nat.le_mul_of_pos_left _ hB
  have hD : virtualBits B n ≤ 3*r := by
    have h := virtualBits_le B n
    rw [Nat.add_mul] at h
    change Nat.clog 2 n ≤ B * Nat.clog 2 n at hc
    change _ ≤ 3*(B * Nat.clog 2 n)
    omega
  have hS : 2^(virtualBits B n) ≤ P := Nat.pow_le_pow_right (by decide) hD
  have hword : 3*r+4 ≤ (r+10)^4 := by
    calc
      3*r+4 ≤ (r+10)^2 := by nlinarith [Nat.zero_le (r*r)]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hroom : P*16 ≤ 2^(CursorBounds.wordBits B n) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hword
    rw [pow_add] at h
    exact h
  have hnR : n ≤ R := (Nat.le_pow_clog (by decide) n).trans (Nat.pow_le_pow_right (by decide) hc)
  have hR2 : R * R = 2^(2*r) := by
    change 2^r * 2^r = 2^(2*r)
    rw [← pow_add, two_mul]
  have hP2 : R * R ≤ P := hR2 ▸ (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2*r ≤ 3*r))
  have hRn : R*n ≤ P := (Nat.mul_le_mul_left _ hnR).trans hP2
  have hR : R ≤ P := (Nat.le_mul_of_pos_right _ hn).trans hRn
  have hnn : n*n ≤ P := (Nat.mul_le_mul_right _ hnR).trans hRn
  have hP : 0 < P := Nat.two_pow_pos _
  change _ + positions n r + size R n n t ≤ _ ∧ 10*R*n+t < _ ∧ n^2 ≤ _ ∧ _
  have hpos : positions n r = 2*(R*n) := by unfold positions; rw [Nat.mul_assoc]; rfl
  rw [hpos, size, pow_two, ← hR2, Nat.mul_assoc 2 R n, Nat.mul_assoc 10 R n]
  change t ≤ R at ht
  omega

/-- Each parser state occurs in a terminal production, so the state bound
also fits when the dense production array fits. -/
theorem states_fit {n H w : ℕ} (hn : 1 ≤ n) (ht : labelCount n n H < 2^w) : H < 2^w := by
  have hmul : H ≤ H*n := Nat.le_mul_of_pos_right _ hn
  unfold labelCount at ht
  omega

end PrimedCounter.Resources

end VPVNP
end Computability
end OAI
