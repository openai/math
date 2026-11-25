import OAI.Hierarchy.ProbeStagePorts

namespace OAI
/-! # Exact lengths of the dyadic subdivision of a permutation -/

namespace Hierarchy.ProbeStage

/-- One digit of the growing radix and the fixed number of splits. -/
def digit (h d : ℕ) := h/(9*d)
def rounds (d : ℕ) := 9*(d-1)
def radix (h d : ℕ) := 2^digit h d

/-- Blocks per parent list at level j have this binary logarithm. -/
def blockLog (h d j : ℕ) := h%(9*d) + 2*j + (rounds d-j)*digit h d

def widthLog (h d j : ℕ) := 9*digit h d + blockLog h d j

theorem radix_pos (h d : ℕ) : 0 < radix h d := pow_pos (by decide) _

theorem widthLog_start {h d : ℕ} (hd : 1 ≤ d) : widthLog h d 0 = h := by
  have add : 9 + rounds d = 9*d := by unfold rounds; omega
  have eq := Nat.div_add_mod h (9*d)
  unfold widthLog blockLog digit
  simp only [Nat.sub_zero,Nat.mul_zero,Nat.add_zero]
  calc
    _ = (9+rounds d)*(h/(9*d)) + h%(9*d) := by ring
    _ = h := by rw [add];exact eq

theorem log_residue {h d j : ℕ} (hd : 1 ≤ d) (hj : j ≤ rounds d) :
    j*digit h d + widthLog h d j = h+2*j := by
  have total : rounds d-j+j=rounds d := Nat.sub_add_cancel hj
  have a := widthLog_start (h:=h) hd
  unfold widthLog blockLog at a ⊢
  simp only [Nat.sub_zero,Nat.mul_zero,Nat.add_zero] at a
  calc
    _ = 9*digit h d + (h%(9*d)+(rounds d-j+j)*digit h d)+2*j := by ring
    _ = _ := by rw [total,a]

theorem blockSize_radix (h d : ℕ) : blockSize (radix h d) = 2^(9*digit h d) := by
  simp only [blockSize,radix,← pow_mul,Nat.mul_comm (digit h d) 9]

theorem quota_radix (h d : ℕ) : quota (radix h d) = 2^(2+8*digit h d) := by
  unfold quota radix
  rw [← pow_mul, pow_add,Nat.mul_comm (digit h d) 8]
  rfl

private theorem mul_ceiling (a b : ℕ) (ha : 0<a) : (a*b) ⌈/⌉ a = b := by
  apply le_antisymm ((ceilDiv_le_iff_le_mul ha).mpr le_rfl)
  exact Nat.le_of_mul_le_mul_left ((ceilDiv_le_iff_le_mul ha).mp le_rfl) ha

theorem blocks_exact (h d j : ℕ) : blocks (2^widthLog h d j) (radix h d) = 2^blockLog h d j := by
  unfold blocks
  rw [blockSize_radix,widthLog,pow_add]
  exact mul_ceiling _ _ (pow_pos (by decide) _)

theorem inner_exact {h d j : ℕ} (hj : j < rounds d) :
    innerSize (2^widthLog h d j) (radix h d) = 2^widthLog h d (j+1) := by
  rw [innerSize,blocks_exact,quota_radix,← pow_add]
  congr 1
  have minus : rounds d-j = rounds d-(j+1)+1 := by omega
  unfold widthLog blockLog
  rw [minus]
  ring

theorem material_exact {h d j : ℕ} (hd : 1 ≤ d) (hj : j ≤ rounds d) :
    (radix h d)^j * 2^widthLog h d j = 4^j * 2^h := by
  unfold radix
  rw [← pow_mul,← pow_add,show (4:ℕ)=2^2 by decide,← pow_mul,← pow_add]
  congr 1
  rw [Nat.mul_comm (digit h d) j,log_residue hd hj,Nat.add_comm]

theorem center_width (h d : ℕ) : widthLog h d (rounds d) =
    9*digit h d + h%(9*d) + 18*(d-1) := by
  simp [widthLog,blockLog,rounds]; omega

theorem outer_width (h d : ℕ) : radix h d * quota (radix h d) = 2^(9*digit h d+2) := by
  rw [quota_radix,radix,← pow_add]
  congr 1
  omega

end Hierarchy.ProbeStage

end OAI
