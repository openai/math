import OAI.Hierarchy.GridDescription
import OAI.Hierarchy.FactorCompiledOwners

namespace OAI
/-! # Fixed allocator slices for the receiver's factor and pin tables -/

namespace Hierarchy.GridPinArena

def slab (w : ℕ) : ℕ := 2^(16*w)

/-- The scratch tables use subintervals of one sector. Thirty-two such
subintervals fit there, and thirty-two sectors fit in the machine word. -/
theorem scales (w : ℕ) (pos : 0<w) :
    32*slab w ≤ GridDescription.sector w ∧ 32*GridDescription.sector w < 2^(64*w) := by
  let g := slab w
  let J := GridDescription.sector w
  have small : 32 < g := calc
    32 < 2^6 := by decide
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (show 6≤16*w by omega)
  have square : g*g=J := by
    change 2^(16*w)*2^(16*w)=2^(32*w)
    rw [← pow_add]
    congr 1
    omega
  have full : J*J=2^(64*w) := by
    change 2^(32*w)*2^(32*w)=2^(64*w)
    rw [← pow_add]
    congr 1
    omega
  have first : 32*g ≤ J := square ▸ Nat.mul_le_mul_right g small.le
  have large : 32<J := by omega
  exact ⟨first, (Nat.mul_lt_mul_of_pos_right large (by omega)).trans_eq full⟩

/-- The six addresses used by the native factor classifier. -/
def assignmentBanks (w : ℕ) : FactorBucketRAM.Banks :=
  let J := GridDescription.sector w
  let g := slab w
  ⟨14*J,14*J+g,15*J,15*J+g,15*J+2*g,15*J+3*g⟩

theorem assignment_bounds {w N d : ℕ} (pos : 0<w)
    (rows : N*d ≤ slab w) (steps : 20*(w+1)+1 ≤ slab w)
    (items : N ≤ slab w) (classes : (20*(w+1)+2)^d ≤ slab w) :
    FactorBucketRAM.BankBounds (assignmentBanks w) w (64*w) N d := by
  obtain ⟨loc,word⟩ := scales w pos
  constructor <;> dsimp only [assignmentBanks] <;> omega

end Hierarchy.GridPinArena

end OAI
