import OAI.Hierarchy.DescentColonyMultipliers
import OAI.Hierarchy.DescentMultiplierSeeds
import OAI.Hierarchy.DescentPackedSplitContribution
import OAI.Hierarchy.DescentAffineColors

namespace OAI
/-! # Relative colony names and affine sides in an old occurrence -/

namespace Hierarchy.DescentColonies.PackedWinnerKey
open DescentGL DescentBinaryField DescentAffineColors DescentSIMDLookup PackedSplit
open scoped Classical Fin.CommRing
noncomputable section
variable {H G k : ℕ}

/-- The index transferred by a matching record is relative to its common
position. The zero record denotes an unused lane of the last packed word. -/
def value (hk : 0<k) (i : Fin (2^k-1)) (j : Candidate k) (x : Block k)
    (p : Cell (1+k*2^k)) : Cell (k+3) :=
  if p=0 then 0 else
    let y := rearrange (multiplier hk (seedAt k i)) x
    let d := PackedSplit.depth (decodeFlags (strip p)) y
    ((1+2*(2^d-1+group d y)+(thick j y).toNat : ℕ) : Cell (k+3))

@[simp] theorem value_zero (hk : 0<k) (i : Fin (2^k-1)) (j : Candidate k) (x : Block k) :
    value hk i j x 0=0 := by simp [value]

theorem value_actual (inc : Fin H→List (Fin H)) (W : Fin G→Fin H→Block k→ℕ) (D cap : ℕ)
    (hk : 0<k) (i : Fin (2^k-1)) (j : Candidate k) (v : Fin H) (g : Fin G) (x : Block k) :
    let y := rearrange (multiplier hk (seedAt k i)) x
    let rows := Scan.build inc (multiplierLoad (W g) (modulus hk) (seedAt k i).val) D cap k
    let d := Scan.leafDepth rows v y
    (value hk i j x (state inc W D cap (modulus hk) (seedAt k i) v g)).val=
      1+2*(2^d-1+group d y)+(thick j y).toNat := by
  let y := rearrange (multiplier hk (seedAt k i)) x
  let rows := Scan.build inc (multiplierLoad (W g) (modulus hk) (seedAt k i).val) D cap k
  let d := Scan.leafDepth rows v y
  have inside : 2^d-1+group d y<2^(k+1) := by
    have lower : d≤k := Scan.leafDepth_le rows v y
    have sector : group d y<2^d := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (k-d))).mpr
      simpa only [←pow_add,show d+(k-d)=k by omega] using y.isLt
    have span := Nat.pow_le_pow_right (by decide : 0<2) lower
    rw [pow_succ]
    omega
  have side : (thick j y).toNat≤1 := by cases thick j y <;> decide
  have fit : 1+2*(2^d-1+group d y)+(thick j y).toNat<2^(k+3) := by
    rw [show k+3=k+1+2 by omega,pow_add];norm_num;omega
  simp only [value,state,present_ne_zero,ite_false,strip_present,decode_encodeFlags,depth_actualFlags]
  exact Fin.val_cast_of_lt fit

end
end Hierarchy.DescentColonies.PackedWinnerKey

end OAI
