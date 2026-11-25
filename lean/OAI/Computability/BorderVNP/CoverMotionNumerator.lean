import OAI.Computability.BorderVNP.CoverDeckFrames
import OAI.Computability.BorderVNP.CoverDeckBitArithmetic

/-!
# Exact integral numerator of a deck correction

For the finite-table formula on p. 16, clearing the denominator in both the
motion and its inverse leaves a factor of `7^(2*a)`. Dividing the canonical
residue of that numerator by this factor recovers the canonical output
residue, even if an underlying integral coefficient is negative.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

/-- The quaternion inverse representative stored for a fixed low tile. -/
noncomputable def inverseRepresentative (a : ℕ) (t : Deck (1+2*a)) : Order :=
  ((baseFrame.symm ((deckTileEquiv (1+2*a) t).out)).val⁻¹ : Orderˣ).val

/-- The integral representative of the matrix correction in the base group. -/
noncomputable def correctedUnit {g : SL} {a : ℕ} (hg : Clears g a) (x : gamma 1) : gamma 1 :=
  baseFrame.symm (correction hg (baseFrame x))

/-- The numerator formula before reduction to a finite address. Both cleared
quaternions belong to a fixed motion table. -/
theorem cleared_numerator {g : SL} {a : ℕ} (hg : Clears g a) (u v : Order)
    (hu : (7:ℝ)^a • (g : Mat) = split u) (hv : (7:ℝ)^a • ((g⁻¹ : SL) : Mat) = split v)
    (x : gamma 1) :
    u * x.val.val * inverseRepresentative a (x : Deck (1+2*a)) * v =
      (7:ℤ)^(2*a) • (correctedUnit hg x).val.val := by
  let y : gamma 1 := baseFrame.symm (lowRepresentative a (baseFrame x))
  let z := correctedUnit hg x
  have he : baseFrame y = lowRepresentative a (baseFrame x) := baseFrame.apply_symm_apply _
  have hy : split ((y.val⁻¹ : Orderˣ).val) = (((lowRepresentative a (baseFrame x))⁻¹ : lattice 1) : Mat) := by
    change ((baseFrame y⁻¹ : lattice 1) : Mat) = _
    rw [map_inv,he]
  have hz : split z.val.val = ((correction hg (baseFrame x) : lattice 1) : Mat) := by
    change ((baseFrame z : lattice 1) : Mat) = _
    rw [show baseFrame z = correction hg (baseFrame x) from baseFrame.apply_symm_apply _]
  apply split_injective
  change split (u*x.val.val*(y.val⁻¹ : Orderˣ).val*v) = split ((7:ℤ)^(2*a) • z.val.val)
  rw [map_mul,map_mul,map_mul,← hu,← hv,hy,map_zsmul,← Int.cast_smul_eq_zsmul ℝ,hz]
  change (((7:ℝ)^a • (g:Mat)) * split x.val.val * _ * ((7:ℝ)^a • ((g⁻¹:SL):Mat))) =
    (((7:ℤ)^(2*a) : ℤ) : ℝ) • ((g:Mat)*(split x.val.val * _)*((g⁻¹:SL):Mat))
  push_cast
  rw [two_mul,pow_add,smul_mul_assoc,smul_mul_assoc,smul_mul_assoc,mul_smul_comm,smul_smul]
  congr 1
  simp only [mul_assoc]

/-- Recover a signed integral coefficient at the smaller modulus by division
of the nonnegative canonical representative at the larger modulus. -/
theorem divide_scaled_residue (d e : ℕ) (z : ℤ) :
    (((7:ℤ)^e*z : ℤ) : ZMod (7^(d+e))).val / 7^e = (z : ZMod (7^d)).val := by
  have h : (((7:ℤ)^e*z : ℤ) : ZMod (7^(d+e))).val = 7^e*(z : ZMod (7^d)).val := by
    apply Int.ofNat_inj.mp
    rw [ZMod.val_intCast,Int.natCast_mul,ZMod.val_intCast]
    push_cast
    rw [pow_add,mul_comm ((7:ℤ)^d) _,Int.mul_emod_mul_of_pos _ _ (by positivity)]
  rw [h,Nat.mul_div_cancel_left _ (by positivity)]

/-- Divide each of the four canonical numerator residues by the known
positive denominator. -/
def divideCoords (k : ℕ) (z : BinaryCoords) : BinaryCoords :=
  (z.1/k,z.2.1/k,z.2.2.1/k,z.2.2.2/k)

/-- The computed output consists of the exact four coordinates of the
geometric correction at level `d`. -/
theorem divided_numerator {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ)
    (u v : Order) (hu : (7:ℝ)^a • (g : Mat) = split u)
    (hv : (7:ℝ)^a • ((g⁻¹:SL) : Mat) = split v) (x : gamma 1) :
    let l := d+2*a
    divideCoords (7^(2*a)) (binaryCoords l
      (reduce l u * coordinates l x.val * reduce l (inverseRepresentative a (x : Deck (1+2*a))) *
        reduce l v)) = binaryCoords d (coordinates d (correctedUnit hg x).val) := by
  dsimp only
  change divideCoords _ (binaryCoords _ (reduce _ _ * reduce _ _ * reduce _ _ * reduce _ _)) = _
  rw [← map_mul,← map_mul,← map_mul]
  change divideCoords _ (binaryCoords _ (reduce _
    (u*x.val.val*inverseRepresentative a (x : Deck (1+2*a))*v))) = _
  rw [cleared_numerator hg u v hu hv x]
  unfold divideCoords binaryCoords
  exact Prod.ext (divide_scaled_residue ..)
    (Prod.ext (divide_scaled_residue ..) (Prod.ext (divide_scaled_residue ..) (divide_scaled_residue ..)))

/-- Reading the correction coordinates gives the same label as the geometric
motion table, for every valid input tile. -/
theorem correctedUnit_address {g : SL} {a d : ℕ} (hg : Clears g a) (hd : 1 ≤ d) (x : gamma 1) :
    motionDeck hg hd (x : Deck (d+2*a)) = ((correctedUnit hg x) : Deck d) := by
  apply (deckTileEquiv d).injective
  rw [motionDeck_rep,deckTileEquiv_rep]
  exact congrArg (tile d) (baseFrame.apply_symm_apply _).symm

end Cover.Frame

end BorderVNP
end Computability
end OAI
