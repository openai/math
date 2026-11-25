import OAI.Computability.BorderVNP.ResidueFourierCount
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Power-basis limb encoding of the guessed interpolation points

A processor may guess one fixed-width binary word for each prime-field coordinate of
each grid point. It rejects out-of-range limbs and the all-zero field element. Thus
each tuple of units occurs exactly once in the sum, including when the prime is odd
and the word capacity strictly exceeds the characteristic.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueFourier

open Module ResidueBox
open scoped BigOperators Classical

variable {p d w : ℕ} [Fact p.Prime] {K E ι σ : Type*} [Field K] [Algebra (ZMod p) K]

/-- A fixed-width word per basis coordinate of a grid field element. -/
abbrev LimbWords (d w : ℕ) := Fin d → Fin (2 ^ w)

/-- Decode the prime-field coordinates of a guessed element in the supplied basis. -/
noncomputable def unpackScalar (B : Basis (Fin d) (ZMod p) K) (a : LimbWords d w) : K :=
  B.equivFun.symm fun j => ((a j).val : ZMod p)

/-- A valid nonzero field word has all limbs in range and at least one nonzero limb. -/
def validLimbs (p : ℕ) (a : LimbWords d w) : Prop :=
  (∀ j, (a j).val < p) ∧ ∃ j, (a j).val ≠ 0

private noncomputable def packScalar (B : Basis (Fin d) (ZMod p) K) (hw : p ≤ 2 ^ w)
    (a : K) : LimbWords d w :=
  fun j => ⟨(B.equivFun a j).val, (ZMod.val_lt _).trans_le hw⟩

private theorem unpack_pack (B : Basis (Fin d) (ZMod p) K) (hw : p ≤ 2 ^ w) (a : K) :
    unpackScalar B (packScalar B hw a) = a := by
  apply B.equivFun.injective
  simp [unpackScalar, packScalar]

private theorem pack_unpack (B : Basis (Fin d) (ZMod p) K) (hw : p ≤ 2 ^ w)
    (a : LimbWords d w) (h : ∀ j, (a j).val < p) :
    packScalar B hw (unpackScalar B a) = a := by
  funext j
  apply Fin.ext
  simp only [packScalar, unpackScalar, LinearEquiv.apply_symm_apply]
  exact ZMod.val_natCast_of_lt (h j)

private theorem valid_pack (B : Basis (Fin d) (ZMod p) K) (hw : p ≤ 2 ^ w) (a : Kˣ) :
    validLimbs p (packScalar B hw a.val) := by
  refine ⟨fun j => ZMod.val_lt _, ?_⟩
  by_contra! h
  apply a.ne_zero
  apply B.equivFun.injective
  funext j
  have := h j
  change (B.equivFun a.val j).val = 0 at this
  simpa using ((ZMod.val_eq_zero _).mp this)

private theorem unpack_ne_zero (B : Basis (Fin d) (ZMod p) K) (a : LimbWords d w)
    (h : validLimbs p a) : unpackScalar B a ≠ 0 := by
  obtain ⟨j, hj⟩ := h.2
  intro hzero
  apply hj
  have e := congrFun (congrArg B.equivFun hzero) j
  simp only [unpackScalar, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply] at e
  simpa [ZMod.val_natCast_of_lt (h.1 j)] using congrArg ZMod.val e

/-- Evaluate a grid-tuple function on packed words, returning zero on rejected encodings. -/
noncomputable def packedValue [Fintype ι] {R : Type*} [Zero R] (B : Basis (Fin d) (ZMod p) K)
    (f : (ι → Kˣ) → R) (a : ι → LimbWords d w) : R :=
  if h : ∀ i, validLimbs p (a i) then f (fun i => Units.mk0 _ (unpack_ne_zero B _ (h i))) else 0

/-- Summing over all packed word guesses is equivalent to summing over the multiplicative
grid. No bound or table indexed by the number of grid elements is involved. -/
theorem sum_packedValue [Fintype ι] [Fintype K] {R : Type*} [AddCommMonoid R]
    (B : Basis (Fin d) (ZMod p) K) (hw : p ≤ 2 ^ w) (f : (ι → Kˣ) → R) :
    ∑ a : ι → LimbWords d w, packedValue B f a = ∑ x : ι → Kˣ, f x := by
  let c : (ι → Kˣ) ↪ (ι → LimbWords d w) :=
    ⟨fun x i => packScalar B hw (x i), fun x y h => funext fun i => Units.ext <| by
      simpa only [unpack_pack] using congrArg (unpackScalar B) (congrFun h i)⟩
  have henc (x : ι → Kˣ) : packedValue B f (c x) = f x := by
    have h (i : ι) : validLimbs p (c x i) := valid_pack B hw (x i)
    rw [packedValue, dite_eq_left h]
    congr 1
    funext i
    apply Units.ext
    exact unpack_pack B hw (x i)
  calc
    _ = ∑ a ∈ Finset.univ.map c, packedValue B f a := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro a _ ha
      have hn : ¬∀ i, validLimbs p (a i) := by
        intro h
        apply ha
        refine Finset.mem_map.mpr ⟨fun i => Units.mk0 _ (unpack_ne_zero B _ (h i)), Finset.mem_univ _, ?_⟩
        funext i
        exact pack_unpack B hw (a i) (h i).1
      simp [packedValue, hn]
    _ = _ := by simp only [Finset.sum_map, henc]

/-- A concrete prime-field coordinate of a residue row is the count of successful
power-basis limb guesses and final threshold guesses. -/
theorem packed_entry_count [Fintype σ] [Fintype ι] [Field E] [Algebra (ZMod p) E] [Fintype K]
    (B : Basis (Fin d) (ZMod p) K) (hw : p ≤ 2 ^ w) (φ : E →ₐ[ZMod p] K)
    (π : E →ₗ[ZMod p] ZMod p) (π' : K →ₗ[ZMod p] ZMod p) (hπ : π'.comp φ.toLinearMap = π)
    (q : ℕ) (hq : 0 < q) (g : ι → MvPolynomial (Option σ) E)
    (a b : E) (e μ k : Exponent σ) (hwidth : (q - 1) * ∑ t, (g t).totalDegree < Fintype.card Kˣ) :
    π ((rowPolynomial q hq g (RingHom.id E) a b e μ).coeff k) =
      ∑ u : Option σ → LimbWords d w, ∑ y : Fin (2 ^ Nat.clog 2 p),
        if y.val < (packedValue B (fun x => π' (pathSummand φ q g a b e μ k x)) u).val then 1 else 0 := by
  simp_rw [count_prime_weight]
  have hm := entry_eq_pathSum φ.toRingHom q hq g a b e μ k hwidth
  rw [← hπ, LinearMap.comp_apply]
  change π' (φ.toRingHom _) = _
  rw [hm, map_sum]
  convert! (sum_packedValue B hw (fun x => π' (pathSummand φ q g a b e μ k x))).symm using 1 <;>
    apply Finset.sum_congr (Finset.ext fun _ => by simp) <;> intros <;> rfl

end ResidueFourier

end BorderVNP
end Computability
end OAI
