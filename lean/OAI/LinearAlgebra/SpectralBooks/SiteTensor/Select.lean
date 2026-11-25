import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Identity
import OAI.LinearAlgebra.SpectralBooks.Prices
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.WireProduct

/-! # Following a nonzero child of an exterior split

At a chosen placement, ordinary addition selects a nonzero child within one
scale factor of the parent tensored with the exterior-level wire.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace SiteTensor.Relocation

open Exterior

variable {I J : Type} {K : Type*} {A : I → Type} [Fintype I] [Fintype J]
  [Nonempty J] [∀ i, Fintype (A i)] [Field K] {Q b : ℕ}

/-- A winning child is nonzero before grouping, so it may be used at any
subsequent placement in the splitting recursion. -/
theorem select_split (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    {scale : ℝ} (hscale : 0 ≤ scale) (T : (∀ i, A i) → Fin Q → K)
    (hT : (marked A (Fin Q) T).coeff ≠ 0) [Nonempty (Level Q (b + 1))]
    (σ : I → J) (c a d : J) :
    let parent := (marked A (Fin Q) T).group (placeMark σ c)
    let W := wire K (Level Q (b + 1)) a d
    let upper := split A (Fin Q) (Level Q (b + 1)) (plusCoeff T (create K) (contract K))
    let lower := split A (Fin Q) (Level Q (b + 1)) (minusCoeff T (contract K) (create K))
    (upper.coeff ≠ 0 ∧ rawLogPrice φ scale parent + rawLogPrice φ scale W ≤
      rawLogPrice φ scale (upper.group (placeSplit σ c a d)) + scale) ∨
    (lower.coeff ≠ 0 ∧ rawLogPrice φ scale parent + rawLogPrice φ scale W ≤
      rawLogPrice φ scale (lower.group (placeSplit σ c a d)) + scale) := by
  let H := Level Q (b + 1)
  let f := placeSplit σ c a d
  let V (v : (∀ i, A i) → Fin Q → H → H → K) := (split A (Fin Q) H v).group f
  let P := V (fun x i α β => T x i * if α = β then 1 else 0)
  let U := (marked A (Fin Q) T).group (placeMark σ c)
  let W := wire K H a d
  have hw : W.coeff ≠ 0 := by
    apply (Raw.group_ne_zero_iff ..).mpr
    intro h
    have hz := congrFun h (fun _ => Classical.arbitrary H)
    change (Raw.diagonal (Fin 2) K H).coeff (fun _ => Classical.arbitrary H) = 0 at hz
    simp [Raw.diagonal_coeff_at (0 : Fin 2)] at hz
  have hu : U.coeff ≠ 0 := (Raw.group_ne_zero_iff ..).mpr hT
  have hp : ofRaw P = ofRaw U * ofRaw W := grouped_split_eq_mul T H σ c a d
  have hpn : P.coeff ≠ 0 := by
    apply (ofRaw_eq_zero_iff P).not.mp
    rw [hp]
    exact mul_ne_zero ((ofRaw_eq_zero_iff U).not.mpr hu) ((ofRaw_eq_zero_iff W).not.mpr hw)
  have hpprice : rawLogPrice φ scale P = rawLogPrice φ scale U + rawLogPrice φ scale W := by
    rw [← rawLogPrice_mul φ scale U W hu hw]
    simp only [rawLogPrice, ofRaw_mul, hp]
  let s : (∀ j, P.Leg j) → K := (V (plusCoeff T (create K) (contract K))).coeff
  let t : (∀ j, P.Leg j) → K := (V (minusCoeff T (contract K) (create K))).coeff
  have he : P.coeff = s + t := funext fun _ => (plus_add_minus_eq T _ _ _ _).symm
  have hval : rawLogPrice φ scale ⟨P.Leg, P.finiteLeg, s + t⟩ = rawLogPrice φ scale P := by
    rw [← he]
  rcases rawLogPrice_add_select φ scale hscale s t (he ▸ hpn) with ⟨hs, hb⟩ | ⟨ht, hb⟩
  · rw [hval, hpprice] at hb
    exact Or.inl ⟨(Raw.group_ne_zero_iff ..).mp hs, hb⟩
  · rw [hval, hpprice] at hb
    exact Or.inr ⟨(Raw.group_ne_zero_iff ..).mp ht, hb⟩

end SiteTensor.Relocation

end

end SpectralBooks
end LinearAlgebra
end OAI
