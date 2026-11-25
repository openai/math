import OAI.LinearAlgebra.FiniteFourier.PlaneCopying
import OAI.LinearAlgebra.FiniteFourier.CopySwapCoordinates

/-! # Copying both swap labels to the center

The first and fourth legs share a label across the first diameter. Copying it
does not affect the label shared across the second diameter. A local change of
basis at the center then identifies the two copies with the ordered output pair.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

variable {G : Type} [Fintype G] {K : Type*} [Field K]

private theorem swapRaw_support (w : G × G → K) (z : ∀ i, phaseLeg G G i)
    (hz : (swapRaw w).coeff z ≠ 0) : (z 0 : G) = z 3 ∧ (z 1 : G) = z 2 := by
  rw [swapRaw_coeff] at hz
  unfold weightedSwapEntry at hz
  split at hz
  · assumption
  · contradiction

/-- At the intersection of the two diameters, the pair of output labels
can both be copied to the central leg at zero extra price. -/
theorem copiedSwap_price_le (P : SpectralPlacementPrices K Plane) (hc : PlaneCopying P)
    (w : G × G → K) (p r : Plane) :
    P.price (copiedSwapRaw w) (fun j ↦ j.elim 0 (![p,r,-r,-p] : Fin 4 → Plane)) ≤
      P.price (swapRaw w) ![p,r,-r,-p] := by
  cases isEmpty_or_nonempty G with
  | inl =>
    have h₁ : (copiedSwapRaw w).coeff = 0 := funext fun z ↦ isEmptyElim (α := G) (z (some 0) : G)
    have h₂ : (swapRaw w).coeff = 0 := funext fun z ↦ isEmptyElim (α := G) (z 0 : G)
    rw [P.zero_tensor _ h₁, P.zero_tensor _ h₂]
  | inr =>
    let x : Fin 4 → Plane := ![p,r,-r,-p]
    let y (i : Option (Fin 4)) := i.elim 0 x
    let σ : Fin 3 → Option (Fin 4) := ![some 3, some 0, none]
    let τ : Fin 3 → Option (Fin 4) := ![some 2, some 1, none]
    let e := Fintype.equivFin G
    have h₁ : P.price (firstSwapCopy w) y ≤ P.price ((swapRaw w).group some) y := by
      apply hc.copy_midpoint ((swapRaw w).group some) y σ Fintype.card_pos (thirdSwapLabel w)
        (fun b ↦ e (b ⟨0,rfl⟩))
      · intro z hz
        have he := swapRaw_support w (fun i ↦ z (some i) ⟨i,rfl⟩) hz
        exact congrArg e he.1.symm
      · change p = - -p
        simp
      · rfl
    have h₂ : P.price (secondSwapCopy w) y ≤ P.price (firstSwapCopy w) y := by
      apply hc.copy_midpoint (firstSwapCopy w) y τ Fintype.card_pos (secondSwapLabel w)
        (fun b ↦ e (b.1 ⟨1,rfl⟩))
      · intro z hz
        let old (i : Option (Fin 4)) := (z i).1
        have hold : ((swapRaw w).group some).coeff old ≠ 0 := by
          intro h
          apply hz
          change @ite K _ (Classical.propDecidable _) (((swapRaw w).group some).coeff old) 0 = 0
          rw [h, ite_self]
        have he := swapRaw_support w (fun i ↦ old (some i) ⟨i,rfl⟩) hold
        exact congrArg e he.2.symm
      · change r = - -r
        simp
      · rfl
    calc
      _ = P.price (secondSwapCopy w) y :=
        placed_price_class_eq P y (ofRaw_eq_iff.mpr (secondSwapCopy_equivalent w)).symm
      _ ≤ P.price ((swapRaw w).group some) y := h₂.trans h₁
      _ = _ := (P.group _ some y).symm

/-- A weighted swap with all weights nonzero has the full two-wire price
on a pair of unit diameters. -/
theorem weightedSwap_diameter_lower_of_copying [Nonempty G] (P : SpectralPlacementPrices K Plane)
    (hc : PlaneCopying P) (w : G × G → Kˣ) {p r : Plane} (hp : ‖p‖ = 1) (hr : ‖r‖ = 1) :
    4 * Real.logb 2 (Fintype.card G) ≤ P.price (swapRaw fun j ↦ (w j : K)) ![p,r,-r,-p] :=
  weightedSwap_diameter_lower P w hp hr (copiedSwap_price_le P hc _ p r)

/-- Applying any diagonal multiplier at the center of the copied unweighted swap
produces the weighted swap by one local contraction. -/
theorem weightedSwap_restricts_plain_copied (w : G × G → K) :
    ((swapRaw w).group some).Restricts (copiedSwapRaw (fun _ : G × G ↦ (1 : K))) := by
  apply centralLabel_contracts _ (G × G) w
  intro z
  have h (i j i' j' : G) : weightedSwapEntry w i j i' j' = ∑ t : G × G,
      (@ite K (t = (i',j')) (Classical.propDecidable _)
        (weightedSwapEntry (fun _ ↦ (1 : K)) i j i' j') 0) * w t := by
    by_cases H : i = j' ∧ j = i' <;> simp [weightedSwapEntry, H, ite_mul]
  exact h (z 0) (z 1) (z 2) (z 3)

/-- Nonzero coefficient weights leave the full price of two intersecting
diameters unchanged. This also covers two collinear diameters and the origin. -/
theorem weightedSwap_diameter_price_eq (P : SpectralPlacementPrices K Plane) (w : G × G → Kˣ)
    (p r : Plane) : P.price (swapRaw fun j ↦ (w j : K)) ![p,r,-r,-p] =
      P.price (swapRaw (fun _ : G × G ↦ (1 : K))) ![p,r,-r,-p] := by
  let x : Fin 4 → Plane := ![p,r,-r,-p]
  let y (j : Option (Fin 4)) := j.elim 0 x
  have hc : PlaneCopying P := planeCopying_of_spectralPrices P
  apply le_antisymm
  · calc
      _ = P.price ((swapRaw fun j ↦ (w j : K)).group some) y := P.group _ some y
      _ ≤ P.price (copiedSwapRaw (fun _ : G × G ↦ (1 : K))) y :=
        placed_price_mono P y (weightedSwap_restricts_plain_copied (fun j ↦ (w j : K)))
      _ ≤ _ := copiedSwap_price_le P hc _ p r
  · exact (unweightedSwap_price_le_copied P w x 0).trans (copiedSwap_price_le P hc _ p r)

/-- On unit diameters, the complete weighted swap price is four times the
logarithm of the register dimension. -/
theorem weightedSwap_unit_diameter_price [Nonempty G] (P : SpectralPlacementPrices K Plane)
    (w : G × G → Kˣ) {p r : Plane} (hp : ‖p‖ = 1) (hr : ‖r‖ = 1) :
    P.price (swapRaw fun j ↦ (w j : K)) ![p,r,-r,-p] = 4 * Real.logb 2 (Fintype.card G) := by
  rw [weightedSwap_diameter_price_eq, swapRaw_one_price]
  change (dist p (-p) + dist r (-r)) * _ = _
  have hd (v : Plane) (hv : ‖v‖ = 1) : dist v (-v) = 2 := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ v, norm_smul, hv]
    norm_num
  rw [hd p hp, hd r hr]
  norm_num

end

end

end FiniteFourier
end LinearAlgebra
end OAI
