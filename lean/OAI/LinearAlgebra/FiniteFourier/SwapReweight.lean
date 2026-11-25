import OAI.LinearAlgebra.FiniteFourier.SwapWeights

/-! # Reweighting two copied swap labels at a common site -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

variable {I G : Type} {K : Type*} [Field K] [Fintype I] [Fintype G]

/-- A tensor with one extra label at an extra site. -/
def withCentralLabel (A : I → Type) [∀ i, Fintype (A i)] (C : Type) [Fintype C]
    (coeff : C → (∀ i, A i) → K) : Raw (Option I) K where
  Leg := fun i ↦ i.elim C A
  finiteLeg := fun i ↦ by
    cases i with
    | none => exact inferInstanceAs (Fintype C)
    | some i => exact inferInstanceAs (Fintype (A i))
  coeff b := coeff (b none) (fun i ↦ b (some i))

/-- Erasing the central leg with a functional is an actual tensor restriction,
including when the other four sites are subsequently identified. -/
theorem centralLabel_contracts (T : Raw.{0} I K) (C : Type) [Fintype C]
    (a : C → K) (b : C → (∀ i, T.Leg i) → K)
    (h : ∀ z, T.coeff z = ∑ j, b j z * a j) :
    (T.group some).Restricts (withCentralLabel T.Leg C b) := by
  classical
  let _ : DecidableEq (Option I) := Classical.decEq _
  let W := withCentralLabel T.Leg C b
  let A (i : Option I) : (T.group some).Leg i → W.Leg i → K :=
    match i with
    | none => fun _ z ↦ a z
    | some i => fun t z ↦ if z = t ⟨i,rfl⟩ then 1 else 0
  refine ⟨A, fun x ↦ ?_⟩
  let z : ∀ i, T.Leg i := fun i ↦ x (some i) ⟨i,rfl⟩
  let e := Equiv.piOptionEquivProd (β := W.Leg)
  change T.coeff z = _
  rw [h]
  trans ∑ y : C × (∀ i, T.Leg i), W.coeff (e.symm y) * ∏ i, A i (x i) (e.symm y i)
  swap
  · exact Fintype.sum_equiv e.symm
      (fun y ↦ W.coeff (e.symm y) * ∏ i, A i (x i) (e.symm y i))
      (fun y ↦ W.coeff y * ∏ i, A i (x i) (y i)) (fun _ ↦ rfl)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  change b j z * a j = ∑ y : ∀ i, T.Leg i, b j y * ∏ i, A i (x i) (e.symm (j,y) i)
  simp only [Fintype.prod_option]
  change b j z * a j = ∑ y : ∀ i, T.Leg i, b j y *
    ((a j) * ∏ i, (if y i = z i then (1:K) else 0))
  simp [Fintype.prod_boole, ← funext_iff, mul_ite]

/-- Both output labels have been copied to the central site. -/
def copiedSwapRaw (w : G × G → K) : Raw (Option (Fin 4)) K :=
  withCentralLabel (phaseLeg G G) (G × G) fun j z ↦
    if j = (z 2, z 3) then (swapRaw w).coeff z else 0

/-- A nonzero local multiplier on the copied labels can erase the weights. -/
theorem unweightedSwap_restricts_copied (w : G × G → Kˣ) :
    ((swapRaw (fun _ : G × G ↦ (1:K))).group some).Restricts
      (copiedSwapRaw (fun j ↦ (w j : K))) := by
  apply centralLabel_contracts _ (G × G) (fun j ↦ ((w j : K)⁻¹))
  intro x
  let x₀ : G := x 0
  let x₁ : G := x 1
  let x₂ : G := x 2
  let x₃ : G := x 3
  have h (z₀ z₁ z₂ z₃ : G) :
      weightedSwapEntry (fun _ : G × G ↦ (1 : K)) z₀ z₁ z₂ z₃ =
      ∑ j : G × G, @ite K (j = (z₂,z₃)) (Classical.propDecidable _)
        (weightedSwapEntry (fun k ↦ (w k : K)) z₀ z₁ z₂ z₃) 0 * (w j : K)⁻¹ := by
    by_cases hz : z₀ = z₃ ∧ z₁ = z₂ <;> simp [weightedSwapEntry, hz, ite_mul]
  exact h x₀ x₁ x₂ x₃

/-- At the intersection of two diameter wires, deleting nonzero weights costs
at most the price of making copies of their labels at the intersection. -/
theorem unweightedSwap_price_le_copied (P : SpectralPlacementPrices K Plane)
    (w : G × G → Kˣ) (x : Fin 4 → Plane) (O : Plane) :
    P.price (swapRaw (fun _ : G × G ↦ (1:K))) x ≤
      P.price (copiedSwapRaw fun j ↦ (w j : K)) (fun j ↦ j.elim O x) := by
  let y (j : Option (Fin 4)) := j.elim O x
  calc
    _ = P.price ((swapRaw (fun _ : G × G ↦ (1:K))).group some) y := P.group _ some y
    _ ≤ _ := placed_price_mono P y (unweightedSwap_restricts_copied w)

/-- At a placement on two diameters, free copying of the matching labels to
the common center gives the lower bound by the price of the two wires. -/
theorem weightedSwap_diameter_lower [Nonempty G] (P : SpectralPlacementPrices K Plane)
    (w : G × G → Kˣ) {p r : Plane} (hp : ‖p‖ = 1) (hr : ‖r‖ = 1)
    (hcopy : P.price (copiedSwapRaw fun j ↦ (w j : K))
        (fun j ↦ j.elim 0 (![p,r,-r,-p] : Fin 4 → Plane)) ≤
      P.price (swapRaw fun j ↦ (w j : K)) ![p,r,-r,-p]) :
    4 * Real.logb 2 (Fintype.card G) ≤ P.price (swapRaw fun j ↦ (w j : K)) ![p,r,-r,-p] := by
  have h := (unweightedSwap_price_le_copied P w ![p,r,-r,-p] 0).trans hcopy
  rw [swapRaw_one_price] at h
  change (dist p (-p) + dist r (-r)) * _ ≤ _ at h
  have he (v : Plane) (hv : ‖v‖ = 1) : dist v (-v) = 2 := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ v, norm_smul, hv]
    norm_num
  simpa only [he _ hp, he _ hr, show (2:ℝ)+2=4 by norm_num] using h

end

end FiniteFourier
end LinearAlgebra
end OAI
