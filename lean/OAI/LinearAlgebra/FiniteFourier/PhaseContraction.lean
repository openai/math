import OAI.LinearAlgebra.FiniteFourier.SwapPrice
import OAI.LinearAlgebra.FiniteFourier.PhaseKernel
import Mathlib.Tactic

/-! # Local contraction of two controlled phases

The six sites carry the four outer legs and the two internal register wires.
At an internal site the local functional pairs the output of the first
phase with the input of the second through the intermediate basis change.
At an outer site it applies the given input or output matrix.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
open scoped Classical BigOperators

section

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

/-- Sites in the concatenation are input, intermediate, and output pairs. -/
def phaseInputSites : Fin 4 → Fin 6 := ![0,1,2,3]
def phaseOutputSites : Fin 4 → Fin 6 := ![2,3,4,5]
def phaseBoundarySites : Fin 4 → Fin 6 := ![0,1,4,5]

variable {K : Type*} [Field K] {G : Type} [Fintype G]

private abbrev Full (G : Type) := (i : Fin 4) → phaseLeg G G i

private def fullEquiv (G : Type) : Full G ≃ (G × G) × (G × G) where
  toFun z := ((z 0,z 1),(z 2,z 3))
  invFun z := phaseCoordinates z.1.1 z.1.2 z.2.1 z.2.2
  left_inv z := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

private abbrev matching (p : G × G) : Full G := phaseCoordinates p.1 p.2 p.1 p.2

private theorem sum_phase (M : Matrix G G K) (F : Full G → K) :
    ∑ a : Full G, (phaseRaw M).coeff a * F a =
      ∑ p : G × G, M p.1 p.2 * F (matching p) := by
  rw [← (fullEquiv G).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single p]
  · change phaseEntry M p.1 p.2 p.1 p.2 * _ = _
    rw [show phaseEntry M p.1 p.2 p.1 p.2 = M p.1 p.2 by simp [phaseEntry]]
    rfl
  · intro q _ hq
    have hne : ¬ (q.1 = p.1 ∧ q.2 = p.2) := fun h ↦ hq (Prod.ext h.1 h.2)
    change (if q.1 = p.1 ∧ q.2 = p.2 then _ else 0) * _ = _
    simp [hne]
  · simp

private theorem sum_pair_phases (M D : Matrix G G K)
    (w : (∀ i, (phaseRaw M).Leg i) → (∀ i, (phaseRaw D).Leg i) → K) :
    (∑ a, ∑ b, (phaseRaw M).coeff a * (phaseRaw D).coeff b * w a b) =
      ∑ i : G × G, ∑ j : G × G, M i.1 i.2 * (D j.1 j.2 * w (matching i) (matching j)) := by
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hf (T : Matrix G G K) (f : (∀ i, (phaseRaw T).Leg i) → K) :
      (∑ a, (phaseRaw T).coeff a * f a) = ∑ p : G × G, T p.1 p.2 * f (matching p) := by
    exact sum_phase T f
  simp_rw [hf D, hf M]

private abbrev GroupLeg (G : Type) (s : Fin 4 → Fin 6) (j : Fin 6) :=
  (t : {i // s i = j}) → phaseLeg G G t.1

private def localContraction (A₀ B₀ A₁ B₁ A₂ B₂ : Matrix G G K) (j : Fin 6) :
    GroupLeg G phaseBoundarySites j →
      GroupLeg G phaseInputSites j × GroupLeg G phaseOutputSites j → K := by
  revert j
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i ↦ i.elim0))))))
  · exact fun x t ↦ A₀ (t.1 ⟨0,rfl⟩) (x ⟨0,rfl⟩)
  · exact fun x t ↦ B₀ (t.1 ⟨1,rfl⟩) (x ⟨1,rfl⟩)
  · exact fun _ t ↦ A₁ (t.2 ⟨0,rfl⟩) (t.1 ⟨2,rfl⟩)
  · exact fun _ t ↦ B₁ (t.2 ⟨1,rfl⟩) (t.1 ⟨3,rfl⟩)
  · exact fun x t ↦ A₂ (x ⟨2,rfl⟩) (t.2 ⟨2,rfl⟩)
  · exact fun x t ↦ B₂ (x ⟨3,rfl⟩) (t.2 ⟨3,rfl⟩)

private def pairGrouping {I J : Type} [Fintype I] [Fintype J] (σ τ : I → J)
    (T U : Raw.{0} I K) :
    ((∀ i, T.Leg i) × (∀ i, U.Leg i)) ≃
      (∀ j, ((T.group σ).mul (U.group τ)).Leg j) :=
  ((groupIndexEquiv σ T.Leg).prodCongr (groupIndexEquiv τ U.Leg)).trans
    (Equiv.arrowProdEquivProdArrow J (T.group σ).Leg (U.group τ).Leg).symm

private theorem sum_grouped_mul {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] (σ τ : I → J)
    (T U : Raw.{0} I K) (w : (∀ j, ((T.group σ).mul (U.group τ)).Leg j) → K) :
    (∑ q, ((T.group σ).mul (U.group τ)).coeff q * w q) =
      ∑ a, ∑ b, T.coeff a * U.coeff b * w (pairGrouping σ τ T U (a,b)) := by
  let f := fun q ↦ ((T.group σ).mul (U.group τ)).coeff q * w q
  change (∑ q, f q) = _
  calc
    _ = ∑ z, f (pairGrouping σ τ T U z) :=
      ((pairGrouping σ τ T U).sum_comp f).symm
    _ = _ := (Fintype.sum_prod_type _).trans (by rfl)

/-- The product of the two phase tensors supplies the complete network
operator by six local linear maps, including arbitrary maps on each
register before, between and after the phases. -/
theorem twoPhase_operatorRaw_restricts {W : Matrix (G × G) (G × G) K}
    (M D A₀ B₀ A₁ B₁ A₂ B₂ : Matrix G G K)
    (hW : ∀ x y, W x y = ∑ i : G × G, ∑ j : G × G, D j.1 j.2 * M i.1 i.2 *
      A₀ i.1 y.1 * B₀ i.2 y.2 * A₁ j.1 i.1 * B₁ j.2 i.2 * A₂ x.1 j.1 * B₂ x.2 j.2) :
    ((operatorRaw W).group phaseBoundarySites).Restricts
      (((phaseRaw M).group phaseInputSites).mul ((phaseRaw D).group phaseOutputSites)) := by
  let act := localContraction A₀ B₀ A₁ B₁ A₂ B₂
  refine ⟨act, fun x ↦ ?_⟩
  let e := pairGrouping phaseInputSites phaseOutputSites (phaseRaw M) (phaseRaw D)
  let Wt (a b : Full G) := ∏ j, act j (x j) (e (a,b) j)
  apply Eq.trans _ (sum_grouped_mul phaseInputSites phaseOutputSites (phaseRaw M) (phaseRaw D)
    (fun q ↦ ∏ j, act j (x j) (q j))).symm
  apply Eq.trans _ (sum_pair_phases M D Wt).symm
  change W _ _ = _
  rw [hW]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Wt, Fin.prod_univ_six]
  change _ = M i.1 i.2 * (D j.1 j.2 *
    (A₀ i.1 (x 0 ⟨0,rfl⟩) * B₀ i.2 (x 1 ⟨1,rfl⟩) *
      A₁ j.1 i.1 * B₁ j.2 i.2 * A₂ (x 4 ⟨2,rfl⟩) j.1 * B₂ (x 5 ⟨3,rfl⟩) j.2))
  change D j.1 j.2 * M i.1 i.2 * A₀ i.1 (x 0 ⟨0,rfl⟩) * B₀ i.2 (x 1 ⟨1,rfl⟩) *
    A₁ j.1 i.1 * B₁ j.2 i.2 * A₂ (x 4 ⟨2,rfl⟩) j.1 * B₂ (x 5 ⟨3,rfl⟩) j.2 = _
  ring

/-- The price of a two-phase kernel is bounded by the sum of the phase prices
for any intermediate positions, even when some of the six sites coincide. -/
theorem twoPhase_price_le (P : SpectralPlacementPrices K Plane)
    (M D A₀ B₀ A₁ B₁ A₂ B₂ : Matrix G G K) (hM : M ≠ 0) (hD : D ≠ 0)
    (A B U V C F : Plane) :
    P.price (operatorRaw (twoPhaseKernel M D A₀ B₀ A₁ B₁ A₂ B₂)) ![A,B,C,F] ≤
      fourierPhasePrice P M ![A,B,U,V] + fourierPhasePrice P D ![U,V,C,F] := by
  let x : Fin 6 → Plane := ![A,B,U,V,C,F]
  have hext : x ∘ phaseBoundarySites = ![A,B,C,F] := by funext i; fin_cases i <;> rfl
  have hin : x ∘ phaseInputSites = ![A,B,U,V] := by funext i; fin_cases i <;> rfl
  have hout : x ∘ phaseOutputSites = ![U,V,C,F] := by funext i; fin_cases i <;> rfl
  let W := twoPhaseKernel M D A₀ B₀ A₁ B₁ A₂ B₂
  have hl := twoPhase_operatorRaw_restricts (W := W) M D A₀ B₀ A₁ B₁ A₂ B₂
    (twoPhaseKernel_apply M D A₀ B₀ A₁ B₁ A₂ B₂)
  have h := placed_price_mono P x hl
  rw [placed_price_mul P x _ _ (((phaseRaw M).group_ne_zero_iff _).mpr (phaseRaw_coeff_ne_zero.mpr hM))
    (((phaseRaw D).group_ne_zero_iff _).mpr (phaseRaw_coeff_ne_zero.mpr hD)),
    ← P.group, ← P.group, ← P.group, hext, hin, hout] at h
  exact h

/-- A concrete two-phase realization gives one weighted swap whose price is
bounded by those of the phases at every placement of the internal registers. -/
theorem TwoPhasesGiveWeightedSwap.exists_price_le {M : Matrix G G K}
    (h : TwoPhasesGiveWeightedSwap M) (P : SpectralPlacementPrices K Plane) (hM : M ≠ 0) :
    ∃ w : G × G → Kˣ, ∀ A B U V C F : Plane,
      P.price (swapRaw (fun t ↦ (w t : K))) ![A,B,C,F] ≤
        fourierPhasePrice P M ![A,B,U,V] + fourierPhasePrice P M ![U,V,C,F] := by
  obtain ⟨A₀,B₀,A₁,B₁,A₂,B₂,w,hw⟩ := h.exists_kernel_eq
  change twoPhaseKernel M M A₀ B₀ A₁ B₁ A₂ B₂ = weightedSwapMatrix (fun t ↦ (w t : K)) at hw
  refine ⟨w, fun A B U V C F ↦ ?_⟩
  simpa only [hw, swapRaw] using twoPhase_price_le P M M A₀ B₀ A₁ B₁ A₂ B₂ hM hM A B U V C F

end

end

end FiniteFourier
end LinearAlgebra
end OAI
