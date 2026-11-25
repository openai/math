import OAI.Hierarchy.ProbePublicGeometry
import OAI.Hierarchy.ProbeStrictActivation
import OAI.Hierarchy.ProbePurchaseFunding
import OAI.Hierarchy.ProbeStripThreshold

namespace OAI
/-! # Public geometry and prices shared by all input lengths, selectors and mesh phases -/

namespace Hierarchy.AdaptiveProbe
open ProbeStage Filter
open scoped BigOperators Classical
noncomputable section

def probeHeat (W : ℕ) : ℝ := (dyadicScale W)^2
def probeResolution (k W : ℕ) : ℝ := probeHeat W/(100*k)
def probeMotion (k W : ℕ) : ℝ := (probeHeat W)^2/(4*k)
def probeBonus (W : ℕ) : ℝ := (W:ℝ)⁻¹^4/(publicStages W*(probeHeat W)^2)
def probeDensity (k W : ℕ) : ℝ := probeMotion k W*publicStages W/(2*publicTiles k W)

/-- A single full calibration for the two kinds of real failed tests. All fields
are consequences of a missing next flat and arithmetic of the chosen dyadic scale. -/
structure PublicCalibration (F : Type*) [Field F] (k : ℕ) (p σ Λ : ℝ) (W M : ℕ) (ε : ℝ) : Prop where
  wide : max 9 (2*k+1)≤W
  large : 2≤M
  accurate : 0<ε
  tiles : 0<publicTiles k W
  motion_mass : (publicStages W:ℝ)*probeHeat W≤1/4
  length_floor : Λ*(dyadicScale W)^σ≤1
  core_capacity : Λ*(1+2*k)*(publicStages W:ℝ)*(dyadicScale W)^p≤1
  acquisition_fee : Λ*(dyadicScale W)^p≤(probeBonus W*probeMotion k W/8)/2
  early : (W:ℝ)⁻¹^4*(1+2*(k:ℝ)/(probeHeat W)^2)*(dyadicScale W)^8≤(W:ℝ)⁻¹^2
  cooling : (W:ℝ)⁻¹^2*(1-Real.log ((dyadicScale W)^8))≤1
  payload : ∀ (P : Type) [Fintype P] (name : P→PayloadStrip.Naming (publicStages W) k)
    (x : Commodity P (publicStages W) k → ℝ),
    (∀i,PayloadStrip.rowQuotes x i∈Set.Icc 0 (PayloadStrip.ceiling (publicStages W) k M)) →
    readings M x≤Fintype.card P*(publicStages W:ℝ)*(probeHeat W)^2 →
    (∑i,PayloadStrip.namedError F (publicStages W) k (name i) M (PayloadStrip.rowQuotes x i)) ≤
      Fintype.card P*ε/(2*(publicStages W+1)) → (∑i,x (.inl i))≤Fintype.card P
  purchase : StrictPayment F (publicTiles k W-1) k M (probeResolution k W) ε
  cutoff : 0<failureTolerance (publicStages W) ε (probeDensity k W) ∧ ∀n : ℕ,
    5*failureTolerance (publicStages W) ε (probeDensity k W)*n≤(n:ℝ)*ε/(2*(publicStages W+1)) ∧
    5*failureTolerance (publicStages W) ε (probeDensity k W)*n≤probeDensity k W*n*ε/4

theorem public_calibration {F : Type*} [Field F] (k : ℕ) (hk : 0<k) (no : ¬HasSpectralFlat F (k+1))
    {p σ Λ : ℝ} (hp : 1<p) (hσ : 0<σ) (hΛ : 0<Λ) :
    ∀ᶠ W : ℕ in atTop, ∃M₀ : ℕ, ∀ M≥M₀, ∃ε : ℝ, PublicCalibration F k p σ Λ W M ε := by
  filter_upwards [public_geometry (F:=F) k hk no hp hσ hΛ,affordable_advised hp hσ hΛ (by norm_num : (0:ℝ)<1/4) k,eventually_ge_atTop (max 9 (2*k+1))] with W geom cheap wide
  obtain ⟨tiles,unit,core,charge,M₀,atM⟩ := geom
  have costs := cheap 0 (Equiv.refl (Fin (2^0)))
  simp only [advised_length] at costs
  refine ⟨max 2 M₀,?_⟩
  intro M big
  obtain ⟨ε,accurate,transfer,read⟩ := atM M ((le_max_right ..).trans big)
  have wr : 0<(W:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<9) ((le_max_left ..).trans wide))
  have kr : 0<(k:ℝ) := Nat.cast_pos.mpr hk
  have nr : 0<(publicStages W:ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hr : 0<(publicTiles k W:ℝ) := Nat.cast_pos.mpr tiles
  have t : 0<dyadicScale W := by unfold dyadicScale; positivity
  have heat : 0<probeHeat W := pow_pos t _
  have positive : 0<probeDensity k W := by unfold probeDensity probeMotion; positivity
  refine ⟨ε,wide,(le_max_left ..).trans big,accurate,tiles,costs.2.2.2,unit,core,?_,
    dyadic_small_time k W ((le_max_right ..).trans wide),
    (dyadic_cooling_integral W ((le_max_left ..).trans wide)).2.2,transfer,
    strict_activation_of_reads _ _ accurate read,failure_tolerance accurate positive⟩
  apply fee_affordable wr kr nr heat
  convert charge using 1; ring

end
end Hierarchy.AdaptiveProbe

end OAI
