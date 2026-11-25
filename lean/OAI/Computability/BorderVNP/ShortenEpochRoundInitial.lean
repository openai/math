import OAI.Computability.BorderVNP.CoverLorentzHopFrames
import OAI.Computability.BorderVNP.CoverSiteRoundingLoads

/-!
# The site potential and its initial segment realization

The nonlocal site width `B` counts each active wire once. The incidence
histogram counts both ends. The subdivision of the actual input pack turns the
site potential into the two initial bounds used in the shortening recurrence.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.SiteRoutes

open BorderVNP.Shortening BorderVNP.Epoch Finset
open scoped Classical

variable {D : ℕ} {P R I : Type*} [Fintype I] {bits : P → ℕ} {d : ℕ} {L h : ℝ}
  {p : Pack D P bits R} (s : SiteRoutes p I d L)

/-- Total nonlocal charged width of the site pack. -/
noncomputable def nonlocalWidth : ℝ := ∑ e, if s.active e then (p.layout.width e : ℝ) else 0

/-- Incidence concentration at the start and end sites of every active wire. -/
noncomputable def incidenceConcentration : ℝ := tileConcentration s.incidence

/-- The quantity `I = B + λ Xsite` of Lemma 6.1, evaluated on an actual pack. -/
noncomputable def potential (weight : ℝ) : ℝ := s.nonlocalWidth + weight * s.incidenceConcentration

/-- Nonlocal width and incidence concentration are both nonnegative. -/
theorem nonneg_width_concentration : 0 ≤ s.nonlocalWidth ∧ 0 ≤ s.incidenceConcentration := by
  refine ⟨sum_nonneg (fun _ _ => ?_),mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)⟩
  split_ifs <;> positivity

/-- Initial length and concentration in the precise normalization expected by
`Shortening.exists_shortening_epoch`. Both estimates use the actual geodesic subdivision. -/
theorem initial_for_recurrence (hh : 0 < h) (hL : 0 ≤ L) {weight M : ℝ} (hweight : 0 < weight)
    (hM : s.potential weight ≤ M) :
    chargedLength (p.layout.subdivide (s.routes h)) (s.physical h) (fun j => s.active j.1) ≤ M*L ∧
    tileConcentration (s.midpointBits hh) ≤ M * (Fintype.card (Hop I L h) / weight) := by
  obtain ⟨hw,hx⟩ := s.nonneg_width_concentration
  change s.nonlocalWidth + weight * s.incidenceConcentration ≤ M at hM
  have h1 : s.nonlocalWidth ≤ M := by linarith [mul_nonneg hweight.le hx]
  have h2 : s.incidenceConcentration ≤ M / weight := (le_div_iff₀ hweight).mpr (by linarith)
  constructor
  · apply (s.chargedLength_subdivided hh).trans
    simpa only [nonlocalWidth,mul_comm L] using (mul_le_mul_of_nonneg_right h1 hL)
  have he : tileConcentration (s.midpointBits hh) ≤
      (Fintype.card (Hop I L h) : ℝ)*s.incidenceConcentration := s.initial_midpoint_concentration hh
  exact he.trans ((mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)).trans_eq (by ring))

/-- Subdivision preserves the exact tensor and bounds both modes of the physical record count
with one catalog-dependent constant. -/
theorem initial_tensor_records [Fintype P] [CommSemiring R] (prior payload : p.layout.Site → ℕ) :
    (s.subdivided h).tensor = p.tensor ∧
    ∀ (expanded : Bool) (M : ℕ), (∀ a : I → Deck (d+1), localRecords p.layout expanded prior payload
      (fun v => reduceMove d (s.origin v) = a) ≤ M) →
      ∀ b, 1 + localRecords (s.subdivided h).layout expanded
        (Sum.elim prior (fun _ => 0)) (Sum.elim payload (fun _ => 0))
        (fun v => productAddress d (s.physical h v) = b) ≤
        (1+3*Fintype.card (Option (allowedMoves I L) × Fin (hopCount L h)))*(1+M) := by
  refine ⟨s.tensor_subdivided h,?_⟩
  intro ex M hold b
  have hr := s.localRecords_subdivided_le (h := h) ex prior payload M hold b
  apply (Nat.add_le_add_left hr 1).trans
  rw [Nat.mul_add,Nat.mul_one]
  omega

end Cover.SiteRoutes

end BorderVNP
end Computability
end OAI
