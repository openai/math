import OAI.Computability.BorderVNP.ShortenPlacedStep

/-!
# Measured inputs to a physical shortening node

A verified motion contributes its bin mean, matching guarantee, midpoint
tile names, and measured deviation. These data give the two recurrence
rows with the actual arithmetic average and maximum over the node's own
children. All these hypotheses concern the motion and the original wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PlacedStep

open Crossing Cover CombiningStep Epoch SeedIntervals Packing Finset
open scoped Classical

variable {D m d d' k : ℕ} [NeZero D] {K : Type*} [Field K] {I : Type} [Fintype I]
    {P B : Type} {bits : P → ℕ} [Fintype B] {child : Fin k → PlacedPack D P bits K I d}

/-- The largest midpoint concentration among the actual children. -/
noncomputable def childMaximum (child : Fin k → PlacedPack D P bits K I d) (hk : 0 < k) : ℝ :=
  univ.sup' ⟨⟨0,hk⟩,mem_univ _⟩ fun i => (child i).concentration

/-- Measurements and exact geometric identifications for the publicly
chosen motions, before sorting or inserting any profile. -/
structure Measurements (s : PlacedStep m B d' child) (hk : 0 < k) (h ν u v : ℝ) where
  /-- Actual integer-count bin means, including the uniform deck shift. -/
  mean : ((I → Deck (d'+1)) × B) → ℝ
  /-- Chosen midpoints of the moved input cables, used for address lookup. -/
  oldMid : (parallelPacks fun i => (child i).pack).layout.Edge → SurfaceHost I (d'+1)
  /-- Public address of each moved cable when it participates in the matching. -/
  addr : (parallelPacks fun i => (child i).pack).layout.Edge → ((I → Deck (d'+1)) × B)
  /-- The selected motions preserve all width-weighted distances cable by cable. -/
  keeps : s.KeepsLength
  /-- Endpoint lifts in the selected bins fit the canonical chart. -/
  fits : s.placed.fits _ s.bin s.perm s.positive h ν
  /-- The midpoint tag agrees with the actual address and is within half the cable length. -/
  midpoint : ∀ c a, s.bin c = some a → addr c = a ∧ a.1 = productTileName d' (oldMid c) ∧
    dist (oldMid c) (s.placed.old ((parallelPacks fun i => (child i).pack).layout.src c)) ≤
    dist (s.placed.old ((parallelPacks fun i => (child i).pack).layout.src c))
      (s.placed.old ((parallelPacks fun i => (child i).pack).layout.dst c)) / 2
  /-- A seed and its signed direction permutations retain the same center tile. -/
  center : ∀ a, (s.perm 0 a).1 = productTileName d' (s.placed.project a (s.placed.chart a).center)
  /-- The true motion mean covers at least half of the input's average length. -/
  half : (s.placed.input _ s.bin s.perm / k) / 2 ≤ matchedLength s.perm
    (fun a => 2*(s.placed.chart a).radius) mean
  /-- The exact tile marginal and minimum segment length bound the mean norm. -/
  norm : Real.sqrt (Fintype.card (I → Deck (d'+1))) * Real.sqrt (binEnergy mean) ≤
    u * (s.placed.input _ s.bin s.perm / k)
  /-- Equation (6.2) for the publicly chosen motions of these children. -/
  deviation : Real.sqrt (Fintype.card (I → Deck (d'+1))) *
    Real.sqrt (binEnergy fun a => count (parallelPacks fun i => (child i).pack).layout s.bin a / k - mean a) ≤
      v * childMaximum child hk / Real.sqrt k

/-- A stage coefficient chosen before the quotient levels, the fan-in, the
child states and all their histograms. -/
def Calibration (e : PaidIdentity K D m) (I B : Type) [Fintype I] [Fintype B] (h ν u v C : ℝ) : Prop :=
      ∀ {P : Type} {bits : P → ℕ} {d d' k : ℕ} (hk : 0 < k)
      (child : Fin k → PlacedPack D P bits K I d) (s : PlacedStep m B d' child),
      Measurements s hk h ν u v → ∀ (V : ℝ), (Fintype.card (I → Deck (d'+1)) : ℝ) ≤ V →
      ∀ q : s.Index e,
      let W := (∑ i, (child i).length) / k
      let X := childMaximum child hk
      (s.result e q).length / k ≤ max 0 (1-(ν/2)/2) * W + C * (Real.sqrt k)⁻¹ * X + C * V ∧
      (s.result e q).concentration / k ≤ C * (W + (Real.sqrt k)⁻¹ * X)

/-- The two exact recurrence rows for measured physical nodes, with the
saving and scale chosen before the relative bins and before all levels. -/
theorem measured_rows (e : PaidIdentity K D m) (hm : 0 < m) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ h : ℝ, 0 < h ∧ ∀ (B : Type) [Fintype B]
      (u v : ℝ), 0 ≤ u → 0 ≤ v → ∃ C : ℝ, 0 ≤ C ∧
      Calibration e I B h ν u v C := by
  obtain ⟨ν,hν,h,hh,uniform⟩ := physical_rows (I := I) e hm
  refine ⟨ν,hν,h,hh,?_⟩
  intro B _ u v hu hv
  obtain ⟨C,hC,bound⟩ := uniform (B := B) u v hu hv
  refine ⟨C,hC,?_⟩
  intro P bits d d' k hk child s data V hV q W X
  let z : Fin k := ⟨0,hk⟩
  have hX : 0 ≤ childMaximum child hk := by
    unfold childMaximum
    exact (PlacedPack.nonneg (child z)).2.trans
      (Finset.le_sup' (s := (Finset.univ : Finset (Fin k))) (fun i => (child i).concentration) (mem_univ z))
  have h := bound d' k hk _ s.bin s.perm s.positive s.placed data.fits
    data.oldMid data.addr data.midpoint data.center data.mean _ V hX hV data.half data.norm data.deviation q
  rw [s.input_length data.keeps] at h
  exact h

end Shortening.PlacedStep

end BorderVNP
end Computability
end OAI
