import OAI.Computability.BorderVNP.PackedHistoryNormalizedBoundary
import OAI.Computability.BorderVNP.PackedSeedCellRecords
import OAI.Computability.BorderVNP.ShortenPublicBottomFrame

/-! # Physical routes of the grouped initial deck grid -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch Shortening Packing Packing.PhysicalEpochs Packing.DeckGrid
open Diagonal.ExternalSew TeamContraction Shortening.PreparedBins Shortening.PublicCapacity
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {R r t pins link inner n : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (d : ℕ)

variable (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) (copies : ℕ)
local notation "axes" => Fintype.card (Cube D)
local notation "N" => seedBundle G axes d order position copies

/-- Each grouped seed tile and directed channel retains its numbered deck-grid coordinates. -/
noncomputable def seedGeometry : GridShape N axes (d+1) :=
  ⟨Equiv.refl _,Equiv.refl _,fun _ => rfl,fun _ => rfl⟩

local notation "geom" => seedGeometry G d order position copies

/-- The integral lifts of the numbered tiles and the schedule's allowed generator on each
nonlocal directed channel. Grouping the external word retains this physical placement. -/
noncomputable def seedRoutes (table : (N).Tables K) : SiteRoutes (Pack.mk N table) (Cube D) (d+1) S.budget where
  origin := (geom).origin (factorEnum D).symm
  active a := decide ((geom).vertex ((N).src a) ≠ (geom).vertex ((N).dst a))
  step a ha := by
    refine ⟨liftDirection (factorEnum D) a.2,S.generators _ ?_ ?_⟩
    · intro one
      have reduced : DeckGrid.step axes (d+2) a.2 = 1 := by
        funext j
        have h := liftDirection_reduce (factorEnum D) a.2 (d+2) ((factorEnum D) j)
        simpa [one] using h.symm
      have h := of_decide_eq_true ha
      change a.1 ≠ a.1 * DeckGrid.step axes (d+2) a.2 at h
      exact h (by rw [reduced,mul_one])
    · intro i
      by_cases hi : (factorEnum D).symm i = a.2.1
      · right; simpa only [liftDirection,ite_eq_left hi] using a.2.2.property
      · left; simp only [liftDirection,ite_eq_right hi]
  aligned a _ := by
    rw [(geom).origin_reduction,(geom).origin_reduction]
    funext i
    change a.1 ((factorEnum D).symm i) * DeckGrid.step axes (d+2) a.2 ((factorEnum D).symm i) =
      a.1 ((factorEnum D).symm i) * (liftDirection (factorEnum D) a.2 i : Deck (d+2))
    rw [liftDirection_reduce]

/-- The reduced site on every stored route is the original grouped tile in the cube's factor order. -/
theorem seed_origin (table : (N).Tables K) (v : (N).Site) :
    reduceMove (d+1) ((seedRoutes S G d order position copies table).origin v) = GridShape.coordinate (factorEnum D).symm v :=
  (geom).origin_reduction (factorEnum D).symm v

/-- The actual seed has the same nonlocal widths and incidence potential as the physical grid
used by the decay estimates. The weight is independent of the choice of representation. -/
theorem seed_potential (F : Factory D K) (table : (N).Tables K) (weight : ℝ) :
    (seedRoutes S G d order position copies table).potential weight = ((geom).routes (factorEnum D).symm F table).potential weight := rfl

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
