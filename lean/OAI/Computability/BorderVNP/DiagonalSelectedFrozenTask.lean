import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask

/-! # The scheduled and deployed signed evaluator have the same task layout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing Cover Packing ExternalSew PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open TeamScales RoutingISA RoutingISA.SignedTaskArena RoutingISA.CubeArena TeamContraction TeamContraction.JointHeader
open TeamContraction.ProcessorSlots GeometryAdvice _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {paid : PaidIdentity F D m}
    {schedule : SiteSchedule paid} {extra E dlog Q A B j : ℕ} (cube : FixedCube K)
    {scales : EpochScales schedule (cube.pred+1) extra} (b : JointSchedule.{0} scales (E+1) dlog Q A B j)

/-- At the selected batch size, depth and epoch count, the length-only task
is the physical layout above the reserved geometry table. Its marked sites
and description size come from the actual initial seed. Its two scalar blocks
are the paid entries followed by the cube entries. -/
theorem JointSchedule.frozenSignedTask_eq_selected {k r R rw d T cells : ℕ} {α ξ : ℝ}
    (size headerFactor : ℕ) (initial : StartupArena) (dir : Directory.Layout)
    (reserve ceiling outputs field : ℕ) (dirs : GeometryDirectories)
    (batch : r = stretch b.ρ (k+1)) (groups : R = b.physical.teamsPred (k+1))
    (wordSize : rw = b.physical.word (k+1)) (depthEq : d+1 = CoverScale.initialDepth (Epoch.Cube D) r (k+1))
    (time : T = epochs scales.τ (k+1)) (alpha : α = (scales.α : ℝ)) (rate : ξ = (scales.τ : ℝ)/5)
    (number : (Epoch.Cube D → Deck (EnrichedOuter.depth schedule (d+1) T+1)) ≃ Fin cells) :
    b.frozenSignedTask cube (k+1) k size headerFactor initial dir reserve ceiling outputs field dirs =
      let V := CoverScale.sites (Epoch.Cube D) (d+1)
      let axes := Fintype.card (Epoch.Cube D)
      let arenaBase := Allocation.stop (initial.next+7*dir.candidates) reserve ceiling outputs field rw
      let cubeArena := (CubeArena.selectedSizes arenaBase (_root_.OAI.Computability.BorderVNP.Cube.alphabet α (k+1))
          ((R+1)*exterior ξ r (k+1)) cells ((boundary schedule (d+1) T).edges+4*((R+1)*V))
          dir.candidates (R+1) r (k+1) reserve).selected cube.pred cube.b cube.h cube.copies cube.width
      let parameters := physicalParameters cubeArena dirs (k+1) ((EnrichedOuter.fan schedule)^T*V)
          (DeckGrid.seedSiteCapacity (k+1) r axes d) (pairedTableParameters (k+1) size) (Nat.clog 2 (r*(2*k+1)+1))
          (Fintype.card (paid.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width)) rw
          (headerFactor*logWidth r (k+1)) (BottomGridBank.bodyBudget
            (DeckGrid.seedBoxCapacity (k+1) r axes d (Fintype.card (DeckGrid.Direction axes))))
      SignedTaskArena.Layout.mk cubeArena (cube.cubeID paid) parameters := by
  have count : CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth schedule (d+1) T) = cells := by
    simpa only [CoverScale.sites,Fintype.card_fin] using Fintype.card_congr number
  subst r R rw T α ξ cells
  dsimp only [JointSchedule.frozenSignedTask]
  rw [←depthEq]
  rfl

/-- The gap before the opaque private descriptions has the same quadratic
length on the scheduled signed task as on the deployed one. -/
theorem JointSchedule.frozenSignedTask_privateGap (n l size headerFactor : ℕ) (initial : StartupArena)
    (dir : Directory.Layout) (reserve ceiling outputs field : ℕ) (dirs : GeometryDirectories) :
    (b.frozenSignedTask cube n l size headerFactor initial dir reserve ceiling outputs field dirs).p.privateGap = n^2 := rfl

end Diagonal

end BorderVNP
end Computability
end OAI
