import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask

/-! # Identifying the issued signed report arena with the frozen task's cube -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Cover Crossing Epoch PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open Packing RoutingISA TeamScales _root_.OAI.Computability.BorderVNP.Cube GeometryAdvice TeamContraction.ProcessorSlots
open scoped Classical BorderVNP.Epoch.Cube

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m} {S : SiteSchedule G}
    {extra E dlog Q A B j : ℕ} (cube : FixedCube K) {s : EpochScales S (cube.pred+1) extra}
    (b : JointSchedule.{0} s (E+1) dlog Q A B j)

/-- The finite numbering of the attained geometry and the frozen physical
lengths define the same routed packet, vertex and receiving-cell banks. -/
theorem JointSchedule.frozenSignedTask_reportCube (k size headerFactor : ℕ) (initial : StartupArena)
    (dir : Directory.Layout) (reserve ceiling outputs field : ℕ) (dirs : SignedTaskArena.GeometryDirectories)
    {r R d T cells : ℕ} (length : r=stretch b.ρ (k+1))
    (level : CoverScale.initialDepth (Epoch.Cube D) r (k+1)=d+1)
    (epochsEq : T=epochs s.τ (k+1)) (teams : R=b.physical.teamsPred (k+1))
    (number : (Epoch.Cube D → Deck (EnrichedOuter.depth S (d+1) T+1)) ≃ Fin cells) :
    let base := Allocation.stop (initial.next+7*dir.candidates) reserve ceiling outputs field (b.physical.word (k+1))
    (b.frozenSignedTask cube (k+1) k size headerFactor initial dir reserve ceiling outputs field dirs).cube =
      (CubeArena.selectedSizes base (alphabet s.α (k+1)) ((R+1)*exterior ((s.τ:ℝ)/5) r (k+1))
        cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Epoch.Cube D) (d+1)))
        dir.candidates (R+1) r (k+1) reserve).selected cube.pred cube.b cube.h cube.copies cube.width := by
  have count : cells=CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S (d+1) T) := by
    simpa only [CoverScale.sites,Fintype.card_fin] using (Fintype.card_congr number).symm
  dsimp only [frozenSignedTask]
  rw [←length,level,←epochsEq,←teams,count]

/-- The complete signed task also agrees. Both forms use the very same
finite scalar numbering and length-only report reservation. -/
theorem JointSchedule.frozenSignedTask_reportLayout (k size headerFactor : ℕ) (initial : StartupArena)
    (dir : Directory.Layout) (reserve ceiling outputs field : ℕ) (dirs : SignedTaskArena.GeometryDirectories)
    {r R d T cells : ℕ} (length : r=stretch b.ρ (k+1))
    (level : CoverScale.initialDepth (Epoch.Cube D) r (k+1)=d+1)
    (epochsEq : T=epochs s.τ (k+1)) (teams : R=b.physical.teamsPred (k+1))
    (number : (Epoch.Cube D → Deck (EnrichedOuter.depth S (d+1) T+1)) ≃ Fin cells) :
    let base := Allocation.stop (initial.next+7*dir.candidates) reserve ceiling outputs field (b.physical.word (k+1))
    let frozen := b.frozenSignedTask cube (k+1) k size headerFactor initial dir reserve ceiling outputs field dirs
    let reported := (CubeArena.selectedSizes base (alphabet s.α (k+1)) ((R+1)*exterior ((s.τ:ℝ)/5) r (k+1))
        cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Epoch.Cube D) (d+1)))
        dir.candidates (R+1) r (k+1) reserve).selected cube.pred cube.b cube.h cube.copies cube.width
    frozen=⟨reported,cube.cubeID G,frozen.p⟩ := by
  have count : cells=CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S (d+1) T) := by
    simpa only [CoverScale.sites,Fintype.card_fin] using (Fintype.card_congr number).symm
  dsimp only [frozenSignedTask]
  rw [←length,level,←epochsEq,←teams,count]

end Diagonal

end BorderVNP
end Computability
end OAI
