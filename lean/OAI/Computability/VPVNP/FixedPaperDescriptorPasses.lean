import OAI.Computability.VPVNP.CompressorNativeLocatedRuns
import OAI.Computability.VPVNP.LiveCompressedPairDescriptorRoom
import OAI.Computability.VPVNP.FixedPaperPairRuns

/-! # The descriptor passes of the fixed paper program

The public workspace is the address evaluated by the paper program's
layout. Both physical pass compilers run at the common small clock inside
the same eleven-operand table. Their common length threshold applies before
the exceptional field model, its label solution and its virtual pair.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace FixedProgramDiagonal.Program
open Compression CursorNetwork CursorBounds BurstRAM LiveProgram LiveProgram.CompressedPair Filter
open CompressorRecords ScheduledTrace DescriptorSpace LabelEvaluator PairSimulation.LocalHistory
open PairSimulation.TraversalRoles PairSimulation.TraversalRows PairStages PairStages.Group PairStages.Group.CompressedPaths LocalCount
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (u : PairExponents B.growthConstant)
variable (c : Constants) (labels : c.motifLabels = Fintype.card B.Entry)
variable (E : UniversalMachine.Program) (addr : ℕ) (positive : 1 ≤ addr) (C : ℕ)
attribute [local irreducible] BlockProgram.script BlockProgram.layout BlockClock.small
local notation "D" => paperProgram B u c labels E addr positive

/-- The fixed paper program executes each selected pass at the public address supplied by the group. -/
theorem eventually_paperPasses :
    ∀ᶠ n : ℕ in atTop, PaperPasses B u c labels E addr positive C (descriptorRate B) n := by
  filter_upwards [eventually_locatedRuns.{0,0} B addr positive, eventually_descriptor_room B u c labels E addr positive,
    eventually_clocks B addr positive] with n run room clocks
  intro hn V p M
  let G := (D).executionGroup n ((D).tagsFit n) (dispatchClock hn)
  let pub : Fin 11 → Word (wordBits addr n) := publicWords G
  let base := (LiveProgram.Layout.pairWorkspace c).eval ((D).geometry n)
  let blocks := blockCount (u.θ : ℝ) n
  let pos := initialPositions addr n
  let L := BlockProgram.layout B base pos blocks
  let f := B.compressorValues hn M
  let hf := B.compressorValues_solution hn M
  let cap := sourceCap pub (fuel G)
  let initial := PairSimulation.TraversalRoles.TaggedLayer.mk (leafLayer (siteOrder V.scanState)) .cursor
  let frame : Fin 8 → Word (wordBits addr n) := cursorFrame L (S.degreeExponent 0) (virtualBits addr n-reservedLanes B u n)
    (reservedLanes B u n) (initialWidth addr n)
  obtain ⟨hw,space,ctrl⟩ := room ((D).tagsFit n) (dispatchClock hn)
  change (pub 2).val = base at hw
  have hclk := (clocks.2.2 G pub rfl).1
  have native : LocatedRuns (CompiledResident.resident B f hf (pub 2) pos blocks n initial frame)
      pub (levelWords (BlockProgram.layout B (pub 2).val pos blocks))
      (directoryRows (BlockProgram.layout B (pub 2).val pos blocks)) cap (BlockClock.small B addr n)
      (nativePassRate (BlockProgram.script B) (descriptorRate B) * pos) blocks pos n :=
    run f hf pub blocks cap initial frame space (by exact (Nat.le_add_right _ 3).trans hclk)
    (ctrl _ le_rfl)
  have address : (base : Word (wordBits addr n)) = pub 2 := by
    apply Fin.ext
    rw [Fin.val_natCast,← hw]
    exact Nat.mod_eq_of_lt (pub 2).isLt
  change LocatedRuns (V.nativeResident f hf base (CompiledResident.payload (w := wordBits addr n) B f hf
    (base : Word (wordBits addr n)) pos blocks n)) pub (levelWords L) (directoryRows L) cap (BlockClock.small B addr n)
    (nativePassRate (BlockProgram.script B) (descriptorRate B)*pos) blocks pos n
  rw [address]
  change LocatedRuns (DetailedResident.resident B f hf initial L (endAddress L) n frame
    (CompiledResident.payload B f hf (pub 2) pos blocks n)) pub (levelWords L) (directoryRows L) _ _ _ _ _ _
  simpa only [CompiledResident.resident,hw,L] using @native

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
