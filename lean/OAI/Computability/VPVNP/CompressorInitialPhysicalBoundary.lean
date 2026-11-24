import OAI.Computability.VPVNP.CompressorInitialBoundary
import OAI.Computability.VPVNP.CompressorInitialTransferred

/-! # The physical memory entering the selected descriptor timeline

The eight startup calls run on the actual eleven operands. Their linked
report log fixes the memory on which the four cursor visits run. At every
sufficiently large length these visits establish the first boundary and
retain their true smaller-clock source reports.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ScheduledTrace

universe v

open BurstRAM Compression DescriptorSpace BlockPlanner Schedule CursorBounds CursorNetwork CursorRouting
open LiveProgram LiveProgram.CompressedPair PairSimulation.LocalHistory PairSimulation.TraversalRows PairSimulation.TraversalRoles
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
  (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)

private theorem startupRows (p q Baddr n base : ℕ) :
    let A := BlockProgram.script B
    let boot := InitialTransferred.bootstrap B p q
    CalendarRows.rows (bootstrapRows boot A.initial.length A.block.length) n =
      directoryRows (BlockProgram.layout B base (initialPositions Baddr n) (roundedDown p q n)) := by
  intro A boot
  change (BlockProgram.initial B).length + (BlockProgram.block B).length*roundedDown p q n = _
  rw [BlockProgram.layout,LevelFields.tight_rows,Nat.mul_comm]

/-- The same threshold works for every incoming memory and admissible
literal pair-operand vector. The live clock can exceed the source clock. -/
theorem eventually_initial_uniform (p q Baddr : ℕ) (hq : 0 < q) (hB : 1 ≤ Baddr)
    (hθ : (p : ℝ)/q ≤ 1) (hlanes : S.laneBits ≤ Baddr) {base : ℕ → ℕ} (poly : PolynomiallyBounded base) :
    let A := BlockProgram.script B
    let boot := InitialTransferred.bootstrap B p q
    let a := S.degreeExponent 0
    ∃ hd : 2+(2^a-2) = 2^a, ∀ᶠ n : ℕ in Filter.atTop, ∀ {R : Type v} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f), ∀ (pub : Fin 11 → Word (wordBits Baddr n)),
      (pub 2).val = base n → (pub 6).val = n → (pub 7).val = addressBits Baddr n →
      (PairTag.address pub).val < base n → ∀ (m : Memory (wordBits Baddr n)) (terminal : PairTable)
        (outerCap cap small : ℕ),
      StartupResult boot A.plan terminal pub Baddr n (base n) m outerCap →
      InitialScriptPackets.budget A (BlockProgram.layout B 0 0 0) a ≤ small → small ≤ cap →
      Online.Run.ControlBounds A.plan small (w := wordBits Baddr n) →
      let l := roundedDown p q n*S.laneBits
      let b := virtualBits Baddr n-l
      let L := BlockProgram.layout B (base n) (initialPositions Baddr n) (roundedDown p q n)
      let mem := after m (eventLog (cursorStartupLogs boot pub Baddr n (base n) m A.initial.length A.block.length A.size))
      let bits : RAMSystem (virtualBits Baddr n) → ℕ := ramFieldBits (virtualBucket n) (wordBits Baddr n)
      ∃ hD : 1 < b+l, let X := cursorState (cursorCoordinateLabels b l) hD hd bits
        ∃ init : InitialInterval B (base n) (initialPositions Baddr n) (roundedDown p q n) cap small b l (initialWidth Baddr n) pub mem,
          Boundary (CurrentResident.resident B f hf ⟨leafLayer (siteOrder X),.cursor⟩ L (endAddress L) n (cursorFrame L a b l (initialWidth Baddr n))) pub
            (levelWords L : Word (wordBits Baddr n)) (directoryRows L) 4 [] X init.interval.segment.memory ∧
          RAMBuckets.cost Report.probes init.interval.source.logs ≤ initialRate B*(initialPositions Baddr n+1) := by
  intro A boot a
  obtain ⟨hd,prepared⟩ := InitialTransferred.eventually_resident B p q Baddr hq hB hθ hlanes poly
  refine ⟨hd,?_⟩
  filter_upwards [prepared] with n resident
  intro R _ f hf pub ws len addr lower m terminal outerCap cap small start budget leClock bounds l b L mem bits
  obtain ⟨hD,cur⟩ := resident pub ws len addr lower m
  let X := cursorState (cursorCoordinateLabels b l) hD hd bits
  have eqn := InitialTransferred.allocation B p q Baddr n (base n)
  change startupLayout boot A.initial.length A.block.length Baddr n (base n) = L at eqn
  have ready := start.ready
  rw [eqn,startupRows B p q Baddr n (base n)] at ready
  have arena := start.arena
  rw [eqn] at arena
  have fit : endAddress L < 2^(wordBits Baddr n) := arena.symm.trans_lt (mem _).isLt
  obtain ⟨init⟩ := initialInterval B (base n) (initialPositions Baddr n) (roundedDown p q n) cap small b l
    (initialWidth Baddr n) n pub mem X fit ws ready cur budget leClock bounds
  exact ⟨hD,init,init.boundary f hf cur fit,init.rate cur⟩

/-- Specialization to a single scalar solution. -/
theorem eventually_initial (p q Baddr : ℕ) (hq : 0 < q) (hB : 1 ≤ Baddr)
    (hθ : (p : ℝ)/q ≤ 1) (hlanes : S.laneBits ≤ Baddr) {base : ℕ → ℕ} (poly : PolynomiallyBounded base) :
    let A := BlockProgram.script B
    let boot := InitialTransferred.bootstrap B p q
    let a := S.degreeExponent 0
    ∃ hd : 2+(2^a-2) = 2^a, ∀ᶠ n : ℕ in Filter.atTop, ∀ (pub : Fin 11 → Word (wordBits Baddr n)),
      (pub 2).val = base n → (pub 6).val = n → (pub 7).val = addressBits Baddr n →
      (PairTag.address pub).val < base n → ∀ (m : Memory (wordBits Baddr n)) (terminal : PairTable)
        (outerCap cap small : ℕ),
      StartupResult boot A.plan terminal pub Baddr n (base n) m outerCap →
      InitialScriptPackets.budget A (BlockProgram.layout B 0 0 0) a ≤ small → small ≤ cap →
      Online.Run.ControlBounds A.plan small (w := wordBits Baddr n) →
      let l := roundedDown p q n*S.laneBits
      let b := virtualBits Baddr n-l
      let L := BlockProgram.layout B (base n) (initialPositions Baddr n) (roundedDown p q n)
      let mem := after m (eventLog (cursorStartupLogs boot pub Baddr n (base n) m A.initial.length A.block.length A.size))
      let bits : RAMSystem (virtualBits Baddr n) → ℕ := ramFieldBits (virtualBucket n) (wordBits Baddr n)
      ∃ hD : 1 < b+l, let X := cursorState (cursorCoordinateLabels b l) hD hd bits
        ∃ init : InitialInterval B (base n) (initialPositions Baddr n) (roundedDown p q n) cap small b l (initialWidth Baddr n) pub mem,
          Boundary (CurrentResident.resident B f hf ⟨leafLayer (siteOrder X),.cursor⟩ L (endAddress L) n (cursorFrame L a b l (initialWidth Baddr n))) pub
            (levelWords L : Word (wordBits Baddr n)) (directoryRows L) 4 [] X init.interval.segment.memory ∧
          RAMBuckets.cost Report.probes init.interval.source.logs ≤ initialRate B*(initialPositions Baddr n+1) := by
  obtain ⟨hd,allModels⟩ := eventually_initial_uniform B p q Baddr hq hB hθ hlanes poly
  exact ⟨hd,allModels.mono fun _ run => run f hf⟩

end CompressorRecords.ScheduledTrace

end

end VPVNP
end Computability
end OAI
