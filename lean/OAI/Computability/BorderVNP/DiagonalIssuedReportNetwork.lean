import OAI.Computability.BorderVNP.DiagonalFrozenPostReportWords

/-! # Native cable bounds in the returned report's offsets pointer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock.IssuedReportFrame

open VPVNP.BurstRAM Packing.RoutingOutputs

/-- The directory offsets in the report and its control pointer come from its registered network size.
An equality of task layouts identifies these two pointers with those computed from
the physical network at the original site. -/
theorem atPhysicalAddresses {w : ℕ} {physical task : SignedTaskArena.Layout}
    (same : physical = task) {pub : Arg → Word w} {m : Memory w} {origin entries ports rows : ℕ}
    (reported : IssuedReportFrame task pub m (bases origin task.cube.cables task.cube.cells entries).ends
      (controlsBase origin task.cube.cables task.cube.cells entries ports) rows) :
    IssuedReportFrame task pub m (bases origin physical.cube.cables physical.cube.cells entries).ends
      (controlsBase origin physical.cube.cables physical.cube.cells entries ports) rows := by
  subst physical
  exact reported

open Lean Meta Elab Term in
/-- Read the public bank, native addresses and memory from the returned report
itself so elaboration keeps the same occurrence. -/
elab "issuedAtPhysicalNetwork%" same:term:max report:term:max : term => do
  let same ← elabTerm same none
  let report ← elabTerm report none
  let some layouts ← whnfUntil (← inferType same) ``Eq
    | throwError "expected equality of native task layouts"
  let some frame ← whnfUntil (← inferType report) ``IssuedReportFrame
    | throwError "expected a returned native report frame"
  let fields := frame.getAppArgs
  let some ends ← whnfUntil fields[4]! ``Bases.ends | throwError "expected the directory's offsets pointer"
  let some rectangle ← whnfUntil ends.getAppArgs.back! ``bases | throwError "expected native routing addresses"
  let some controls ← whnfUntil fields[5]! ``controlsBase | throwError "expected the native control pointer"
  let layout := layouts.getAppArgs
  let base := rectangle.getAppArgs
  return mkAppN (← mkConstWithLevelParams ``atPhysicalAddresses)
    #[fields[0]!, layout[1]!, layout[2]!, same, fields[2]!, fields[3]!, base[0]!, base[3]!,
      controls.getAppArgs.back!, fields[6]!, report]

end RoutingISA.Evaluator.ScheduleClock.IssuedReportFrame

end BorderVNP
end Computability
end OAI
