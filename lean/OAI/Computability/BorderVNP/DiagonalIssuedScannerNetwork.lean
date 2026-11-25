import OAI.Computability.BorderVNP.FragmentRowsSparseLaunch

/-! # Scanner results at the original report's physical network addresses -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows.SparseGeometry

open Packing.RoutingOutputs

/-- A returned fragment's sparse directory lies at the offsets and control
pointers of the physical network identified by the registered task. -/
theorem atPhysicalAddresses {physical planner : SignedTaskArena.Layout}
    (same : physical = planner) {f : FragmentRows.Layout} {origin entries ports : ℕ}
    (stored : SparseGeometry planner f (bases origin planner.cube.cables planner.cube.cells entries).ends
      (controlsBase origin planner.cube.cables planner.cube.cells entries ports)) :
    SparseGeometry planner f (bases origin physical.cube.cables physical.cube.cells entries).ends
      (controlsBase origin physical.cube.cables physical.cube.cells entries ports) := by
  subst physical
  exact stored

open Lean Meta Elab Term in
/-- Recover the emitted record's own directory and native port count when the
scanner is consumed at the original network. -/
elab "issuedAtPhysicalGeometry%" same:term:max record:term:max : term => do
  let same ← elabTerm same none
  let record ← elabTerm record none
  let some layouts ← whnfUntil (← inferType same) ``Eq | throwError "expected equality of native layouts"
  let some geometry ← whnfUntil (← inferType record) ``SparseGeometry | throwError "expected native fragment geometry"
  let fields := geometry.getAppArgs
  let some ends ← whnfUntil fields[2]! ``Bases.ends | throwError "expected directory offsets"
  let some rectangle ← whnfUntil ends.getAppArgs.back! ``bases | throwError "expected native routing addresses"
  let some controls ← whnfUntil fields[3]! ``controlsBase | throwError "expected the native control pointer"
  let layout := layouts.getAppArgs
  let base := rectangle.getAppArgs
  return mkAppN (← mkConstWithLevelParams ``atPhysicalAddresses)
    #[layout[1]!, layout[2]!, same, fields[1]!, base[0]!, base[3]!, controls.getAppArgs.back!, record]

/-- All 37 words read on the original emission agree at the physical
routing rectangle of the same signed task. -/
theorem controlsAtPhysicalAddresses {w : ℕ} {physical planner : SignedTaskArena.Layout}
    (same : physical = planner) {m : VPVNP.BurstRAM.Memory w} {origin entries ports : ℕ}
    (words : ∀ i : Fin 37, readings m
      (controlsBase origin planner.cube.cables planner.cube.cells entries ports + i.val) =
      planner.controls i.val) :
    ∀ i : Fin 37, readings m (controlsBase origin physical.cube.cables physical.cube.cells entries ports + i.val) =
      planner.controls i.val := by
  subst physical
  exact words

open Lean Meta Elab Term in
/-- Recover the saved RAM and address from the quantified control-word proof
produced by the returning scanner. -/
elab "issuedControlsAtPhysicalNetwork%" same:term:max words:term:max : term => do
  let same ← elabTerm same none
  let words ← elabTerm words none
  let some layouts ← whnfUntil (← inferType same) ``Eq | throwError "expected equality of task layouts"
  forallBoundedTelescope (← inferType words) (some 1) fun _ point => do
    let some equality ← whnfUntil point ``Eq | throwError "expected a native control-word equality"
    let some read ← whnfUntil equality.getAppArgs[1]! ``readings | throwError "expected the returned report RAM"
    let some index ← whnfUntil read.getAppArgs.back! ``Nat.add | throwError "expected the control slot"
    let some address ← whnfUntil index.getAppArgs[0]! ``controlsBase | throwError "expected the actual control pointer"
    let layout := layouts.getAppArgs
    let ram := read.getAppArgs
    let coords := address.getAppArgs
    return mkAppN (←mkConstWithLevelParams ``controlsAtPhysicalAddresses)
      #[ram[1]!, layout[1]!, layout[2]!, same, ram[2]!, coords[0]!, coords[3]!, coords[4]!, words]


end RoutingISA.FragmentRows.SparseGeometry

end BorderVNP
end Computability
end OAI
