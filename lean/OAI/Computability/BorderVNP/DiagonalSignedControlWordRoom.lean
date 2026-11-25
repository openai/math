import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenRoom
import OAI.Computability.BorderVNP.RoutingISAFragmentControlRoom
import OAI.Computability.BorderVNP.DiagonalTallyControlWordRoom

/-! # Word bounds for all controls of the installed signed task -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace RoutingISA.SignedTaskArena

open DiagonalTallyAllocation

/-- The two starts and the two strides printed by the typed task builder fit
in the area below the post-task buffers whenever a receiving cell exists. -/
private theorem taskWindowBounds (t : Layout) (cells : 0 < t.cube.cells) :
    let a := t.tasks 0 0 0 0
    a.scratch ≤ t.after.start ∧ a.bursts ≤ t.after.start ∧
      a.scratchStride ≤ t.after.start ∧ a.burstStride ≤ t.after.start := by
  have scratch := Nat.le_mul_of_pos_right t.p.scratchStride cells
  have burst := Nat.le_mul_of_pos_right t.p.burstStride cells
  dsimp only [Layout.tasks,TypedTaskBuilder.Layout.windows,Layout.after,TypedTaskBuilder.Layout.windowsEnd]
  omega

/-- The physical end of the residue reader covers even unused post-task buffers. -/
private theorem postRoom (t : Layout) (w u v k : ℕ) : t.after.localBase ≤ t.endAddress w u v k := by
  dsimp only [Layout.endAddress,Layout.entry,DiagonalResidueRAM.gateBase,Layout.valuation,Layout.tallyBits]
  omega

/-- The cell bank and its actual per-cell stride both lie below the reserved
report and typed-task regions. -/
private theorem bankBounds (t : Layout) (cells : 0 < t.cube.cells) :
    t.cube.cellBank ≤ t.before.start ∧ t.cube.cellStride ≤ t.before.start := by
  have stop : t.cube.stop ≤ CubeConstants.arenaEnd t.cube.stop t.id := by
    unfold CubeConstants.arenaEnd CubeConstants.idBase
    omega
  have hi := stop.trans t.constants_le_before
  change t.cube.cellBank+t.cube.cells*t.cube.cellStride ≤ t.before.start at hi
  have h := Nat.le_mul_of_pos_left t.cube.cellStride cells
  omega

/-- All 37 published control words fit the physical machine word. Addresses of
the task, report and fragment banks, and the strides they reserve, are bounded
by the installed reader endpoint. Only the external sort and scanner scalars
require their own width bounds. -/
theorem Layout.controls_word_of_scalars (t : Layout) {w u v k : ℕ}
    (endFits : t.endAddress w u v k < 2^w) (cells : 0 < t.cube.cells)
    (reportCells : 0 < t.p.report.cells) (count : t.p.report.countWidth ≤ w)
    (sorted : t.p.sorted < 2^w) (padded : t.p.padded < 2^w) (stops : t.p.stops < 2^w)
    (payload : t.p.bundlePayload < 2^w) (inverse : t.p.bundleInverse < 2^w)
    (gap : t.p.privateGap < 2^w) (site : t.p.siteWidth < 2^w) (body : t.p.bodyCap < 2^w)
    (i : Fin 37) : t.controls i.val < 2^w := by
  have pre := (t.before_limit_le_endAddress w u v k).trans_lt endFits
  have post := (postRoom t w u v k).trans_lt endFits
  have preStart : t.before.start < 2^w := by
    rw [t.before.footprint] at pre
    omega
  have postStart : t.after.start < 2^w := by
    rw [AfterTasks.localBase,t.after.footprint] at post
    omega
  obtain ⟨scratch,bursts,scratchStride,burstStride⟩ := taskWindowBounds t cells
  obtain ⟨bank,stride⟩ := bankBounds t cells
  unfold Layout.controls
  apply t.fragments.controls_fit _ preStart cells _ i.val i.isLt
  apply t.after.controls_fit reportCells count site body post
  apply t.before.controls_fit t.after rfl reportCells pre post
  intro j _
  split
  all_goals first
    | assumption
    | exact scratch.trans_lt postStart
    | exact bursts.trans_lt postStart
    | exact scratchStride.trans_lt postStart
    | exact burstStride.trans_lt postStart
    | exact bank.trans_lt preStart
    | exact stride.trans_lt preStart
    | exact Nat.two_pow_pos w

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
