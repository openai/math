import OAI.Computability.BorderVNP.RoutingISAFragmentArena
import OAI.Computability.BorderVNP.RoutingISATypedTaskWindows
import OAI.Computability.BorderVNP.DiagonalTallyAlign
import OAI.Computability.BorderVNP.PackedRoutingControls

/-! # Length-only scalar choices for the owned cells and the residue-entry query

The three-word call directory, compact seven-word tasks, scratch and burst
windows lie above all original routed inputs. The materialized cell and cube
reports lie above those windows. The Fourier query uses the one length-only
address reached by the aligned tally computation on every accepted history.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally DiagonalTallyAllocation

/-- Remaining public geometry, finite report and compiled task dimensions. -/
structure Parameters where
  /-- Length-only upper bounds on report sites, bits, vertices and supplemental words. -/
  report : Bounds
  /-- Absolute sorted primary descriptor word base, reconstructed from the geometry. -/
  sorted : ℕ
  /-- Width of the primary descriptor sort. -/
  padded : ℕ
  /-- First stop marker of the primary descriptor sort. -/
  stops : ℕ
  /-- Absolute result bank of the marked bundle sort. -/
  bundlePayload : ℕ
  /-- Absolute inverse-rank bank of the marked bundle sort. -/
  bundleInverse : ℕ
  /-- Reserved use and count bits between supplied data and opaque originals. -/
  privateGap : ℕ
  /-- Scratch words reserved for each potential cell. -/
  scratchStride : ℕ
  /-- Burst words reserved for each potential cell. -/
  burstStride : ℕ
  /-- Width of each original-site scalar field. -/
  siteWidth : ℕ
  /-- Length-only upper bound on the opaque body of an original box. -/
  bodyCap : ℕ
  /-- Number of curve parameters preceding the gadget-count coordinates. -/
  parameters : ℕ

/-- The physical placement combines the cube, fixed signed table and sparse report bounds. -/
structure Layout where
  /-- Cube, shared routing and host-input allocation. -/
  cube : CubeArena.Layout
  /-- Position IDs in the fixed cube identity. -/
  id : TableEntry cube.n cube.b cube.h cube.K cube.s → ℕ
  /-- Report and geometry scalar dimensions. -/
  p : Parameters

/-- Reserve genuine cable and free-literal fragments, their stable bucket
and the compact external payloads below all typed windows. -/
noncomputable def Layout.fragments (l : Layout) : FragmentArena.Layout :=
  ⟨CubeConstants.arenaEnd l.cube.stop l.id,l.cube.cables,l.cube.maxRows,l.cube.cells,l.p.scratchStride⟩

/-- Before the owned-cell scan, allocate its true counters, supplemental outputs,
six- and four-word rows and original bundle ordinal tables. -/
noncomputable def Layout.before (l : Layout) : BeforeTasks :=
  ⟨l.fragments.limit,l.p.report⟩

/-- The sparse fragment and report ranges lie above all fixed cube operands. -/
theorem Layout.constants_le_before (l : Layout) : CubeConstants.arenaEnd l.cube.stop l.id ≤ l.before.start := by
  change l.fragments.start ≤ l.fragments.limit
  rw [l.fragments.footprint]
  omega

/-- Windows matching the native seven-word task producer. -/
noncomputable def Layout.tasks (l : Layout) (team frame offsets control : ℕ) : TypedTaskBuilder.Layout :=
  let empty : TypedTaskBuilder.Layout := {
    frame := frame, team := team, cells := l.cube.cells, cables := l.cube.cables,
    calls := 0, banks := l.cube.hostDirectory, offsets := offsets, tasks := 0, control := control,
    sorted := l.p.sorted, padded := l.p.padded, stops := l.p.stops, scratch := 0, bursts := 0,
    scratchStride := 0, burstStride := 0, tails := l.before.tailWidths }
  empty.windows l.before.limit l.p.scratchStride l.p.burstStride

/-- Runtime operand buffers start after every task scratch and burst interval. -/
noncomputable def Layout.after (l : Layout) : AfterTasks :=
  let t := l.tasks 0 0 0 0
  ⟨t.windowsEnd l.before.limit l.p.scratchStride l.p.burstStride,l.p.report⟩

/-- The exact 37 natural values emitted as constant geometry output columns. -/
noncomputable def Layout.controls (l : Layout) : ℕ → ℕ :=
  let t := l.tasks 0 0 0 0
  let core : ℕ → ℕ
    | 0 => l.p.sorted | 1 => l.p.padded | 2 => l.p.stops
    | 3 => t.scratch | 4 => t.bursts | 5 => t.scratchStride | 6 => t.burstStride
    | 8 => l.p.privateGap | 9 => l.cube.cellBank | 10 => l.cube.cellStride
    | 20 => l.p.bundlePayload | 21 => l.p.bundleInverse | _ => 0
  l.fragments.controls (l.after.controls l.p.siteWidth l.p.bodyCap (l.before.controls core))

/-- Coordinate dimension of the signed residue matrix query. -/
def Layout.dim (l : Layout) := l.p.parameters+l.p.report.gadgets

/-- This absolute source is encoded once in the supplied entry-reader circuit
and is valid for every realized operand count and cube selector choice. -/
noncomputable def Layout.tallyBits (l : Layout) :=
  l.after.localBase+l.dim+l.cube.teams*l.dim+l.dim+l.dim+1

/-- The source encoded in the literal packet equals the true native serializer’s
output, even though the realized number of report and cube records can vary. -/
theorem Layout.tallyBits_actual (l : Layout) {e : ℕ} (fit : e ≤ l.p.report.operands)
    (raw team width w : ℕ) :
    ((l.after.arenaFor e raw l.dim l.cube.teams team width).bitFrame w).dst=l.tallyBits :=
  (l.after.fixed_outputs fit raw l.dim l.cube.teams team width w).2.2.2

/-- Initial tally fields. The operand and vertex counts are subsequently set
by the native cell, cube and sparse suffix scans. -/
noncomputable def Layout.reportFields (l : Layout) (raw team subtotalWidth : ℕ) (old : ℕ → ℕ) : ℕ → ℕ :=
  let t := l.tasks 0 0 0 0
  let base : ℕ → ℕ
    | 33 => l.dim | 35 => 0 | 36 => raw | 38 => l.cube.teams | 39 => team | 40 => subtotalWidth
    | 46 => 0 | 89 => t.tasks | 90 => 0 | 95 => l.p.parameters | i => old i
  l.after.frameFields base

/-- True extended literal words for all lookup, receiving-cell, and tally
scalars, preserving the independently placed geometry and static cube header. -/
noncomputable def Layout.extension {w : ℕ} (l : Layout) (raw team subtotalWidth : ℕ)
    (old : Fin 81 → Word w) (j : Fin 81) : Word w :=
  let cube := l.cube.extension old
  let previous : ℕ → ℕ := fun k ↦ (cube ⟨min (k-31) 80,by omega⟩).val
  TeamTapeInputEmit.word w (l.reportFields raw team subtotalWidth previous (31+j.val))

/-- Ordinary operand entries 15 and 16 designate the true call and count
words while the existing contiguous routing-address operands are supplied
from the same cube arena. -/
noncomputable def Layout.bootOperand (l : Layout) (frame : ℕ) : ℕ → Option ℕ
  | 15 => some l.before.limit
  | 16 => some l.cube.cells
  | i => l.cube.bootOperand frame i

/-- Physical consumer directories agree on the bank, stride and supplemental
locations. These equalities also pin the two marked bundle-sort result bases. -/
theorem Layout.consumer_words (l : Layout) :
    l.controls 7=l.before.tailWidths ∧ l.controls 8=l.p.privateGap ∧
    l.controls 9=l.cube.cellBank ∧ l.controls 10=l.cube.cellStride ∧
    l.controls 17=l.before.six ∧ l.controls 18=l.before.ranges ∧ l.controls 19=l.before.bundleTable ∧
    l.controls 20=l.p.bundlePayload ∧ l.controls 21=l.p.bundleInverse ∧
    l.controls 25=l.after.packed ∧ l.controls 26=l.after.refs :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
