import OAI.Computability.BorderVNP.RoutingISACubeArena
import OAI.Computability.BorderVNP.TransmissionRouteFactory

/-! # Reading the original cube tables after emitting and routing physical rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM Transmission Evaluator

/-- The actual cube allocation places the shared views before the opaque
cell inputs. Both lie above every word of the live scheduler and its sources. -/
theorem Layout.bank_bounds (a : Layout) (frame count w : ℕ) (pins : Pins.Layout)
    (rows : count ≤ a.maxRows) (input : pins.processors*pins.stride ≤ a.pairBase)
    (sub : pins.ibase+pins.count ≤ a.pairBase) (fit : a.stop ≤ 2^w) :
    a.pairBase+a.pairStride*a.header.d^2 ≤ a.cellBank ∧
    a.cellBank+a.cells*a.cellStride ≤ 2^w ∧
    (a.table frame count).readExtent pins ≤ a.pairBase := by
  have table := TableLayout.reserve_extent (frame := frame) (records := a.records)
    (R := a.teams) rows
  refine ⟨?_,fit,?_⟩
  · unfold Layout.cellBank
    rw [Nat.mul_comm]
  · change max ((a.table frame count).ordinals+count)
      (max (pins.processors*pins.stride) (pins.ibase+pins.count)) ≤ a.pairBase
    exact max_le table (max_le input sub)

/-- Both true native row writers preserve every earlier word except the
single frame field where they publish the evolving transmission count. -/
theorem emitted_before_records {w : ℕ} (emit : DataWriter.Layout) (pub : Arg → Word w) (m : Memory w)
    {g : BorderVNP.Cube.SharedRows.Layout} {after : ℕ → ℕ}
    (shared : g.Emitted (readings (DataWriter.publish emit pub m)) after)
    (frame : g.frame=(pub 0).val) (records : g.records=emit.output) (x : ℕ)
    (lo : x < emit.output) (field : x ≠ (pub 0).val+13) : after x = readings m x := by
  rw [shared.outside x (frame ▸ field) (Or.inl (by unfold BorderVNP.Cube.SharedRows.Layout.address; omega))]
  exact congrArg Fin.val (show DataWriter.publish emit pub m x = m x by
    rw [DataWriter.publish,Function.update_of_ne field,Packing.Directory.ISA.putWords_outside _ _ _ _ (Or.inl lo)])

/-- Each actual selected transfer protects all words preceding the public
records, including in the shared-first physical allocation. -/
theorem routeRanges_before_records {w : ℕ} {tab : TableLayout} {pub : Arg → Word w} {mt : Memory w}
    (ordered : tab.Ordered) (ranges : RouteRanges tab pub mt) {x i : ℕ} (hx : x < tab.records)
    (hi : i < tab.count) : (tableRange tab mt i).protectsCell (directoryFrame pub mt 0) x := by
  intro mode hs reg hd
  obtain ⟨lo,fit⟩ := ranges.destinations i hi mode hs reg hd
  obtain ⟨_,rec,ws,off,use⟩ := ordered
  exact ⟨fit,Or.inl (by omega)⟩

/-- Preservation for an arbitrary real return of the four-stage native
program. The scheduler image and the sequence of writes are obtained
from the return itself. -/
theorem route_before_records {w : ℕ} (tab : TableLayout) (row : ℕ → TableRow) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (before : Memory w)
    (al : tab.Allocated w) (ordered : tab.Ordered) (rowFit : tab.RowsFit w row)
    (base : (pub 0).val=tab.frame) (fields : tab.frameFields (readings before))
    (records : tab.recordsMatch row (readings before)) (f : BroadcastFrame)
    (im : f.At (readings pub) (readings before)) (fit : f.Fits w (pub 0).val)
    (teams : f.teams=tab.teams) (cap : ∀ u v, f.header+
      Routing.legLoad al.teamCount (tab.widthMatrix row) u v+
      Routing.legLoad al.teamCount (tab.widthMatrix row) v u ≤ f.capacity)
    (safe : ∀ mt, tab.Image row (readings before) (readings mt) → RouteRanges tab pub mt)
    (z : Returns route pub mac s before) {x : ℕ} (hx : x < tab.records) :
    z.val.2.2 x = before x := by
  obtain ⟨h,hpub,_,rows,count,image,_,final,_⟩ := route_history_of_return tab row pub mac s before
    al ordered rowFit base fields records f im fit teams cap safe z
  have written := safe h.initial image
  rw [← final,h.output]
  apply (tableMemory_protected h.rows h.team h.pub h.initial _ h.count x ?_).trans
    (Fin.ext (image.before_records ordered hx))
  intro i hi
  rw [rows]
  change (tableRange tab h.initial i).protectsCell (directoryFrame h.pub h.initial 0) x
  rw [hpub]
  exact routeRanges_before_records ordered written hx (count ▸ hi)

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
