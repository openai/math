import OAI.Computability.BorderVNP.RoutingISAScheduleClockProducedHeader

/-! # The private preparation source of the native owned-row producer

Each compact row indexes the original host cell chosen by the native owner
scan. The real report and sidecar sections give the supplemental input,
the occupied span and tail arrays give the encoder input, and the actual
fixed arenas give the later typed and call allocations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellDispatch CompactMachine CellSparse CellPacket TypedTaskBuilder
open CellPacket.Supplement.Batch

variable {w n : ℕ} {Site : Type} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (a : SignedTaskArena.Layout) (l : CellControlRows.Layout) (raw : ℕ → ℕ)
    (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record) (cells : ℕ → SparseExterior.Owned)

set_option quotPrecheck false
local notation "count" => l.before raw l.cells
local notation "src" => produced l raw p geom extra
local notation "merge" => (fun i => (src i).cell)
local notation "patched" => written m merge count
local notation "old" => (fun i => (src i).typed)
local notation "os" => (fun i => cells (globalCell l.toLayout raw i))
local notation "sl" => SparseExterior.batchLayout a l.frame l.control count
local notation "tasks" => (fun i => (os i).typed sl (old i))

/-- Register the actual native builder output on the owning team as the source for the three
argument passes. The packed extent and word inequalities concern real arrays
and live intervals. The sparse memory itself is obtained by execution. -/
noncomputable def SparseCallInput.ofOwned (fp : (pub 0).val=l.frame) (fields : l.toLayout.Fields raw)
    (room : l.toLayout.Room raw w) (image : readings m=l.toLayout.published raw)
    (word : raw (l.frame+30)=w) (header : l.control+36<2^w) (fourRoom : l.four+4*l.cells≤2^w)
    (table : l.tasks=(a.tasks 0 0 0 0).tasks) (four : l.four=a.before.four)
    (callBase : l.calls=a.before.limit) (cellCount : l.cells=a.cube.cells) (reportCount : l.cells≤a.p.report.cells)
    (controller : ∀ k ∈ [11,17,31,32,34,35,36], raw (l.control+k)=a.controls k)
    (span : ∀ c < l.cells, raw (l.sorted+l.padded+(l.stops+c))-raw (l.sorted+l.padded+c)-1=3*((p c).parts.length+3))
    (frameLow : l.frame+112≤l.sorted ∧ l.frame+112≤l.merged)
    (callsHigh : l.sorted+l.padded≤l.calls ∧ l.merged+l.cells≤l.calls)
    (controlLo : l.frame+112≤l.control) (controlHi : l.control+37≤l.calls ∧ l.control+37≤l.tasks)
    (ctrlSorted : l.control+37≤l.sorted ∨ l.sorted+l.padded≤l.control)
    (ctrlMerged : l.control+37≤l.merged ∨ l.merged+l.cells≤l.control)
    (early : l.frame+112≤a.fragments.external)
    (mergeFields : ∀ i < count, MergeFields (src i) l.tasks l.four i m)
    (ranges : MergeRanges src count l.tasks l.four)
    (global : ∀ c < l.cells, l.owner raw c=l.team → (cells c).global=c)
    (extent : ∀ c < l.cells, l.owner raw c=l.team → (cells c).field.bytes.length ≤ a.fragments.stride)
    (spans : ∀ c < l.cells, l.owner raw c=l.team → (cells c).first+(cells c).field.spans.length≤a.fragments.capacity)
    (tails : ∀ c < l.cells, l.owner raw c=l.team → (cells c).dense+(cells c).field.width+(cells c).field.tail.length≤a.fragments.start)
    (inputs : ∀ c < l.cells, l.owner raw c=l.team → ∀ r ∈ (cells c).field.spans, r.source+r.bits.length≤a.fragments.start)
    (intervals : ∀ i < count, (os i).Initial sl i patched)
    (chunkRegion : ∀ i < count, ∀ x, SparseExterior.TypedSources (old i) x → SparseExterior.inputRegion a count x)
    (arenas : l.toLayout.Arenas raw w tasks)
    (cap : ∀ i < count, ((tasks i).cell.burst w).length≤TeamScales.width n (1/2)) : SparseCallInput pub m := by
  have loaded := produced_headers l raw p geom extra m room span a fields image word table four controller frameLow
    controlLo controlHi ctrlSorted ctrlMerged
  have ptr := loaded.1
  have base := loaded.2.1
  have len := loaded.2.2.1
  have control := loaded.2.2.2.1
  have load := loaded.2.2.2.2.1
  have width := loaded.2.2.2.2.2
  have tableEq : (sl).tasks=l.tasks := table.symm
  have countFit : count≤l.cells := l.before_le raw l.cells
  have bounds := room.frame
  change l.frame+112 < 2^w at bounds
  have tbl := room.tasks
  change l.tasks+7*l.cells < 2^w at tbl
  have taskRoom : (sl).tasks+7*(sl).count ≤ 2^w := by change _+7*count≤_; rw [tableEq]; omega
  have selected (i : ℕ) (hi : i<count) : globalCell l.toLayout raw i<l.cells := (global_spec l.toLayout raw hi).1
  have mine (i : ℕ) (hi : i<count) : l.owner raw (globalCell l.toLayout raw i)=l.team := (global_spec l.toLayout raw hi).2.1
  have numbers (i : ℕ) (hi : i<count) : (os i).global=globalCell l.toLayout raw i := global _ (selected i hi) (mine i hi)
  have ids (i : ℕ) (hi : i<count) : (os i).global<a.fragments.cells := by
    rw [numbers i hi]; change _<a.cube.cells; exact cellCount ▸ selected i hi
  have lengths (i : ℕ) (hi : i<count) := extent _ (selected i hi) (mine i hi)
  have independent := SparseExterior.batch_independent a l.frame l.control count os (countFit.trans reportCount) ids
    (fun i hi => spans _ (selected i hi) (mine i hi)) lengths (fun i hi => tails _ (selected i hi) (mine i hi)) (fun i hi => inputs _ (selected i hi) (mine i hi))
  have distinct : Function.Injective (fun i : Fin count => (os i.val).global) := by
    apply StrictMono.injective
    intro i j lt
    change (os i.val).global<(os j.val).global
    rw [numbers _ i.isLt,numbers _ j.isLt]
    exact global_strict l.toLayout raw lt j.isLt
  have protect := SparseExterior.protected_from_arena a l.frame l.control count os old ids lengths distinct chunkRegion
  have roster := ownerTable_supplemented l raw p geom extra fp fields room image span
    (show l.frame+16≤l.sorted ∧ l.frame+16≤l.merged by omega) callsHigh
  have callPtr : (Frame.ofMemory pub patched).base=a.before.limit := (congrArg Frame.base roster.frame).trans callBase
  have total : (Frame.ofMemory pub patched).count≤a.cube.cells := (congrArg Frame.count roster.frame).le.trans cellCount.le
  have held := SparseExterior.frame_owners_outside a l.frame l.control count os
    (Frame.ofMemory pub patched) ids lengths early callPtr total
  have frameKept := held.1
  have ownerKept := held.2
  have allocation := TypedTaskBuilder.allocated l.toLayout raw room arenas
  have fits (i : ℕ) (hi : i<count) : (tasks i).callRow+2<2^w ∧ (tasks i).cell.Room w := by
    have addr := (arenas.starts i hi).1
    have hc := selected i hi
    have high := room.calls
    change l.calls+3*l.cells<2^w at high
    exact ⟨by rw [addr]; change l.calls+3*(globalCell l.toLayout raw i)+2<_; omega,
      TypedTaskBuilder.task_room l.toLayout raw room arenas hi⟩
  have controls := TypedTaskBuilder.control l.toLayout raw room arenas fp roster.frame
  let logical := TypedTaskBuilder.augmentedInput l.toLayout raw p extra
  apply SparseCallInput.ofNative (n:=n) pub mac s m l.four merge sl os old (fun i => (logical i).directory)
    (fun i => (logical i).privateWires) (fun i => (cells i).field) fp (by change l.frame+92<_; omega)
    (by change readings m (l.frame+92)+11<_; rw [ptr]; omega) len base
    (by change readings m (readings m (l.frame+92)+11)=_; rw [ptr]; exact control) taskRoom
    (by change l.four+4*count≤_; omega)
  · rw [tableEq]; exact fun i hi => ⟨(mergeFields i hi).scalar,(mergeFields i hi).room⟩
  · rw [tableEq]; exact ranges.scanReads
  · exact header
  · exact load
  · exact intervals
  · exact independent
  · exact protect
  · exact width
  · rw [tableEq]; exact ranges.sources m mergeFields
  · intro i hi k hk
    have small : k<112 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
    exact frameKept i hi k small
  · exact ownerKept
  · rw [tableEq]; exact allocation
  · exact fits
  · exact controls
  · exact produced_ordinals pub patched l raw cells p geom extra roster
  · exact cap

/-- A full array of bounded sparse sources can also be used by the owned scan. -/
noncomputable def SparseCallInput.ofProduced (fp : (pub 0).val=l.frame) (fields : l.toLayout.Fields raw)
    (room : l.toLayout.Room raw w) (image : readings m=l.toLayout.published raw)
    (word : raw (l.frame+30)=w) (header : l.control+36<2^w) (fourRoom : l.four+4*l.cells≤2^w)
    (table : l.tasks=(a.tasks 0 0 0 0).tasks) (four : l.four=a.before.four)
    (callBase : l.calls=a.before.limit) (cellCount : l.cells=a.cube.cells) (reportCount : l.cells≤a.p.report.cells)
    (controller : ∀ k ∈ [11,17,31,32,34,35,36], raw (l.control+k)=a.controls k)
    (span : ∀ c < l.cells, raw (l.sorted+l.padded+(l.stops+c))-raw (l.sorted+l.padded+c)-1=3*((p c).parts.length+3))
    (frameLow : l.frame+112≤l.sorted ∧ l.frame+112≤l.merged)
    (callsHigh : l.sorted+l.padded≤l.calls ∧ l.merged+l.cells≤l.calls)
    (controlLo : l.frame+112≤l.control) (controlHi : l.control+37≤l.calls ∧ l.control+37≤l.tasks)
    (ctrlSorted : l.control+37≤l.sorted ∨ l.sorted+l.padded≤l.control)
    (ctrlMerged : l.control+37≤l.merged ∨ l.merged+l.cells≤l.control)
    (early : l.frame+112≤a.fragments.external)
    (mergeFields : ∀ i < count, MergeFields (src i) l.tasks l.four i m)
    (ranges : MergeRanges src count l.tasks l.four)
    (global : ∀ c < l.cells, (cells c).global=c)
    (extent : ∀ c < l.cells, (cells c).field.bytes.length ≤ a.fragments.stride)
    (spans : ∀ c < l.cells, (cells c).first+(cells c).field.spans.length≤a.fragments.capacity)
    (tails : ∀ c < l.cells, (cells c).dense+(cells c).field.width+(cells c).field.tail.length≤a.fragments.start)
    (inputs : ∀ c < l.cells, ∀ r ∈ (cells c).field.spans, r.source+r.bits.length≤a.fragments.start)
    (intervals : ∀ i < count, (os i).Initial sl i patched)
    (chunkRegion : ∀ i < count, ∀ x, SparseExterior.TypedSources (old i) x → SparseExterior.inputRegion a count x)
    (arenas : l.toLayout.Arenas raw w tasks)
    (cap : ∀ i < count, ((tasks i).cell.burst w).length≤TeamScales.width n (1/2)) : SparseCallInput pub m :=
  SparseCallInput.ofOwned pub mac s m a l raw p geom extra cells fp fields room image word header fourRoom table four
    callBase cellCount reportCount controller span frameLow callsHigh controlLo controlHi ctrlSorted ctrlMerged early
    mergeFields ranges (fun c hc _ => global c hc) (fun c hc _ => extent c hc) (fun c hc _ => spans c hc)
    (fun c hc _ => tails c hc) (fun c hc _ => inputs c hc) intervals chunkRegion arenas cap

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
