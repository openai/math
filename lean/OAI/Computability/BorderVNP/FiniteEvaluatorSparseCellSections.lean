import OAI.Computability.BorderVNP.FiniteEvaluatorSparseCellWindows
import OAI.Computability.BorderVNP.RoutingISAScheduleClockMergeRangesGeometry

/-! # Original finite cell sections in the signed sparse arena

The genuine geometric prefix, private box chunks, patched geometry suffix
and merged count occupy their published ranges. Their endpoints protect
the metadata and supply the input bounds of the sparse finite dispatcher.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM Evaluator CellSparse CellSparse.Packet CellPacket CellPacket.Supplement
open DiagonalTallyAllocation FiniteEvaluator SparseExterior TypedTaskBuilder

variable {Site : Type} (a : Layout)

/-- Bounds on the actual original chunk stream and patched geometric suffix.
These are read from their published locations in the signed sparse arena. -/
structure Layout.CellSections (o : Batch.Owned Site) : Prop where
  prefixEnd : o.placed.descriptorBase+(descriptors (prefixChunks o.placed)).length=o.layout.tail
  descriptors : o.layout.tail+12≤a.fragments.external
  inputs : ∀ c ∈ prefixChunks o.placed, c.endSource≤a.fragments.external
  geometry : o.geometry+1+(o.placed.rows.flatMap record).length+(fieldList vector o.placed.reports).length≤a.fragments.external
  merged : a.fragments.limit≤o.layout.merged ∧ o.layout.merged+1≤a.before.limit
  supplement : a.fragments.limit≤o.layout.supplement ∧ o.layout.supplement+(o.extra.flatMap record).length≤a.before.limit

/-- All patched descriptor, original-box, geometry and count sources end below
the typed task windows, including empty records. -/
theorem Layout.CellSections.ranges {o : Batch.Owned Site} (sections : a.CellSections o) :
    o.typed.cell.descriptorBase+3*o.typed.cell.chunks.length≤a.before.limit ∧
      ∀ c ∈ o.typed.cell.chunks, c.endSource≤a.before.limit := by
  have low : a.fragments.external≤a.before.limit := by
    rw [a.before.footprint]
    have start : a.before.start=a.fragments.limit := rfl
    have room : a.fragments.external≤a.fragments.limit := by dsimp only [FragmentArena.Layout.limit,FragmentArena.Layout.counts]; omega
    omega
  have prefixEnd := sections.prefixEnd
  rw [descriptors_length] at prefixEnd
  constructor
  · change o.placed.descriptorBase+3*(prefixChunks o.placed++tailChunks o.layout o.placed o.geometry o.extra).length≤_
    rw [List.length_append,show (tailChunks o.layout o.placed o.geometry o.extra).length=4 from rfl,Nat.mul_add,←Nat.add_assoc,prefixEnd]
    exact sections.descriptors.trans low
  · intro c hc
    change c ∈ prefixChunks o.placed++tailChunks o.layout o.placed o.geometry o.extra at hc
    rcases List.mem_append.mp hc with before|after
    · exact (sections.inputs c before).trans low
    · simp only [tailChunks,List.mem_cons,List.not_mem_nil,or_false] at after
      have geom := sections.geometry.trans low
      have merged := sections.merged.2
      have supplement := sections.supplement.2
      rcases after with rfl|rfl|rfl|rfl <;> simp only [Chunk.endSource,List.length_cons,List.length_nil] <;> omega

variable {w : ℕ} (team frame offsets ctl live ports : ℕ) (raw : ℕ → ℕ)
variable (placed : ℕ → Placed Site) (geometry : ℕ → ℕ) (extra : ℕ → List Record)
local notation "R" => a.controlRows team frame offsets ctl live ports
local notation "src" => Batch.produced R raw placed geometry extra
local notation "taskCount" => TypedTaskBuilder.Layout.before (CellControlRows.Layout.toLayout R) raw (TypedTaskBuilder.Layout.cells (CellControlRows.Layout.toLayout R))

/-- All primary words, eight task controls, per-cell report tails and global
call owners are disjoint from the real merged counts and twelve patched
descriptor words of every owned cell. -/
theorem Layout.produced_meta (place : a.SparsePlacement frame ctl)
    (room : (R).toLayout.Room raw w)
    (span : ∀ c < (R).cells, raw ((R).sorted+(R).padded+((R).stops+c))-raw ((R).sorted+(R).padded+c)-1=
      3*((placed c).parts.length+3)) : Reports.MetaOutside (R).toLayout taskCount src := by
  have order := a.sparse_order place.cells
  have frag : a.fragments.start≤a.fragments.limit := by rw [a.fragments.footprint]; omega
  have bank : a.cube.cellBank≤a.before.merged := order.1.trans (order.2.1.trans (frag.trans order.2.2.1))
  have tails : a.before.tailWidths+a.cube.cells≤a.before.merged := by
    have cells := place.cells
    dsimp only [BeforeTasks.merged,BeforeTasks.counters,BeforeTasks.supplement]
    change a.before.tailWidths+a.cube.cells≤a.before.tailWidths+a.p.report.cells+_+_
    omega
  have low : a.cube.cellBank≤a.before.tailWidths := order.1.trans (order.2.1.trans frag)
  have limit : a.before.merged+a.cube.cells≤a.before.limit :=
    order.2.2.2.1.trans ((Nat.le_add_right ..).trans order.2.2.2.2.1)
  intro i hi
  obtain ⟨merged,_,endAt,beginAt⟩ := produced_addresses R raw placed geometry extra room hi span
  have gc : globalCell (R).toLayout raw i<a.cube.cells := (global_spec (R).toLayout raw hi).1
  change (src i).layout.merged=a.before.merged+globalCell (R).toLayout raw i at merged
  change (src i).layout.tail+12<a.p.sorted+a.p.padded at endAt
  change a.p.sorted≤(src i).layout.tail at beginAt
  have before := place.beforeBank
  have primary := place.primary
  have ctlStart := place.beforeControl
  have sorted := place.sortedBank
  have away (z : ℕ) (sort : z<a.p.sorted ∨ a.p.sorted+a.p.padded≤z)
      (mrg : z<a.before.merged ∨ a.before.merged+a.cube.cells≤z) : (src i).cell.Outside z := by
    change z≠(src i).layout.merged ∧ (z<(src i).layout.tail ∨ (src i).layout.tail+12≤z)
    omega
  refine ⟨fun j hj => away (frame+j) (.inl (by omega)) (.inl (by omega)),?_,?_⟩
  · intro j hj
    have sep := place.controller
    exact away (ctl+j) (by omega) (.inl (by omega))
  · intro c hc
    change c<a.cube.cells at hc
    exact ⟨away (a.before.tailWidths+c) (.inr (by omega)) (.inl (by omega)),
      away (a.before.limit+3*c) (.inr (by omega)) (.inr (by omega))⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
