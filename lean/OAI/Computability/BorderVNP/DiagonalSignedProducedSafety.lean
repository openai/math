import OAI.Computability.BorderVNP.DiagonalSignedProducedSections

/-! # Disjoint signed task ranges on the native owner scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM Evaluator Evaluator.ScheduleClock CellPacket CellPacket.Supplement CellSparse
open CellSparse.Packet CellSparse.Packet.Source DiagonalTallyAllocation TypedTaskBuilder SparseExterior

variable {Site : Type} {w : ℕ} (a : Layout) (team frame offsets ctl live ports : ℕ)
    (raw : ℕ → ℕ) (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record)
    (m : Memory w) (cells : ℕ → SparseExterior.Owned)

set_option quotPrecheck false
local notation "R" => a.controlRows team frame offsets ctl live ports
local notation "num" => (R).before raw (R).cells
local notation "src" => Batch.produced R raw p geom extra
local notation "sl" => batchLayout a frame ctl num
local notation "cell" => fun i => cells (globalCell (R).toLayout raw i)
local notation "task" => fun i => ((cell) i).typed sl (src i).typed

/-- The true seven-word task row, the occupied source intervals and two real
allocator strides supply all three memory-disjointness premises of the signed
argument serializer. Rows may be empty and the same cell's two private
bursts retain their original source addresses. -/
theorem Layout.produced_sparse_safety (place : a.SparsePlacement frame ctl) (room : (R).toLayout.Room raw w)
    (image : readings m=(R).toLayout.published raw)
    (span : ∀ c < (R).cells, raw ((R).sorted+(R).padded+((R).stops+c))-raw ((R).sorted+(R).padded+c)-1=
      3*((p c).parts.length+3))
    (rank : ∀ c c' : Fin (R).cells, c<c' → raw ((R).sorted+(R).padded+((R).stops+c.val)) <
      raw ((R).sorted+(R).padded+c'.val))
    (sections : MergeSections R p geom extra)
    (rows : ∀ i < num, MergeFields (src i) (R).tasks (R).four i m)
    (bounds : ∀ i < num, a.CellSections (src i))
    (globals : ∀ c < (R).cells, (R).owner raw c=(R).team → (cells c).global=c)
    (bytes : ∀ c < (R).cells, (R).owner raw c=(R).team → (cells c).field.bytes.length ≤ a.fragments.stride)
    (fits : ∀ i < num, ((task) i).cell.payload.length≤a.p.scratchStride ∧ (((task) i).cell.burst w).length≤a.p.burstStride) :
    MergeRanges src num (R).tasks (R).four ∧
    (∀ i < num, ∀ addr, TypedSources (src i).typed addr → inputRegion a num addr) ∧
    (R).toLayout.Arenas raw w task := by
  have arena := MergeArena.of_signed_layout R a team frame offsets ctl rfl place.cells place.sortedBank rfl rfl rfl rfl rfl
  have merge := MergeRanges.of_sections R raw p geom extra arena sections room span rank (fun i hi => (rows i hi).prefixEnd)
  have global (i : ℕ) (hi : i < num) : ((cell) i).global<a.fragments.cells := by
    have hc := (global_spec (R).toLayout raw hi).1
    exact (globals _ hc (global_spec (R).toLayout raw hi).2.1) ▸ hc
  have lengths (i : ℕ) (hi : i < num) := bytes _ (global_spec (R).toLayout raw hi).1 (global_spec (R).toLayout raw hi).2.1
  have rectangles := a.compressed_arenas team frame offsets ctl num w raw cell src m room image rfl
    (fun i hi => (rows i hi).task) global lengths
    (fun i hi => (bounds i hi).ranges.1) (fun i hi => (bounds i hi).ranges.2) fits
  refine ⟨merge,?_,rectangles.1⟩
  intro i hi addr touched
  let b := bounds i hi
  exact supplemental_inputRegion a num (src i) b.prefixEnd b.descriptors b.inputs b.geometry b.merged b.supplement touched

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
