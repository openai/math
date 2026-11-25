import OAI.Computability.BorderVNP.FiniteEvaluatorSparseCellSections
import OAI.Computability.BorderVNP.RoutingISAScheduleClockProducedInput

/-! # Source intervals of the actual signed sparse tasks

The public packet supplies the geometry beneath the sorted marker bank. Each
opaque chunk instead uses its receiving site's bounded slot. After the two
sources are concatenated, only the per-cell supplement and its merged count
address the later report allocation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM Evaluator Evaluator.ScheduleClock CellPacket CellPacket.Supplement CellSparse
open CellSparse.Packet CellSparse.Packet.Source DiagonalTallyAllocation TypedTaskBuilder
open private chunk_intervals from OAI.Computability.BorderVNP.RoutingISAScheduleClockMergeRangesGeometry

variable {Site : Type} {w : ℕ} (a : Layout) (team frame offsets ctl live ports : ℕ)
    (raw : ℕ → ℕ) (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record)

set_option quotPrecheck false
local notation "R" => a.controlRows team frame offsets ctl live ports
local notation "src" => Batch.produced R raw p geom extra
local notation "num" => (R).before raw (R).cells

/-- In native owner order every row of the genuine descriptor prefix and all
supplemental/merged operands lie in the sparse writer's protected source regions.
Only opaque slots that occur in a particular cell's packet require a bound. -/
theorem Layout.produced_signed_sections (place : a.SparsePlacement frame ctl)
    (room : (R).toLayout.Room raw w)
    (span : ∀ c < (R).cells, raw ((R).sorted+(R).padded+((R).stops+c))-raw ((R).sorted+(R).padded+c)-1 =
      3*((p c).parts.length+3))
    (publicEnd : ∀ c < (R).cells, (p c).publicBase+((p c).parts.flatMap Part.publicBuffer).length ≤ (R).sorted)
    (geometry : ∀ c < (R).cells, geom c=(p c).publicBase+((prefixParts (p c)).flatMap Part.publicBuffer).length)
    (slots : ∀ c < (R).cells, ∀ j, Sum.inr j ∈ (p c).boxes →
      (p c).slot j+(p c).headerWidth+(boxBody ((p c).factors j)).length ≤ a.fragments.external)
    (supp : ∀ c < (R).cells, ((extra c).flatMap record).length ≤ (R).stride)
    (ends : ∀ i < num, (src i).placed.descriptorBase+(descriptors (prefixChunks (src i).placed)).length=(src i).layout.tail)
    {i : ℕ} (hi : i < num) : a.CellSections (src i) := by
  let c := globalCell (R).toLayout raw i
  have hc : c < (R).cells := (global_spec (R).toLayout raw hi).1
  have order := a.sparse_order place.cells
  have stop : a.fragments.start ≤ a.fragments.external := by
    dsimp only [FragmentArena.Layout.external,FragmentArena.Layout.cursors,FragmentArena.Layout.triples,
      FragmentArena.Layout.pairs,FragmentArena.Layout.quads]
    omega
  have sorted : (R).sorted+(R).padded ≤ a.fragments.external :=
    place.sortedBank.trans (order.1.trans (order.2.1.trans stop))
  have positions := produced_addresses R raw p geom extra room hi span
  have whole : (p c).parts=prefixParts (p c)++[.publicWords (fieldList record (p c).rows++fieldList vector (p c).reports)] := rfl
  have atEnd := publicEnd c hc
  rw [whole,List.flatMap_append,List.flatMap_singleton] at atEnd
  simp only [Part.publicBuffer,List.length_append] at atEnd
  have old := chunk_intervals (p c).slot (p c).headerWidth (p c).factors (prefixParts (p c)) (p c).publicBase
    (R).sorted 0 a.fragments.external (by omega) (by
      intro j member
      have inside : Sum.inr j ∈ (p c).boxes := by
        obtain h | h := List.mem_cons.mp member
        · contradiction
        · obtain ⟨b,hb,eq⟩ := List.mem_map.mp h
          cases b with
          | inl fs => contradiction
          | inr k => cases eq; exact hb
      exact ⟨Nat.zero_le _,slots c hc j inside⟩)
  have lower : a.fragments.limit ≤ a.before.supplement := Nat.le_add_right ..
  have total := Nat.mul_le_mul_right a.before.bound.supplementStride (Nat.succ_le_of_lt (hc.trans_le place.cells))
  rw [Nat.succ_mul] at total
  change c*a.before.bound.supplementStride+a.before.bound.supplementStride ≤ a.before.bound.cells*a.before.bound.supplementStride at total
  have tail : a.before.supplement+a.before.bound.cells*a.before.bound.supplementStride ≤ a.before.limit := by
    change a.before.counters ≤ a.before.limit
    simp only [BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.six,BeforeTasks.four,BeforeTasks.merged]
    omega
  have upper := supp c hc
  change ((extra c).flatMap record).length ≤ a.before.bound.supplementStride at upper
  refine ⟨ends i hi,positions.2.2.1.le.trans sorted,?_,?_,?_,?_⟩
  · intro chunk member
    rcases old chunk member with lo | ⟨_,h⟩
    · exact lo.trans ((Nat.le_add_right ..).trans sorted)
    · exact h
  · change geom c+1+((p c).rows.flatMap record).length+(fieldList vector (p c).reports).length ≤ a.fragments.external
    rw [geometry c hc]
    simp only [fieldList,List.length_cons] at atEnd ⊢
    omega
  · change a.fragments.limit ≤ a.before.merged+c ∧ a.before.merged+c+1 ≤ a.before.limit
    have bound : c+1 ≤ a.cube.cells := hc
    have merged := order.2.2.1
    have later := order.2.2.2.1
    have last := order.2.2.2.2.1
    omega
  · change a.fragments.limit ≤ a.before.supplement+a.before.bound.supplementStride*c ∧
      a.before.supplement+a.before.bound.supplementStride*c+((extra c).flatMap record).length ≤ a.before.limit
    rw [Nat.mul_comm a.before.bound.supplementStride c]
    omega

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
