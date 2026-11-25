import OAI.Computability.BorderVNP.RoutingISAScheduleClockMergeSource
import OAI.Computability.BorderVNP.RoutingISAScheduleClockMergeRanks
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedTaskSource
import OAI.Computability.BorderVNP.DiagonalTallyAllocationRate

/-! # Source protection for the native supplemental patches

Each compact task rewrites the final four descriptor triples of its own sorted
section and one merged count indexed by its global cell. The earlier public
words, opaque private boxes, report output, and seven-word task table occupy
separate ranges of the signed allocation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellPacket CellSparse CellSparse.Packet CellPacket.Supplement CellPacket.Supplement.Batch
open DiagonalTallyAllocation TypedTaskBuilder

/-- The addresses reserved by the pre-task arena for the supplemental records,
counters and four-word rows used by the descriptor patcher. -/
structure MergeArena (l : CellControlRows.Layout) : Prop where
  sorted : l.sorted+l.padded ≤ l.supplemental
  supplement : l.supplemental+l.stride*l.cells ≤ l.counters
  counters : l.counters+2*l.cells ≤ l.merged
  four : l.merged+l.cells ≤ l.four
  tasks : l.merged+l.cells ≤ l.tasks

/-- The allocated pre-task partition supplies these bounds even when an
owned cell uses its entire supplemental stride. -/
theorem MergeArena.of_before (l : CellControlRows.Layout) (pre : BeforeTasks)
    (cells : l.cells≤pre.bound.cells) (supplement : l.supplemental=pre.supplement)
    (stride : l.stride=pre.bound.supplementStride) (counts : l.counters=pre.counters)
    (merged : l.merged=pre.merged) (four : l.four=pre.four)
    (sort : l.sorted+l.padded ≤ pre.start) (tasks : pre.limit ≤ l.tasks) : MergeArena l := by
  obtain ⟨_,sup,cnt,mrg,fourEnd,sixEnd,rangesEnd,bundlesEnd⟩ := pre.ordered
  have start : pre.start ≤ pre.supplement := by simp [BeforeTasks.supplement,BeforeTasks.tailWidths]
  have prod := Nat.mul_le_mul_right pre.bound.supplementStride cells
  constructor <;> simp only [supplement,stride,counts,merged,four,Nat.mul_comm pre.bound.supplementStride]
  · exact sort.trans start
  · omega
  · omega
  · omega
  · omega

variable {Site : Type} {w : ℕ} (l : CellControlRows.Layout) (raw : ℕ → ℕ) (p : ℕ → Placed Site)
    (geom : ℕ → ℕ) (extra : ℕ → List Record)

set_option quotPrecheck false

local notation "os" => produced l raw p geom extra
local notation "count" => l.before raw l.cells
local notation "global" => globalCell l.toLayout raw

/-- Per-cell geometry and original private boxes occupy the public word bank or
the private input banks between the sorted descriptors and the report output.
The supplemental list consumes at most its allocated per-cell stride. -/
structure MergeSections (l : CellControlRows.Layout) (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record) : Prop where
  chunks : ∀ c < l.cells, ∀ u ∈ prefixChunks (p c), u.endSource ≤ l.sorted ∨
    l.sorted+l.padded ≤ u.base ∧ u.endSource ≤ l.supplemental
  geometry : ∀ c < l.cells, geom c+1+((p c).rows.flatMap record).length+(fieldList vector (p c).reports).length ≤ l.sorted
  supplement : ∀ c < l.cells, ((extra c).flatMap record).length ≤ l.stride

/-- Native owner order, stable inverse marker ranks, and the actual arena
intervals protect every address read before and after a supplemental patch. -/
theorem MergeRanges.of_sections (arena : MergeArena l) (sections : MergeSections l p geom extra)
    (room : l.toLayout.Room raw w)
    (span : ∀ c < l.cells, raw (l.sorted+l.padded+(l.stops+c))-raw (l.sorted+l.padded+c)-1 = 3*((p c).parts.length+3))
    (rankOrder : ∀ c c' : Fin l.cells, c<c' →
      raw (l.sorted+l.padded+(l.stops+c.val)) < raw (l.sorted+l.padded+c'.val))
    (ends : ∀ i < count, (os i).placed.descriptorBase+(CellPacket.descriptors (prefixChunks (os i).placed)).length=(os i).layout.tail) :
    MergeRanges os count l.tasks l.four := by
  have bounds (i : ℕ) (hi : i<count) := SignedTaskArena.produced_addresses l raw p geom extra room hi span
  have valid (i : ℕ) (hi : i<count) : global i<l.cells := (global_spec l.toLayout raw hi).1
  have sortedMerge : l.sorted+l.padded ≤ l.merged :=
    arena.sorted.trans ((Nat.le_add_right l.supplemental _).trans (arena.supplement.trans
      ((Nat.le_add_right l.counters _).trans arena.counters)))
  have low (k : ℕ) (hk : k<count) (a : ℕ) (ha : a<l.sorted) : (os k).cell.Outside a := by
    obtain ⟨mrg,_,_,lo⟩ := bounds k hk
    change a≠(os k).layout.merged ∧ (a<(os k).layout.tail ∨ (os k).layout.tail+12≤a)
    omega
  have gap (k : ℕ) (hk : k<count) (a : ℕ) (lo : l.sorted+l.padded≤a) (hi : a<l.merged) : (os k).cell.Outside a := by
    obtain ⟨mrg,_,stop,_⟩ := bounds k hk
    change a≠(os k).layout.merged ∧ (a<(os k).layout.tail ∨ (os k).layout.tail+12≤a)
    omega
  have high (k : ℕ) (hk : k<count) (a : ℕ) (ha : l.merged+l.cells≤a) : (os k).cell.Outside a := by
    obtain ⟨mrg,_,stop,_⟩ := bounds k hk
    have ck := valid k hk
    change a≠(os k).layout.merged ∧ (a<(os k).layout.tail ∨ (os k).layout.tail+12≤a)
    omega
  have separate {i k : ℕ} (ik : i<k) (hk : k<count) : (os i).layout.tail+12 ≤ (os k).placed.descriptorBase := by
    have hi := ik.trans hk
    have order := rankOrder ⟨global i,valid i hi⟩ ⟨global k,valid k hk⟩ (global_strict l.toLayout raw ik hk)
    change raw (l.sorted+l.padded+(l.stops+global i)) < raw (l.sorted+l.padded+global k) at order
    rw [(bounds i hi).2.1]
    change l.sorted+raw (l.sorted+l.padded+(l.stops+global i)) ≤ l.sorted+raw (l.sorted+l.padded+global k)+1
    omega
  have chunk {i k : ℕ} (hi : i<count) (hk : k<count) (u : Chunk) (hu : u ∈ prefixChunks (os i).placed)
      {a : ℕ} (ha : u.base≤a) (hb : a<u.endSource) : (os k).cell.Outside a := by
    obtain left | ⟨right,cap⟩ := sections.chunks (global i) (valid i hi) u hu
    · exact low k hk a (hb.trans_le left)
    · exact gap k hk a (right.trans ha) (hb.trans_le (cap.trans ((Nat.le_add_right _ _).trans
        (arena.supplement.trans ((Nat.le_add_right _ _).trans arena.counters)))))
  have supp {i k : ℕ} (hi : i<count) (hk : k<count) {a : ℕ} (ha : (os i).layout.supplement ≤ a)
      (hb : a < (os i).layout.supplement+((os i).extra.flatMap record).length) : (os k).cell.Outside a := by
    change l.supplemental+l.stride*global i ≤ a at ha
    change a<l.supplemental+l.stride*global i+((extra (global i)).flatMap record).length at hb
    have cap := sections.supplement (global i) (valid i hi)
    have room := Nat.mul_le_mul_left l.stride (valid i hi)
    rw [Nat.mul_succ] at room
    have start := arena.sorted
    have stop := arena.supplement
    have last := arena.counters
    apply gap k hk a <;> omega
  have geomEnd (i : ℕ) (hi : i<count) :
      (os i).geometry+1+((os i).placed.rows.flatMap record).length+(fieldList vector (os i).placed.reports).length ≤ l.sorted :=
    sections.geometry (global i) (valid i hi)
  have table (k : ℕ) (hk : k<count) (a : ℕ) (ha : l.tasks≤a) := high k hk a (arena.tasks.trans ha)
  constructor
  · intro i hi k hki a member
    have hk := hki.trans hi
    have sel := valid i hi
    have sep := separate hki hi
    have first := ends i hi
    have stop := (bounds i hi).2.2.1
    have mrg := (bounds k hk).1
    have g := geomEnd i hi
    have four := arena.four
    have cn := arena.counters
    have sp := arena.supplement
    have so := arena.sorted
    change a ∈ [l.tasks+7*i+1,l.four+4*i,l.four+4*i+1,l.four+4*i+2,l.four+4*i+3,
      (os i).layout.tail+1,(os i).layout.tail+2,(os i).geometry,l.counters+2*global i,l.counters+2*global i+1] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact table k hk _ (by omega)
    · exact high k hk _ (by omega)
    · exact high k hk _ (by omega)
    · exact high k hk _ (by omega)
    · exact high k hk _ (by omega)
    · change _ ≠ (os k).layout.merged ∧ (_ < (os k).layout.tail ∨ (os k).layout.tail+12 ≤ _)
      omega
    · change _ ≠ (os k).layout.merged ∧ (_ < (os k).layout.tail ∨ (os k).layout.tail+12 ≤ _)
      omega
    · exact low k hk _ (by omega)
    · exact gap k hk _ (by omega) (by omega)
    · exact gap k hk _ (by omega) (by omega)
  · intro i hi k hki a source
    have hk := hki.trans_lt hi
    obtain ⟨start,ha⟩ | ⟨u,member,lo,hi'⟩ | ⟨_,hg⟩ | ⟨lo,hs⟩ | ⟨lo,he⟩ := source
    · change a < (os i).placed.descriptorBase+(CellPacket.descriptors (prefixChunks (os i).placed)).length at ha
      rw [ends i hi] at ha
      have stop := (bounds i hi).2.2.1
      have mrg := (bounds k hk).1
      change a≠(os k).layout.merged ∧ (a<(os k).layout.tail ∨ (os k).layout.tail+12≤a)
      rcases hki.eq_or_lt with rfl|lt
      · omega
      · have between := separate lt hi
        change (os i).placed.descriptorBase ≤ a at start
        omega
    · exact chunk hi hk u member lo hi'
    · change a < (os i).geometry+(fieldList record (os i).placed.rows++fieldList vector (os i).placed.reports).length at hg
      simp only [fieldList,List.length_append,List.length_cons] at hg
      have h := geomEnd i hi
      simp only [fieldList,List.length_cons] at h
      exact low k hk a (by omega)
    · exact supp hi hk lo hs
    · change a < (os i).placed.externalBase+([] : List Bool).length at he
      change (os i).placed.externalBase ≤ a at lo
      simp only [List.length_nil,Nat.add_zero] at he
      omega
  · intro i hi k hik hk a source
    obtain ⟨lo,_⟩ | ⟨_,hd⟩ | ⟨lo,he⟩ | ⟨u,member,lo,hu⟩ := source
    · exact table k hk a (by omega)
    · have prefixEnd := ends i hi
      rw [CellPacket.descriptors_length] at prefixEnd
      change a < (os i).placed.descriptorBase+3*(prefixChunks (os i).placed++tailChunks (os i).layout
        (chunkPlacement (os i).placed) (os i).geometry (os i).extra).length at hd
      rw [List.length_append,show (tailChunks (os i).layout (chunkPlacement (os i).placed) (os i).geometry (os i).extra).length=4 from rfl,
        Nat.mul_add] at hd
      have next := separate hik hk
      have nextPrefix := ends k hk
      have stop := (bounds i hi).2.2.1
      have mrg := (bounds k hk).1
      change a≠(os k).layout.merged ∧ (a<(os k).layout.tail ∨ (os k).layout.tail+12≤a)
      omega
    · change a<(os i).placed.externalBase+([] : List Bool).length at he
      change (os i).placed.externalBase≤a at lo
      simp only [List.length_nil,Nat.add_zero] at he
      omega
    · change u ∈ prefixChunks (os i).placed++tailChunks (os i).layout (chunkPlacement (os i).placed) (os i).geometry (os i).extra at member
      obtain before | after := List.mem_append.mp member
      · exact chunk hi hk u before lo hu
      · simp only [tailChunks,List.mem_cons,List.not_mem_nil,or_false] at after
        rcases after with rfl|rfl|rfl|rfl <;> simp only [Chunk.base,Chunk.endSource,List.length_cons,List.length_nil] at lo hu
        · have first := (bounds i hi).1
          have last := (bounds k hk).1
          have separated := global_strict l.toLayout raw hik hk
          have stop := (bounds k hk).2.2.1
          change a≠(os k).layout.merged ∧ (a<(os k).layout.tail ∨ (os k).layout.tail+12≤a)
          omega
        · have h := geomEnd i hi
          change a < (os i).geometry+1+((os i).placed.rows.flatMap record).length at hu
          exact low k hk a (by omega)
        · exact supp hi hk lo hu
        · exact low k hk a (hu.trans_le (geomEnd i hi))
  · intro i _ k hk j _
    exact table k hk _ (by omega)

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
