import OAI.Computability.BorderVNP.RoutingISAFiniteScalarPhysical
import OAI.Computability.BorderVNP.RoutingISATypedTaskAllocation

/-! # Live scalar suffixes after signed packet construction

All task headers, exterior words and tail widths precede the reusable scratch
arena. The signed validators publish only to their own argument fields.
The subsequent finite-field suffix packs therefore recover the actual claims
of each checked cell from the same shared memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FiniteScalarBatch

open VPVNP.BurstRAM Packing.Directory.ISA TypedTaskBuilder

variable {w : ℕ}

/-- A scalar pack does not touch an address below every task's scratch interval. -/
theorem written_below (m : Memory w) (rows : ℕ → Row) (i a : ℕ)
    (below : ∀ k < i, a < (rows k).task.cell.scratchBase) : written m rows i a = m a := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [written,Row.image,putWords_outside _ _ _ _ (.inl (below i (Nat.lt_succ_self _)))]
    exact ih (fun j h => below j (Nat.lt_succ_of_lt h))

/-- Reusing a signed task's scratch arena leaves enough words to pack its checked
tail. This also holds for a cell with zero report bits. -/
theorem Row.pack_le (r : Row) (hw : 2 ≤ w) (bank : r.task.cell.external=r.supplied++r.claims) :
    (r.words w).length ≤ r.task.cell.payload.length := by
  rw [Row.words,CompactFrame.length_pack,←CompactFrame.wordCount,CompactFrame.wordCount_terminator (by omega)]
  have div : (2*r.claims.length)/w ≤ r.claims.length := by
    calc _ ≤ (w*r.claims.length)/w := Nat.div_le_div_right (Nat.mul_le_mul_right _ hw)
         _ = _ := Nat.mul_div_cancel_left _ (by omega)
  simp only [CellPacket.Task.payload,CellPacket.envelope,RationalHitting.StackLanguage.codeWord_length,bank,List.length_append]
  omega

variable (l : Layout) (publicMem : ℕ → ℕ) (rows : ℕ → Row)

/-- The exterior inputs, actual counts, and native task rows survive the complete
signed preparation and all earlier scalar scratch stores. -/
theorem live {original : Memory w} (room : l.Room publicMem w) (ar : l.Arenas publicMem w (fun j => (rows j).task))
    (tailRange : l.SourceRange l.tails l.cells)
    (ids : ∀ i < l.before publicMem l.cells, (rows i).cell=globalCell l publicMem i)
    (stored : ∀ i < l.before publicMem l.cells, (rows i).task.Stored original l.tasks i)
    (data : ∀ i < l.before publicMem l.cells, (rows i).task.cell.Stored original)
    (bank : ∀ i < l.before publicMem l.cells, (rows i).task.cell.external=(rows i).supplied++(rows i).claims)
    (tail : ∀ i < l.before publicMem l.cells, (original (l.tails+(rows i).cell)).val=(rows i).claims.length) :
    let count := l.before publicMem l.cells
    let after := TypedBatch.written original (fun j => (rows j).task) count
    ∀ i < count, Stored (rows i) (written after rows i) l.tasks l.calls l.tails i ∧ Fits (rows i) w l.tails := by
  intro count after i hi
  let r := rows i
  have global : r.cell < l.cells := by rw [show r.cell = _ from ids i hi]; exact (global_spec l publicMem hi).1
  have count_le : count ≤ l.cells := l.before_le publicMem l.cells
  have keep (a : ℕ) (below : a < l.scratch) (apart : a < l.calls ∨ l.calls+3*l.cells ≤ a) :
      written after rows i a = original a := by
    rw [written_below after rows i a (fun j hj => by
      have sr := (ar.starts j (hj.trans hi)).2.1
      change (rows j).task.cell.scratchBase = _ at sr
      omega)]
    exact TypedBatch.preserve original (fun j => (rows j).task) (i:=0) (Nat.zero_le _) a
      (fun j _ hj => TypedTaskBuilder.below l publicMem ar hj below apart)
  have header (k : ℕ) (hk : k < 7) : written after rows i (l.tasks+7*i+k)=original (l.tasks+7*i+k) := by
    apply keep
    · have h := ar.table; omega
    · rcases room.ownerTasks with z|z <;> omega
  have ext := ar.external i hi
  change l.SourceRange r.task.cell.externalBase r.task.cell.external.length at ext
  have len := congrArg List.length (bank i hi)
  change r.task.cell.external.length = (r.supplied++r.claims).length at len
  rw [List.length_append] at len
  have cellRoom := task_room l publicMem room ar hi
  change r.task.cell.Room w at cellRoom
  have st := stored i hi
  change r.task.Stored original l.tasks i at st
  have tbase := (ar.starts i hi).2.1
  change r.task.cell.scratchBase = _ at tbase
  have hw : 2 ≤ w := by
    by_contra! h
    have hf := room.frame
    have p := Nat.pow_le_pow_right (show 0 < 2 by decide) (show w ≤ 1 by omega)
    norm_num at p
    omega
  have q := r.pack_le hw (bank i hi)
  change Stored r (written after rows i) l.tasks l.calls l.tails i ∧ Fits r w l.tails
  constructor
  · constructor
    · unfold TypedBatch.Task.Stored at st ⊢
      simp only [show written after rows i (l.tasks+7*i) = original (l.tasks+7*i) from header 0 (by decide),
        header 1 (by decide),header 2 (by decide),header 3 (by decide),header 4 (by decide),
        header 5 (by decide),header 6 (by decide)]
      exact st
    · exact (ar.starts i hi).1.trans (congrArg (l.call ·) (ids i hi).symm)
    · rw [keep _ (by have := tailRange.end_le; omega) (by rcases tailRange.calls with h|h <;> omega)]
      exact tail i hi
    · exact bank i hi
    · have bits := r.source original (bank i hi) (data i hi).external
      intro k hk
      have small := ext.end_le
      change (written after rows i (r.task.cell.externalBase+r.supplied.length+k)).val = _
      rw [keep _ (by omega) (by rcases ext.calls with h|h <;> omega)]
      exact bits _ hk
  · have sFit := cellRoom.sourceFit
    have dst := cellRoom.scratchFit
    have extEnd := ext.end_le
    refine ⟨by have := room.tails; omega,?_,?_,?_,?_,?_⟩
    · change r.task.cell.externalBase+r.supplied.length < 2^w; omega
    · change r.task.cell.externalBase+r.supplied.length+r.claims.length ≤ 2^w; omega
    · exact (Nat.add_le_add_left q _).trans dst.le
    · omega
    · left; change r.task.cell.externalBase+r.supplied.length+r.claims.length ≤ r.task.cell.scratchBase; omega

end RoutingISA.FiniteScalarBatch

end BorderVNP
end Computability
end OAI
