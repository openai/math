import OAI.Computability.BorderVNP.RoutingISATypedBatchScan
import OAI.Computability.BorderVNP.RoutingISACallModel

/-! # Chronological live memory in the typed packet task scan

Each task reads the declared public ranges and the delivered opaque box words before
writing its scratch string, compact burst and two call-row columns. Protection of
later reads and earlier results suffices even when read-only inputs overlap.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedBatch

open VPVNP.BurstRAM Packing.Directory.ISA CellDispatch

/-- The four writes of a task leave this particular shared address untouched. -/
def Task.Outside (t : Task) (w a : ℕ) : Prop :=
  (a < t.cell.scratchBase ∨ t.cell.scratchBase+t.cell.payload.length ≤ a) ∧
  (a < t.cell.burstBase ∨ t.cell.burstBase+(t.cell.burst w).length ≤ a) ∧
  a ≠ t.callRow+1 ∧ a ≠ t.callRow+2

/-- Addresses needed before the two writes of the cell argument and the publication stores. -/
def Task.SourceAt (t : Task) (table i a : ℕ) : Prop :=
  (table+7*i ≤ a ∧ a < table+7*i+7) ∨
  (t.cell.descriptorBase ≤ a ∧ a < t.cell.descriptorBase+3*t.cell.chunks.length) ∨
  (t.cell.externalBase ≤ a ∧ a < t.cell.externalBase+t.cell.external.length) ∨
  ∃ c ∈ t.cell.chunks, c.base ≤ a ∧ a < c.endSource

/-- Memory separation needed by the actual chronology of a team batch. -/
structure Allocated (w table count : ℕ) (tasks : ℕ → Task) : Prop where
  /-- Any future source remains available until the reading task starts. -/
  reads : ∀ i j, i < j → j < count → ∀ a, (tasks j).SourceAt table j a → (tasks i).Outside w a
  /-- Publishing the two columns cannot overwrite this task's own output words. -/
  self : ∀ i < count, ∀ k < ((tasks i).cell.burst w).length,
    (tasks i).cell.burstBase+k ≠ (tasks i).callRow+1 ∧ (tasks i).cell.burstBase+k ≠ (tasks i).callRow+2
  /-- Later tasks preserve the actual packed output and the two published argument fields. -/
  output : ∀ i j, i < j → j < count → ∀ a,
    ((tasks i).cell.burstBase ≤ a ∧ a < (tasks i).cell.burstBase+((tasks i).cell.burst w).length) ∨
      a = (tasks i).callRow+1 ∨ a = (tasks i).callRow+2 → (tasks j).Outside w a

private theorem write_other {w : ℕ} (t : Task) (m : Memory w) (a : ℕ) (h : t.Outside w a) :
    t.publish (t.cell.image m) a = m a := by
  obtain ⟨scratch,burst,first,last⟩ := h
  rw [Task.publish,Function.update_of_ne last,Function.update_of_ne first,CellPacket.Task.image,
    putWords_outside _ _ _ _ burst,putWords_outside _ _ _ _ (by simpa only [List.length_map] using scratch)]

/-- A word is preserved through any number of intervening tasks that do not write its address. -/
theorem preserve {w : ℕ} (m : Memory w) (tasks : ℕ → Task) {i j : ℕ} (ij : i ≤ j) (a : ℕ)
    (h : ∀ k, i ≤ k → k < j → (tasks k).Outside w a) :
    written m tasks j a = written m tasks i a := by
  induction j with
  | zero => have := Nat.eq_zero_of_le_zero ij; subst i; rfl
  | succ j ih =>
    by_cases last : i = j+1
    · rw [last]
    · rw [written,write_other _ _ _ (h _ (by omega) (by omega))]
      exact ih (by omega) (fun k hk hj => h k hk (by omega))

/-- Originally supplied public task rows, chunk descriptors, private box data and
external assignment bits are still present on entry to each task of an allocated scan. -/
theorem Allocated.live {w table count : ℕ} {tasks : ℕ → Task} (layout : Allocated w table count tasks)
    (m : Memory w) (init : ∀ i < count, (tasks i).Stored m table i ∧ (tasks i).cell.Stored m)
    (i : ℕ) (hi : i < count) :
    (tasks i).Stored (written m tasks i) table i ∧ (tasks i).cell.Stored (written m tasks i) := by
  obtain ⟨row,src⟩ := init i hi
  have keep (a : ℕ) (h : (tasks i).SourceAt table i a) : written m tasks i a = m a :=
    preserve m tasks (i := 0) (Nat.zero_le _) a (fun k _ hk => layout.reads k i hk hi a h)
  have field (k : ℕ) (hk : k < 7) : written m tasks i (table+7*i+k) = m (table+7*i+k) :=
    keep _ (.inl ⟨by omega,by omega⟩)
  constructor
  · unfold Task.Stored
    simp only [show written m tasks i (table+7*i)=m (table+7*i) from field 0 (by decide),
      field 1 (by decide),field 2 (by decide),field 3 (by decide),field 4 (by decide),
      field 5 (by decide),field 6 (by decide)]
    exact row
  · constructor
    · intro j
      have hj := j.isLt.trans_eq (CellPacket.descriptors_length _)
      change (written m tasks i ((tasks i).cell.descriptorBase+j.val)).val = _
      rw [keep _ (.inr (.inl ⟨by omega,by omega⟩))]
      exact src.descriptors j
    · intro c hc
      have k (a : ℕ) (lo : c.base ≤ a) (high : a < c.endSource) :
          readings (written m tasks i) a = readings m a :=
        congrArg Fin.val (keep a (.inr (.inr (.inr ⟨c,hc,lo,high⟩))))
      have input := src.chunks c hc
      cases c with
      | words base xs =>
        intro j
        rw [k (base+j.val) (Nat.le_add_right ..) (by simp [CellPacket.Chunk.endSource])]
        exact input j
      | box base h bs =>
        obtain ⟨size,head,body⟩ := input
        refine ⟨size,fun j => ?_,fun j => ?_⟩
        · rw [k (base+j.val) (Nat.le_add_right ..) (by dsimp [CellPacket.Chunk.endSource]; have := j.isLt; omega)]
          exact head j
        · rw [k (base+h+j.val) (by dsimp [CellPacket.Chunk.base]; omega)
            (by dsimp [CellPacket.Chunk.endSource]; have := j.isLt; omega)]
          exact body j
    · intro j hj
      rw [keep _ (.inr (.inr (.inl ⟨by omega,by omega⟩)))]
      exact src.external j hj

/-- At the end of the whole scan the true published registers and all words they name
still equal the output of the corresponding physical task. -/
theorem Allocated.output_words {w table count : ℕ} {tasks : ℕ → Task}
    (layout : Allocated w table count tasks) (m : Memory w) (i : ℕ) (hi : i < count)
    (room : (tasks i).cell.Room w) :
    let t := tasks i
    let mt := written m tasks count
    (mt (t.callRow+1)).val = t.cell.burstBase ∧ (mt (t.callRow+2)).val = (t.cell.burst w).length ∧
      TeamRAM.previous mt (.burst (mt (t.callRow+1)).val (mt (t.callRow+2)).val) = t.cell.burst w := by
  let t := tasks i
  let xs := t.cell.burst w
  let mt := written m tasks count
  have saved (a : ℕ) (ha : (t.cell.burstBase ≤ a ∧ a < t.cell.burstBase+xs.length) ∨
        a = t.callRow+1 ∨ a = t.callRow+2) : mt a = t.publish (t.cell.image (written m tasks i)) a :=
    preserve m tasks (i := i+1) hi a (fun j hj hk => layout.output i j (by omega) hk a ha)
  have baseFit : t.cell.burstBase < 2^w := by
    have size := room.burstFit
    have h : 0 < xs.length := by
      change 0 < (CompactFrame.pack w t.cell.payload).length
      rw [CompactFrame.length_pack,Nat.div_pos_iff]
      have := room.positive; omega
    change t.cell.burstBase + xs.length ≤ 2^w at size
    omega
  have ptr : (mt (t.callRow+1)).val=t.cell.burstBase := by
    rw [saved _ (.inr (.inl rfl)),Task.publish,Function.update_of_ne (by omega),Function.update_self]
    exact DiagonalResidueRAM.word_val _ _ baseFit
  have cnt : (mt (t.callRow+2)).val=xs.length := by
    rw [saved _ (.inr (.inr rfl)),Task.publish,Function.update_self]
    exact DiagonalResidueRAM.word_val _ _ room.countFit
  refine ⟨ptr,cnt,?_⟩
  change TeamRAM.previous mt (.burst (mt (t.callRow+1)).val (mt (t.callRow+2)).val) = xs
  rw [ptr,cnt]
  change List.ofFn (fun k : Fin xs.length => mt (t.cell.burstBase+k.val)) = xs
  have val (k : Fin xs.length) : mt (t.cell.burstBase+k.val) = xs[k] := by
    rw [saved _ (.inl ⟨by omega,by have := k.isLt; omega⟩)]
    have h := layout.self i hi k k.isLt
    rw [Task.publish,Function.update_of_ne h.2,Function.update_of_ne h.1,CellPacket.Task.image]
    exact putWords_read ..
  simp_rw [val]
  exact List.ofFn_getElem ..

end RoutingISA.TypedBatch

end BorderVNP
end Computability
end OAI
