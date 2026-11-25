import OAI.Computability.BorderVNP.CellPacketSupplementalBatch
import OAI.Computability.BorderVNP.RoutingISATypedBatchMemory

/-! # Reading each patched typed initializer from the completed supplemental batch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket

open VPVNP.BurstRAM

/-- A physical chunk stays readable when every address in its source interval is preserved. -/
theorem Chunk.Stored.congr {c : Chunk} {old new : ℕ → ℕ} (src : c.Stored old)
    (keep : ∀ a, c.base ≤ a → a < c.endSource → new a = old a) : c.Stored new := by
  cases c with
  | words a xs =>
    dsimp only [Chunk.base,Chunk.endSource] at keep
    intro j
    rw [keep _ (Nat.le_add_right ..) (Nat.add_lt_add_left j.isLt a)]
    exact src j
  | box a H xs =>
    dsimp only [Chunk.base,Chunk.endSource] at keep
    refine ⟨src.1,fun j => ?_,fun j => ?_⟩
    · rw [keep _ (Nat.le_add_right ..) (by have := j.isLt; omega)]
      exact src.2.1 j
    · rw [keep _ (by omega) (Nat.add_lt_add_left j.isLt _)]
      exact src.2.2 j

/-- Transfer a typed initializer through a physical memory update preserving the
same source addresses used by the genuine seven-word task scanner. -/
theorem Task.Stored.congr_sources {w table i : ℕ} {t : TypedBatch.Task} {m mt : Memory w}
    (src : t.cell.Stored m) (keep : ∀ a, t.SourceAt table i a → mt a = m a) : t.cell.Stored mt := by
  have value (a : ℕ) (h : t.SourceAt table i a) : readings mt a = readings m a := congrArg Fin.val (keep a h)
  constructor
  · intro j
    have len := j.isLt.trans_eq (descriptors_length t.cell.chunks)
    rw [value _ (.inr (.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left len _⟩))]
    exact src.descriptors j
  · intro c hc
    exact (src.chunks c hc).congr (fun a lo hi => value a (.inr (.inr (.inr ⟨c,hc,lo,hi⟩))))
  · intro j hj
    rw [keep _ (.inr (.inr (.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left hj _⟩)))]
    exact src.external j hj

namespace Supplement.Batch

open CellSparse CellSparse.Packet

variable {w i count tasks controls : ℕ} {Site : Type}

/-- The five original arrays consumed by the one-cell proof, before any supplemental
writes. Prefix chunks include actual length-delimited private boxes. -/
structure Original (p : Placed Site) (l : Layout) (base : ℕ) (extra : List Record) (m : Memory w) : Prop where
  prefixRows : WordsAt (readings m) p.descriptorBase (CellPacket.descriptors (prefixChunks p))
  boxes : ∀ c ∈ prefixChunks p, c.Stored (readings m)
  geom : WordsAt (readings m) base (fieldList record p.rows++fieldList vector p.reports)
  supp : WordsAt (readings m) l.supplement (extra.flatMap record)
  ext : CompactWrite.Source m p.externalBase p.external

/-- The true prepass needs these original typed source intervals only up to and
including this row's own descriptor patch. -/
def originalSource (p : Placed Site) (l : Layout) (base : ℕ) (extra : List Record) (a : ℕ) : Prop :=
  (p.descriptorBase ≤ a ∧ a < p.descriptorBase+(CellPacket.descriptors (prefixChunks p)).length) ∨
  (∃ c ∈ prefixChunks p, c.base ≤ a ∧ a < c.endSource) ∨
  (base ≤ a ∧ a < base+(fieldList record p.rows++fieldList vector p.reports).length) ∨
  (l.supplement ≤ a ∧ a < l.supplement+(extra.flatMap record).length) ∨
  (p.externalBase ≤ a ∧ a < p.externalBase+p.external.length)

private theorem Stored.desc_fit {c : Cell} {m : Memory w} (row : Stored c tasks controls i m) (room : Room c w) :
    ∀ x ∈ Supplement.descriptors c.layout c.data, x < 2^w := by
  have merged := row.merged.symm.trans_lt (m (controls+4*i+2)).isLt
  have source := row.source.symm.trans_lt (m (controls+4*i)).isLt
  have words := row.suppWords.symm.trans_lt (m (c.layout.counters+1)).isLt
  have reports := row.report.symm.trans_lt (m (controls+4*i+3)).isLt
  have tail := room.tail
  have base := room.base
  intro x hx
  simp only [Supplement.descriptors,List.mem_cons,List.not_mem_nil,or_false] at hx
  omega

/-- The task-table endpoint used by the actual batch loader is exactly twelve words
past the first tail descriptor, as there are four consecutive three-word chunks. -/
theorem tailEnd_of_taskRow (m : Memory w) (p : Placed Site) (l : Layout) (base callRow : ℕ) (extra : List Record)
    (prefixEnd : p.descriptorBase+(CellPacket.descriptors (prefixChunks p)).length = l.tail)
    (row : (⟨Supplement.task l p base extra,callRow⟩ : TypedBatch.Task).Stored m tasks i) :
    readings m (tasks+7*i+1) = l.tail+12 := by
  have value := row.2.1
  change readings m (tasks+7*i+1) = p.descriptorBase+3*(prefixChunks p++tailChunks l p base extra).length at value
  rw [CellPacket.descriptors_length] at prefixEnd
  rw [List.length_append,show (tailChunks l p base extra).length = 4 from rfl] at value
  omega

/-- All seven scalar fields of a typed task are still present after the supplemental
prepass, even though the descriptors to which they point have been rewritten. -/
theorem task_row (m : Memory w) (cells : ℕ → Cell) (t : TypedBatch.Task)
    (row : t.Stored m tasks i) (apart : ∀ k < count, ∀ j < 7, (cells k).Outside (tasks+7*i+j)) :
    t.Stored (written m cells count) tasks i := by
  have keep (j : ℕ) (hj : j < 7) : written m cells count (tasks+7*i+j) = m (tasks+7*i+j) :=
    preserve m cells (i := 0) (Nat.zero_le _) _ fun k _ hk => apart k hk j hj
  unfold TypedBatch.Task.Stored
  simp only [show written m cells count (tasks+7*i) = m (tasks+7*i) from keep 0 (by decide),
    keep 1 (by decide),keep 2 (by decide),keep 3 (by decide),keep 4 (by decide),keep 5 (by decide),keep 6 (by decide)]
  exact row

set_option maxRecDepth 2000 in
/-- The actual typed initializer for an owned cell can read its merged argument in the
completed batch. Before its patch all original inputs are protected. Afterward the
seven-word task's reads, including the new merged count and descriptors, are protected. -/
theorem typed_stored (m : Memory w) (cells : ℕ → Cell) (hi : i < count) (p : Placed Site)
    (base callRow : ℕ) (extra : List Record) (measures : (cells i).data = measured base p.rows extra)
    (report : (cells i).layout.reportWords = (fieldList vector p.reports).length)
    (endPrefix : p.descriptorBase+(CellPacket.descriptors (prefixChunks p)).length = (cells i).layout.tail)
    (row : Stored (cells i) tasks controls i m) (room : Room (cells i) w)
    (original : Original p (cells i).layout base extra m)
    (self : (cells i).layout.merged < (cells i).layout.tail ∨ (cells i).layout.tail+12 ≤ (cells i).layout.merged)
    (early : ∀ k ≤ i, ∀ a, originalSource p (cells i).layout base extra a → (cells k).Outside a)
    (later : ∀ k, i < k → k < count → ∀ a,
      (⟨Supplement.task (cells i).layout p base extra,callRow⟩ : TypedBatch.Task).SourceAt tasks i a →
        (cells k).Outside a) :
    (Supplement.task (cells i).layout p base extra).Stored (written m cells count) := by
  let l := (cells i).layout
  let t : TypedBatch.Task := ⟨Supplement.task l p base extra,callRow⟩
  have keep (a : ℕ) (h : originalSource p l base extra a) : written m cells i a = m a :=
    preserve m cells (i := 0) (Nat.zero_le _) a fun k _ hk => early k hk.le a h
  have take (a : ℕ) (xs : List ℕ) (before : WordsAt (readings m) a xs)
      (included : ∀ b, a ≤ b → b < a+xs.length → originalSource p l base extra b) :
      WordsAt (readings (written m cells i)) a xs := by
    intro j
    change (written m cells i (a+j.val)).val = _
    rw [keep _ (included _ (Nat.le_add_right ..) (Nat.add_lt_add_left j.isLt _))]
    exact before j
  have pref := take _ _ original.prefixRows fun _ lo up => Or.inl ⟨lo,up⟩
  have geo := take _ _ original.geom fun _ lo up => Or.inr (.inr (.inl ⟨lo,up⟩))
  have supp := take _ _ original.supp fun _ lo up => Or.inr (.inr (.inr (.inl ⟨lo,up⟩)))
  have boxes (c : Chunk) (hc : c ∈ prefixChunks p) : c.Stored (readings (written m cells i)) :=
    Chunk.Stored.congr (original.boxes c hc) fun a lo up => congrArg Fin.val (keep a (.inr (.inl ⟨c,hc,lo,up⟩)))
  have ext : CompactWrite.Source (written m cells i) p.externalBase p.external := by
    intro j hj
    rw [keep _ (.inr (.inr (.inr (.inr ⟨Nat.le_add_right ..,Nat.add_lt_add_left hj _⟩))))]
    exact original.ext j hj
  have countFit : p.rows.length+extra.length < 2^w := by
    have sumFit := room.count
    rw [measures] at sumFit
    exact sumFit
  have fits : ∀ x ∈ Supplement.descriptors l (measured base p.rows extra), x < 2^w := measures ▸ row.desc_fit room
  have now : t.cell.Stored (written m cells (i+1)) := by
    rw [written,measures]
    exact Supplement.stored p l base extra _ report endPrefix pref boxes geo supp ext
      (fun j hj => early i le_rfl _ (.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left hj _⟩))
      (fun c hc a lo up => early i le_rfl a (.inr (.inl ⟨c,hc,lo,up⟩)))
      (fun j hj => early i le_rfl _ (.inr (.inr (.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left hj _⟩))))
      (fun j hj => early i le_rfl _ (.inr (.inr (.inr (.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left hj _⟩)))))
      (fun j hj => early i le_rfl _ (.inr (.inr (.inr (.inr ⟨Nat.le_add_right ..,Nat.add_lt_add_left hj _⟩)))))
      self countFit fits
  exact now.congr_sources (t := t) fun a ha => preserve m cells (i := i+1) hi a (fun k hk hc => later k hk hc a ha)

end Supplement.Batch
end RoutingISA.CellPacket

end BorderVNP
end Computability
end OAI
