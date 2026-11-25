import OAI.Computability.BorderVNP.CellPacketSupplementalTyped

/-! # The patched descriptor image and the true spliced cell input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket.Supplement

open VPVNP.BurstRAM DiagonalResidueRAM Packing.Directory.ISA CellSparse CellSparse.Packet

variable {w : ℕ} {Site : Type}

/-- Addresses outside both the merged count and the four reserved triples. -/
def Outside (l : Layout) (a : ℕ) : Prop := a ≠ l.merged ∧ (a < l.tail ∨ l.tail+12 ≤ a)

/-- The native count and descriptor prepass has no other memory effects. -/
theorem image_outside (l : Layout) (d : Data) (m : Memory w) {a : ℕ} (outside : Outside l a) :
    image l d m a = m a := by
  rw [image,putWords_outside,Function.update_of_ne outside.1]
  simpa [descriptors] using outside.2

/-- The actual native descriptor stores read back as natural values when all
declared addresses and counts fit the physical words. -/
theorem descriptor_read (l : Layout) (d : Data) (m : Memory w)
    (fit : ∀ x ∈ descriptors l d, x < 2^w) :
    WordsAt (readings (image l d m)) l.tail (descriptors l d) := by
  intro i
  change (putWords _ l.tail ((descriptors l d).map (DiagonalResidueRAM.word w)) (l.tail+i.val)).val = _
  have k : i.val < ((descriptors l d).map (DiagonalResidueRAM.word w)).length := by simpa only [List.length_map] using i.isLt
  have read := congrArg Fin.val (putWords_read (Function.update m l.merged (DiagonalResidueRAM.word w (d.geomCount+d.suppCount)))
    l.tail ((descriptors l d).map (DiagonalResidueRAM.word w)) ⟨i.val,k⟩)
  change (putWords _ _ _ (l.tail+i.val)).val = (((descriptors l d).map (DiagonalResidueRAM.word w))[i.val]).val at read
  simpa only [List.getElem_map,word_val _ _ (fit _ (List.getElem_mem i.isLt))] using read

/-- Scalar and address registers loaded by the prepass suffice for the descriptor
representability proof, even though the supplemental word count depends on the sidecars. -/
theorem descriptors_fit (l : Layout) (d : Data) (s : Bank w) (m : Memory w) (input : Input l d s m)
    (baseFit : d.geomBase+1+d.geomWords < 2^w) (hw : 0 < w) :
    ∀ x ∈ descriptors l d, x < 2^w := by
  have merged := input.merged.symm.trans_lt (s 5).isLt
  have extra := input.source.symm.trans_lt (s 3).isLt
  have words := input.suppWords.symm.trans_lt (m (l.counters+1)).isLt
  have report := input.report.symm.trans_lt (s 6).isLt
  have one : 1 < 2^w := Nat.one_lt_pow hw.ne' (by decide)
  intro x hx
  simp only [descriptors,List.mem_cons,List.not_mem_nil,or_false] at hx
  omega

private theorem append_words {mem : ℕ → ℕ} {a : ℕ} {xs ys : List ℕ}
    (hx : WordsAt mem a xs) (hy : WordsAt mem (a+xs.length) ys) : WordsAt mem a (xs++ys) := by
  intro i
  by_cases left : i.val < xs.length
  · simpa only [List.getElem_append_left left] using hx ⟨i.val,left⟩
  · have bound : i.val-xs.length < ys.length := by have h := i.isLt; simp only [List.length_append] at h; omega
    have h := hy ⟨i.val-xs.length,bound⟩
    simp only [List.getElem_append_right (by omega : xs.length ≤ i.val)]
    simpa only [show a+xs.length+(i.val-xs.length)=a+i.val by omega] using h

private theorem keepWords (l : Layout) (d : Data) (m : Memory w) (a : ℕ) (xs : List ℕ)
    (src : WordsAt (readings m) a xs) (away : ∀ i < xs.length, Outside l (a+i)) :
    WordsAt (readings (image l d m)) a xs := by
  intro i
  change (image l d m (a+i.val)).val = _
  rw [image_outside l d m (away _ i.isLt)]
  exact src i

private theorem keepChunk (l : Layout) (d : Data) (m : Memory w) (c : Chunk)
    (h : c.Stored (readings m)) (away : ∀ a, c.base ≤ a → a < c.endSource → Outside l a) :
    c.Stored (readings (image l d m)) := by
  cases c with
  | words a xs =>
    exact keepWords l d m a xs h (fun i hi => away (a+i) (Nat.le_add_right ..) (Nat.add_lt_add_left hi _))
  | box a H bs =>
    change ∀ j, a ≤ j → j < a+H+bs.length → Outside l j at away
    refine ⟨h.1,fun i => ?_, fun i => ?_⟩
    · change (image l d m (a+i.val)).val = _
      rw [image_outside l d m (away (a+i.val) (Nat.le_add_right ..) (by have := i.isLt; omega))]
      exact h.2.1 i
    · change (image l d m (a+H+i.val)).val = _
      rw [image_outside l d m (away (a+H+i.val) (by omega) (Nat.add_lt_add_left i.isLt _))]
      exact h.2.2 i

/-- The physical post-prepass memory satisfies the initializer input for the
merged typed directory. Public geometry and the true supplemental producer supply
separate word banks, and the count and four triples come from actual prepass stores. -/
theorem stored (p : Placed Site) (l : Layout) (base : ℕ) (extra : List Record) (m : Memory w)
    (report : l.reportWords = (fieldList vector p.reports).length)
    (endPrefix : p.descriptorBase+(CellPacket.descriptors (prefixChunks p)).length = l.tail)
    (prefixRows : WordsAt (readings m) p.descriptorBase (CellPacket.descriptors (prefixChunks p)))
    (boxes : ∀ c ∈ prefixChunks p, c.Stored (readings m))
    (geom : WordsAt (readings m) base (fieldList record p.rows++fieldList vector p.reports))
    (supp : WordsAt (readings m) l.supplement (extra.flatMap record))
    (external : CompactWrite.Source m p.externalBase p.external)
    (prefixAway : ∀ i < (CellPacket.descriptors (prefixChunks p)).length, Outside l (p.descriptorBase+i))
    (boxAway : ∀ c ∈ prefixChunks p, ∀ a, c.base ≤ a → a < c.endSource → Outside l a)
    (geomAway : ∀ i < (fieldList record p.rows++fieldList vector p.reports).length, Outside l (base+i))
    (suppAway : ∀ i < (extra.flatMap record).length, Outside l (l.supplement+i))
    (extAway : ∀ i < p.external.length, Outside l (p.externalBase+i))
    (countApart : l.merged < l.tail ∨ l.tail+12 ≤ l.merged)
    (countFit : p.rows.length+extra.length < 2^w)
    (descFit : ∀ x ∈ descriptors l (measured base p.rows extra), x < 2^w) :
    (task l p base extra).Stored (image l (measured base p.rows extra) m) := by
  let d := measured base p.rows extra
  let mt := image l d m
  have gs := keepWords l d m base _ geom geomAway
  have gs' : WordsAt (readings mt) base ([p.rows.length] ++
      ((p.rows.flatMap record)++fieldList vector p.reports)) := gs
  have ts : WordsAt (readings mt) (base+1) ((p.rows.flatMap record)++fieldList vector p.reports) := gs'.right
  have use := keepWords l d m _ _ supp suppAway
  have merge : (image l d m l.merged).val = p.rows.length+extra.length := by
    rw [image,putWords_outside,Function.update_self,word_val]
    · rfl
    · exact countFit
    · simpa [descriptors] using countApart
  constructor
  · change WordsAt (readings mt) p.descriptorBase
      ((prefixChunks p ++ tailChunks l p base extra).flatMap Chunk.descriptor)
    rw [List.flatMap_append]
    apply append_words (keepWords l d m _ _ prefixRows prefixAway)
    change WordsAt (readings mt) (p.descriptorBase+(CellPacket.descriptors (prefixChunks p)).length) (CellPacket.descriptors (tailChunks l p base extra))
    rw [endPrefix,tail_descriptors l p base extra report]
    exact descriptor_read l d m descFit
  · intro c hc
    change c ∈ prefixChunks p ++ tailChunks l p base extra at hc
    rcases List.mem_append.mp hc with hp | ht
    · exact keepChunk l d m c (boxes c hp) (boxAway c hp)
    · simp only [tailChunks,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · change WordsAt (readings mt) l.merged [p.rows.length+extra.length]
        intro i
        change (image l d m (l.merged+i.val)).val = [p.rows.length+extra.length][i.val]
        simp [merge]
      · exact ts.left
      · exact use
      · exact ts.right
  · intro i hi
    change (image l d m (p.externalBase+i)).val = _
    rw [image_outside l d m (extAway i hi)]
    exact external i hi

end RoutingISA.CellPacket.Supplement

end BorderVNP
end Computability
end OAI
