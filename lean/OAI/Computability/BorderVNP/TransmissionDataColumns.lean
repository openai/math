import OAI.Computability.BorderVNP.TransmissionDataLastWrite
import OAI.Computability.BorderVNP.PackedDirectoryProgram

/-! # Correspondence of the two native seven-column encodings -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM Packing.Directory
open DiagonalResidueRAM (word word_val)
open Packing.Directory.ISA (encodeRows encodeRows_length)

variable {w : ℕ}

private theorem row_words (r : Row) : r.words.length = 7 := rfl

private theorem encodeRows_at (rows : List Row) (i : Fin rows.length) (j : Fin 7) :
    (encodeRows w rows)[i.val*7+j.val]? = some (word w ((rows[i.val]).words[j.val]'j.isLt)) := by
  induction rows with
  | nil => exact i.elim0
  | cons r rows ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.val_zero,Nat.zero_mul,Nat.zero_add,encodeRows,List.flatMap_cons,List.getElem_cons_zero]
      rw [List.getElem?_append_left (by simpa only [List.length_map,row_words] using j.isLt),
        List.getElem?_eq_getElem (by simpa only [List.length_map,row_words] using j.isLt),
        List.getElem_map]
    · change (r.words.map (word w) ++ encodeRows w rows)[(k.val+1)*7+j.val]? = some _
      have atEnd : (r.words.map (word w)).length ≤ (k.val+1)*7+j.val := by rw [List.length_map,row_words]; omega
      rw [List.getElem?_append_right atEnd,List.length_map,row_words,
        show (k.val+1)*7+j.val-7 = k.val*7+j.val by omega]
      exact ih k

/-- A read from the true input published by the placement generator recovers the
seven original natural fields, at their true compacted row number. -/
theorem DataWriter.demandAt_published (m : Memory w) (frame base : ℕ) (rows : List Row)
    (before : frame+9 < base) (i : Fin rows.length)
    (fitted : ∀ x ∈ rows[i.val].words, x < 2^w) :
    demandAt (readings (Packing.Directory.ISA.publish m frame base rows)) (base+i.val*7) = rows[i.val] := by
  obtain ⟨_,read⟩ := Packing.Directory.ISA.publish_read m frame base rows before
  have atWord (j : Fin 7) : readings (Packing.Directory.ISA.publish m frame base rows)
      (base+i.val*7+j.val) = (rows[i.val]).words[j.val]'j.isLt := by
    have room : i.val*7+j.val < (encodeRows w rows).length := by rw [encodeRows_length]; have := i.isLt; have := j.isLt; omega
    have eq := encodeRows_at (w := w) rows i j
    rw [List.getElem?_eq_getElem room] at eq
    have h := read ⟨i.val*7+j.val,room⟩
    change (Packing.Directory.ISA.publish m frame base rows (base+i.val*7+j.val)).val = _
    rw [Nat.add_assoc, h]
    change ((encodeRows w rows)[i.val*7+j.val]'room).val = _
    exact (congrArg Fin.val (Option.some.inj eq)).trans (word_val _ _ (fitted _ (List.getElem_mem j.isLt)))
  exact congrArg₇_row (atWord 0) (atWord 1) (atWord 2) (atWord 3) (atWord 4) (atWord 5) (atWord 6)
where
  congrArg₇_row {a b c d e f g a' b' c' d' e' f' g' : ℕ}
      (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') (he : e = e') (hf : f = f') (hg : g = g') :
      Row.mk a b c d e f g = Row.mk a' b' c' d' e' f' g' := by subst_vars; rfl

/-- Native scheduled rows have the destination columns used by `data_lastWrite`
whenever the public owner table encodes the fixed-stride bank allocation and the
shared-row appender retains the data prefix written by the native compiler. -/
theorem DataColumns.of_image {l : TableLayout} {row : ℕ → TableRow} {before : ℕ → ℕ} {after : Memory w}
    (image : l.Image row before (readings after)) (al : l.Allocated w)
    (d : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → ℕ) (origin stride : ℕ)
    (emit : DataWriter.Layout) (m : Memory w) (count : (d.directory pp lp).length ≤ l.count)
    (owners : ∀ i : Fin (d.directory pp lp).length,
      let cell := (d.directory pp lp)[i.val].cell
      readings m (emit.owners+cell*2) = owner cell ∧
      readings m (emit.owners+cell*2+1) = origin+cell*stride)
    (recorded : ∀ i : Fin (d.directory pp lp).length, ∀ j : Fin 7,
      before (l.records+i.val*7+j.val) =
        (DataWriter.record emit (readings m) (d.directory pp lp)[i.val])[j.val]'j.isLt) :
    DataColumns (tableRange l after) d pp lp owner origin stride := by
  have fields (i : Fin (d.directory pp lp).length) :=
    DataWriter.range_fields image al (i.isLt.trans_le count) emit m (d.directory pp lp)[i.val] (recorded i)
  refine ⟨fun i => ?_,fun i => (fields i).2.2.1.trans (owners i).1,
    fun i => (fields i).2.2.2.1,fun i => ?_⟩
  · apply Fin.ext
    have bound := (tableRange l after i).kind.isLt
    rw [(fields i).1] at bound ⊢
    rw [Fin.val_one',Nat.mod_eq_of_lt bound]
  · rw [(fields i).2.2.2.2.2.2,(owners i).2]

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
