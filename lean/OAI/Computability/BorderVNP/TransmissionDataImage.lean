import OAI.Computability.BorderVNP.TransmissionDataProgram
import OAI.Computability.BorderVNP.TransmissionScheduled

/-! # Reading a compiled data row from the scheduled transmission directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission.DataWriter

open VPVNP.BurstRAM Packing.Directory
open Packing.Directory.ISA (putWords putWords_append putWords_outside putWords_read)
open DiagonalResidueRAM (word)
open private prefix_length from OAI.Computability.BorderVNP.TransmissionDataProgram
open private addFieldVal cursorVal from OAI.Computability.BorderVNP.TransmissionScheduled

variable {w : ℕ}

private theorem prefix_read (d : Layout) (m : Memory w) {i k : ℕ} (hi : i < k) (j : Fin 7) :
    putWords m d.output (emittedPrefix d m k) (d.output+i*7+j.val) = (encoded d m i)[j.val]'j.isLt := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [emittedPrefix,putWords_append,prefix_length]
    by_cases h : i = k
    · subst k; exact putWords_read _ _ (encoded d m i) ⟨j.val,j.isLt⟩
    · rw [putWords_outside _ _ _ _ (Or.inl (by have := j.isLt; omega))]
      exact ih (by omega)

/-- The published count and every column of every populated data transfer record are
present in the addressed memory handed to the shared-row append phase. -/
theorem publish_read (d : Layout) (pub : Arg → Word w) (m : Memory w)
    (separate : (pub 0).val+13 < d.output ∨ d.output+d.count*7 ≤ (pub 0).val+13) :
    publish d pub m ((pub 0).val+13) = word w d.count ∧ ∀ i < d.count, ∀ j : Fin 7,
      publish d pub m (d.output+i*7+j.val) = (encoded d m i)[j.val]'j.isLt := by
  refine ⟨Function.update_self ..,fun i hi j => ?_⟩
  have neq : d.output+i*7+j.val ≠ (pub 0).val+13 := by rcases separate with a | a <;> have := j.isLt <;> omega
  rw [publish,Function.update_of_ne neq,prefix_read d m hi]

/-- Data semantics of the complete seven words in a physical scheduler record. The
scheduler computes the extra ordinal in its separate table and leaves the source,
owner and both slot words intact. -/
theorem range_fields {l : TableLayout} {row : ℕ → TableRow} {before : ℕ → ℕ} {after : Memory w}
    (image : l.Image row before (readings after)) (al : l.Allocated w) {i : ℕ} (hi : i < l.count)
    (d : Layout) (m : Memory w) (r : Row)
    (recorded : ∀ j : Fin 7, before (l.records+i*7+j.val) =
      (record d (readings m) r)[j.val]'j.isLt) :
    let v := tableRange l after i
    v.kind.val = 1 ∧ v.teamA.val = r.team ∧
      v.teamB.val = readings m (d.owners+r.cell*2) ∧ v.width.val = r.width ∧
      v.source.val = r.sourceBase d.pins ∧ v.dstA.val = 0 ∧
      v.dstB.val = readings m (d.owners+r.cell*2+1) + r.slot := by
  let base := cursorAt (Fin.ofNat _ l.records : Word w) 7 i
  have cap : l.records+i*7+6 < 2^w := by
    have := al.address (l.contains_record hi (by decide : 6 < 7)); omega
  have bv : base.val = l.records+i*7 := cursorVal l.records 7 i (by omega)
  have column (j : Fin 7) : readings after (base + Fin.ofNat _ j.val).val =
      (record d (readings m) r)[j.val]'j.isLt := by
    have h := l.contains_record hi j.isLt
    have inside : l.contains .records (l.records+i*7+j.val) := by
      convert h using 1; omega
    rw [addFieldVal _ _ (by have := j.isLt; omega),bv,
      image.outside _ (al.separate .records .widths _ (by decide) inside)
        (al.separate .records .ordinals _ (by decide) inside)
        (al.separate .records .offsets _ (by decide) inside)
        (al.separate .records .used _ (by decide) inside),recorded]
  refine ⟨?_,column 1,column 2,column 3,column 4,column 5,column 6⟩
  change readings after base.val = 1
  simpa [record] using column 0

end RoutingISA.Transmission.DataWriter

end BorderVNP
end Computability
end OAI
