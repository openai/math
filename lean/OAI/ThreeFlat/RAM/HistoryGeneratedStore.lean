import OAI.ThreeFlat.RAM.HistoryCompiledRows
import OAI.ThreeFlat.Diagonal.HistoryPostorder

namespace OAI
/-! # Output memory of a postorder descriptor copy -/

namespace ThreeFlat.RAM.HistoryCompiledRows

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.HistoryContraction HistoryJoinScan BitNetwork.Ordered BitLayout
open scoped BigOperators Classical Fin.CommRing

variable {F : Type*} {n p h w : ℕ} {arity : Fin n → ℕ}
    (N : ∀ i, BitNetwork F (arity i)) (wire : ∀ i, Fin (arity i) → BitSource h p)
    (tag : ((Fin 3 → Bool) → F) → ℕ)

/-- A four-word memory record property, portable across all intermediate
child outputs. A coefficient table is unnecessary for copying the tag. -/
def Records {p w : ℕ} (A : BitNetwork F p) (start : ℕ) (mem : Memory w) :=
  ∀ i : Fin A.cells, ∀ j : Fin 4, mem (start + (4*i.val+j.val)) = (metadata tag A i j : Word w)

/-- One output copy has the exact four post-resolution words of the parent
on its assigned contiguous child interval. -/
theorem segment_record (head : Header ℕ) (m : Memory w) (i : Fin n) (row : Fin (N i).cells) (j : Fin 4)
    (table : ℕ → ℕ) (map_ok : ∀ z, table z.val = sourceAddress (BitNetwork.Ordered.resolve N wire i (.pin z)))
    (fields : head.oldPins = arity i ∧ head.newPins = p ∧ head.offset = h+∑ z : Fin i.val, (N (Fin.castLE i.isLt.le z)).internal)
    (wide : 4<2^w) (srcRange : head.source+4*(N i).cells ≤ 2^w) (pinRange : head.pins+head.oldPins ≤ 2^w)
    (oldRange : 2+head.oldPins < 2^w) (small : metadata tag (N i) row j < 2^w)
    (childRows : Records tag (N i) head.source m)
    (pinData : ∀ t, t < head.oldPins → m (head.pins+t) = (table t : Word w)) :
    (fillSegment head.dest (4*(N i).cells) (fun a => readWord head.words m (Fin.ofNat _ a)) m)
      (head.dest+(4*row.val+j.val)) = (metadata tag (BitNetwork.Ordered.glue N wire) (finSigmaFinEquiv ⟨i,row⟩) j : Word w) := by
  have range : 4*row.val+j.val < 4*(N i).cells := by have := row.isLt; have := j.isLt; omega
  simp only [fillSegment,ite_eq_left (show head.dest ≤ head.dest+(4*row.val+j.val) ∧ head.dest+(4*row.val+j.val)<head.dest+4*(N i).cells by omega)]
  let raw := metadata tag (N i) row j
  have eq := at_record head m row.val j raw table wide (by omega) (by omega) small (old_fit:=oldRange)
    (childRows row j) (fun _ e => by omega) (fun a e => pinData (raw-2) (by omega))
  change readWord head.words m ((head.dest+(4*row.val+j.val) : ℕ) : Word w) = _
  rw [eq]
  by_cases input : j.val < 3
  · rw [ite_eq_left input]
    simp only [raw,metadata,dite_eq_left input,fields.1,fields.2.1,fields.2.2,
      translate_source N wire i table map_ok,source_at]; rfl
  · simp only [raw,metadata,dite_eq_right input,ite_eq_right input,table_at]

/-- Reassemble every chronological copy interval into the one contiguous
parent array. The dependent ordinal enumerates precisely the child's rows. -/
theorem records_of_intervals (base : ℕ) (m : Memory w)
    (rows : ∀ (i : Fin n) (row : Fin (N i).cells) (j : Fin 4),
      m (base+4*Tree.before (fun t => (N t).cells) i+(4*row.val+j.val))=
        (metadata tag (glue N wire) (finSigmaFinEquiv ⟨i,row⟩) j:Word w)) :
    Records tag (glue N wire) base m := by
  intro key j
  obtain ⟨r,hr⟩ := (finSigmaFinEquiv : Row N ≃ Fin (∑ t, (N t).cells)).surjective key
  rcases r with ⟨i,row⟩
  subst key
  rw [row_offset]
  simpa [Tree.before,Nat.mul_add,Nat.add_assoc] using rows i row j

/-- The compiled row invariant plus the one immutable field table is exactly
the compact memory input of the weighted interpreter. -/
theorem stores_of_records [Fintype F] (A : BitNetwork F p) (code : FieldCode F w) (start lut : ℕ) (m : Memory w)
    (rows : Records (fun t : (Fin 3 → Bool) → F => (Fintype.equivFin _ t).val) A start m)
    (tables : ∀ (i : Fin (library A).count) (j : Fin 8), m (lut+8*i.val+j.val) =
      code.encode ((library A).table i (bits j.val))) : HistoryFactors.Stores A (library A) code start lut m where
  source i j := by
    have ok := rows i (j.castLE (by decide : 3≤4))
    simpa [metadata,j.isLt,Nat.add_assoc] using ok
  tag i := by simpa [metadata,library,Nat.add_assoc] using rows i 3
  coefficient := tables

end ThreeFlat.RAM.HistoryCompiledRows

end OAI
