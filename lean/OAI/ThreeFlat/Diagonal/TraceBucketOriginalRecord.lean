import OAI.ThreeFlat.Diagonal.TraceBucketImage
import OAI.ThreeFlat.Diagonal.TraceBucketOriginal
import OAI.ThreeFlat.Diagonal.TraceBucketDigits
import OAI.ThreeFlat.RAM.TraceBucketOriginalArgs

namespace OAI
/-! # The original trace-cell substream of a numeric initial history atom -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM LaneCursor LaneCursor.RowLayout TraceSourceOwner RAM RAM.TraceBucketAtom
open RAM.BitLayout
open scoped Classical
variable {F : Type*} [Fintype F] [CommRing F] {w p S f q low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+((q+1)+low))) (L : Lane (q+1)) (copies records dictionary masks ids : ℕ)
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k d
local notation "B" => bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies records dictionary masks ids
local notation "N" => network hF hw hp base st hs hf r k d
local notation "P" => layout hF hw hp base st hs hf r k fit
local notation "R" => rectangular hF hw hp base st hs hf r k fit
local notation "I" => bitIndex hF hw hp base st hs hf r k fit L

/-- From the immutable eleven-word cell image, common slot IDs, and sparse
inverse mask dictionary, the generated original row agrees with the
local network's remapped incoming trivalent gate. -/
theorem original_record (m : ℕ→ℕ)
    (values : ∀ (row : Row (q+1) low) (slot : Fin (G).cells) (j : Fin 3),
      m ((B).readAt row.val slot.val j.val)=sourceAddress ((N).source ((R).cell row slot) j))
    (labels : ∀ (j : Fin (G).cells), m (ids+j.val) = ((HistoryCompiledRows.library G).id j).val)
    (dict : ∀ a : Occurrence N, m (dictionary+((P).offset ((P).code a)).val)=((P).code a).val)
    (i : Fin (I).c) (j : Fin 4) :
    TraceBucketFields.originalNat m (originalInputs B m (finFunctionFinEquiv L).val ((B).relays+i.val) j.val) =
      (I).original (r:=copies) tableId i j := by
  have siteBound := (bucketCounts hF hw hp base st hs hf r k fit L copies records dictionary masks ids).2.2.2
  let gate := ((I).cell i).val
  let row := ((P).cellAddress gate).1
  let slot := ((P).cellAddress gate).2
  have actual : (R).cell row slot=gate := (P).cellAddress.injective ((R).at_cell _ _)
  have ord := (P).laneCell_digits R L i
  change row.val=(finFunctionFinEquiv L).val*2^low+i.val/(G).cells ∧ slot.val=i.val%(G).cells at ord
  have table (a : Fin (N).cells) : m (ids+((P).cellAddress a).2.val)=tableId ((N).table a) := by
    have hcell : (R).cell ((P).cellAddress a).1 ((P).cellAddress a).2=a :=
      (P).cellAddress.injective ((R).at_cell _ _)
    rw [labels]
    change tableId ((G).table ((P).cellAddress a).2) = tableId ((N).table a)
    exact congrArg tableId ((rectangular_table hF hw hp base st hs hf r k fit
      ((P).cellAddress a).1 ((P).cellAddress a).2).symm.trans (congrArg (N).table hcell))
  rw [←(I).original_word tableId m dictionary ids dict table (fun _ => rfl) i j]
  by_cases read : j.val<3
  · let leg : Fin 3 := ⟨j.val,read⟩
    have src := values row slot leg
    rw [actual] at src
    have owner := bitSource hF hw hp base st hs hf r k fit row ((N).source gate leg)
    change (sourceRow (P).hiddenRow (P).pinRow row ((N).source gate leg)).val =
      ownerAt (B).shape 1 row.val (sourceAddress ((N).source gate leg)) at owner
    have power : ((q+1)+low)-1=low+q := by omega
    have vec : originalInputs B m (finFunctionFinEquiv L).val ((B).relays+i.val) j.val =
        (I).checkedArgs (r:=copies) i j dictionary ids := by
      unfold originalInputs BucketIndex.checkedArgs
      simp only [Nat.add_sub_cancel_left,read,dite_true]
      change ![j.val,m ((B).readAt ((finFunctionFinEquiv L).val*2^low+i.val/(G).cells) (i.val%(G).cells) j.val),
        ownerAt (B).shape 1 ((finFunctionFinEquiv L).val*2^low+i.val/(G).cells)
          (m ((B).readAt ((finFunctionFinEquiv L).val*2^low+i.val/(G).cells) (i.val%(G).cells) j.val)),
        (finFunctionFinEquiv L).val*2^low+i.val/(G).cells,(G).cells,i.val%(G).cells,2^low,
        (B).pinCount (finFunctionFinEquiv L).val,(I).t,BucketIndex.bank copies (I).t,2^(d-1),dictionary,ids]=_
      rw [←ord.1,←ord.2,src,siteBound,←owner,power]
    rw [vec]
  · simp only [TraceBucketFields.originalNat,originalInputs,BucketIndex.checkedArgs,
      read,dite_false,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
      Nat.add_sub_cancel_left]
    change m (ids+i.val%(G).cells)=m (ids+slot.val)
    rw [ord.2]

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
