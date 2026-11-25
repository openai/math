import OAI.ThreeFlat.Diagonal.TraceBitHeaderOffsets
import OAI.ThreeFlat.Diagonal.TraceBucketCandidate
import OAI.ThreeFlat.Diagonal.TraceBucketCompare
import OAI.ThreeFlat.Diagonal.TraceBucketMasks

namespace OAI
/-! # The physical emitted-variable test in each initial comparison row -/

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
local notation "P₀" => rawLayout hF hw hp base st hs hf r k fit
local notation "P" => layout hF hw hp base st hs hf r k fit
local notation "R₀" => rawRectangular hF hw hp base st hs hf r k fit
local notation "R" => rectangular hF hw hp base st hs hf r k fit
local notation "N" => network hF hw hp base st hs hf r k d
local notation "I" => bitIndex hF hw hp base st hs hf r k fit L
local notation "A" => bitAddress hF hw hp base st hs hf r k fit L I

theorem comparison_record (m : ℕ→ℕ)
    (values : ∀ (row : Row (q+1) low) (slot : Fin (G).cells) (j : Fin 3),
      m ((B).readAt row.val slot.val j.val)=sourceAddress ((N).source ((R).cell row slot) j))
    (offsets : ∀ i, m (masks+i.val)=((P).offset i).val) (t : Fin (I).t) (j : Fin 4) :
    TraceBucketFields.compareNat (cmpInputs B m (finFunctionFinEquiv L).val ((B).relays+(B).gates+t.val) j.val) =
      (I).compareRow (r:=copies) A tableId t j := by
  let ln := (finFunctionFinEquiv L).val
  let first := ln*pinSpan 1 low
  have pins (j : Fin S) (own : (splitRow _ _ ((P₀).pinRow j)).1=L) :
      ((I).ext.symm ⟨j,own⟩).val=j.val-first ∧ first≤j.val := by
    refine ⟨bitExt_symm_val hF hw hp base st hs hf r k fit L ⟨j,own⟩,?_⟩
    have he := (bitPin_lane hF hw hp base st hs hf r k fit L j).mp own
    have hn := Nat.div_mul_le_self j.val (pinSpan 1 low)
    rw [he] at hn
    exact hn
  have hidden (j : Fin (N).internal) (own : (splitRow _ _ ((P₀).hiddenRow j)).1=L) :
      ((A).put ((I).hidden.symm ⟨j,own⟩)).val=laneHiddenSlot (B).shape low j.val := by
    rw [bitAddress_put,(I).hidden.apply_symm_apply]
    change laneHiddenSlot (B).shape low j.val = laneHiddenSlot (B).shape low j.val
    rfl
  have hmask (i) : firstMask (P₀).offset i=decide (i.val≠d+1) := by
    rw [rawLayout_offset]; exact TracePhysical.firstMask_eq _ _ i
  have eqn := (I).compare_word (r:=copies) R₀ A tableId first (laneHiddenSlot (B).shape low) pins hidden hmask t j
  have cnd := candidate_actual hF hw hp base st hs hf r k fit L copies records dictionary masks ids m values offsets t
  have pin := (bucketCounts hF hw hp base st hs hf r k fit L copies records dictionary masks ids).2.2.2
  have start : (B).pinLow (finFunctionFinEquiv L).val=first := by
    change ln*2^low*2=ln*((1*2)*2^low)
    ring
  unfold cmpInputs
  rw [cnd]
  simp only []
  rw [pin,start]
  exact eqn

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
