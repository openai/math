import OAI.ThreeFlat.Diagonal.TraceBucketImage
import OAI.ThreeFlat.Diagonal.TraceBucketCompare
import OAI.ThreeFlat.RAM.TraceBucketEndArgs

namespace OAI
/-! # The compulsory zero checks of the rectangular initial private-bit bank -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM LaneCursor LaneCursor.RowLayout TraceSourceOwner RAM RAM.TraceBucketAtom
open scoped Classical
variable {F : Type*} [Fintype F] [CommRing F] {w p S f q low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+((q+1)+low))) (L : Lane (q+1)) (copies records dictionary masks ids : ℕ)
set_option quotPrecheck false
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k d
local notation "D" => shape w p r k S f d (G).internal
local notation "B" => bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies records dictionary masks ids
local notation "I" => bitIndex hF hw hp base st hs hf r k fit L
local notation "A" => bitAddress hF hw hp base st hs hf r k fit L I

theorem hole_record (j : Fin (2^low*(D).stride)) (field : Fin 4) :
    let v := holeInputs B (finFunctionFinEquiv L).val ((B).relays+(B).gates+(B).tags+j.val) field.val
    (if v 0<3 then 2+v 1+v 2+v 3 else if v 4=0 then v 5 else v 6)=(I).holeRow (r:=copies) A tableId j field := by
  intro v
  have pin := (bucketCounts hF hw hp base st hs hf r k fit L copies records dictionary masks ids).2.2.2
  have occupancy := bitAddress_get_none hF hw hp base st hs hf r k fit L I j
  have h := (I).hole_word (r:=copies) A tableId j field
  rw [←h]
  change (if field.val<3 then 2+(B).pinCount (finFunctionFinEquiv L).val+((B).bank+(B).bank)+
      ((B).relays+(B).gates+(B).tags+j.val-((B).relays+(B).gates+(B).tags)) else _) = _
  rw [Nat.add_sub_cancel_left,pin]
  by_cases leg : field.val<3
  · simp [leg,BucketIndex.ports]
   ; rfl
  · simp only [leg,ite_false]
    change (if (decodeLane D low (finFunctionFinEquiv L).val
      ((B).relays+(B).gates+(B).tags+j.val-((B).relays+(B).gates+(B).tags))).isSome.toNat=0 then _ else _)=_
    rw [Nat.add_sub_cancel_left]
    cases hc : decodeLane D low (finFunctionFinEquiv L).val j.val with
    | none =>
      have vacant:=(occupancy.mpr hc)
      rw [vacant]; rfl
    | some x =>
      have used : (A).get j≠none := by
        intro vacant
        have impossible : some x=(none : Option ℕ) := hc.symm.trans (occupancy.mp vacant)
        cases impossible
      cases ha : (A).get j with
      | none => exact (used ha).elim
      | some y => rfl

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
