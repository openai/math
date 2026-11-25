import OAI.ThreeFlat.Diagonal.TraceBucketImage
import OAI.ThreeFlat.Diagonal.TraceBucketDigits
import OAI.ThreeFlat.RAM.TraceBucketComparisonArgs

namespace OAI
/-! # The numeric reverse candidate in the actual paired-bit trace array -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM LaneCursor LaneCursor.RowLayout TraceSourceOwner RAM RAM.TraceBucketAtom
open RAM.BitLayout
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

/-- Each register produced by mixed-radix tag decoding reads the original
11-word row of the unique potential recipient. No assumptions about that
recipient being live or located at the requested owner are needed. -/
theorem candidate_actual (m : ℕ→ℕ)
    (values : ∀ (row : Row (q+1) low) (slot : Fin (G).cells) (j : Fin 3),
      m ((B).readAt row.val slot.val j.val)=sourceAddress ((N).source ((R).cell row slot) j))
    (offsets : ∀ i, m (masks+i.val)=((P).offset i).val) (t : Fin (I).t) :
    let u := (I).tag t
    let own := (splitRow _ _).symm (L,u.2.1)
    let dx := ((P).offset u.1).val
    let recv := partner own ((P).offset u.1)
    let s := (N).source ((R).cell recv u.2.2.1) u.2.2.2
    let x := sourceAddress s
    let h := (sourceRow (P).hiddenRow (P).pinRow recv s).val
    candidate B m (finFunctionFinEquiv L).val ((B).relays+(B).gates+t.val) =
      ⟨t.val,u.1.val,u.2.1.val,u.2.2.1.val,u.2.2.2.val,own.val,dx,recv.val,x,h,
        laneHiddenSlot (B).shape low (x-(2+S))⟩ := by
  intro u own dx recv s x home
  have idx : ((tagOrder _ low (G).cells).symm u).val=t.val :=
    congrArg Fin.val ((I).tag.symm_apply_apply _)
  obtain ⟨off,lo,slot,leg⟩ := tag_digits u
  rw [idx] at off lo slot leg
  have joined : own.val=(finFunctionFinEquiv L).val*2^low+u.2.1.val := joinedRow L u.2.1
  have flip : recv.val=own.val ^^^ dx := rfl
  have src := values recv u.2.2.1 u.2.2.2
  change m ((B).readAt recv.val u.2.2.1.val u.2.2.2.val)=x at src
  have oh := bitSource hF hw hp base st hs hf r k fit recv s
  unfold candidate
  simp only [Nat.add_sub_cancel_left]
  change Candidate.mk t.val (t.val/(2^low*((G).cells*3))) ((t.val/((G).cells*3))%2^low)
    ((t.val/3)%(G).cells) (t.val%3) _ _ _ _ _ _=_
  have lowRows : (B).lowRows = 2^low := rfl
  have slots : (B).slots = (G).cells := rfl
  have stride : (B).per = 2^low*((G).cells*3) := rfl
  have maskBase : (B).masks = masks := rfl
  have header : (B).shape.header = S := rfl
  have maskRead : m (masks+u.1.val) = dx := offsets u.1
  change home = ownerAt (B).shape 1 recv.val x at oh
  simp only [lowRows,slots,stride,maskBase,off,lo,slot,leg,maskRead,←joined,
    ←flip,src,←oh,header,laneHiddenSlot]

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
