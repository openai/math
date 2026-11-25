import OAI.ThreeFlat.Diagonal.TraceBucketImage
import OAI.ThreeFlat.RAM.TraceBucketCapacity

namespace OAI
/-! # A genuine eleven-word trace table establishes the native word bounds -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM LaneCursor LaneCursor.RowLayout TraceSourceOwner RAM RAM.TraceBucketAtom
open RAM.BitLayout
open scoped Classical Fin.CommRing
variable {F : Type*} [Fintype F] [CommRing F] {w p S f q low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+((q+1)+low))) (copies records dictBase masks ids : ℕ)
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k d
local notation "B" => bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies records dictBase masks ids
local notation "P" => layout hF hw hp base st hs hf r k fit
local notation "R" => rectangular hF hw hp base st hs hf r k fit
local notation "N" => network hF hw hp base st hs hf r k d
set_option quotPrecheck false in
local notation "D" => (B).shape

theorem record_le_source {m n : ℕ} (a : BitSource n m) : sourceAddress a<2+m+n := by
  cases a with
  | hidden h => change 2+m+h.val<_; omega
  | pin i => change 2+i.val<_; omega
  | constant b =>
    cases b with
    | false => change 0 < 2+m+n; omega
    | true => change 1 < 2+m+n; omega

theorem capacity_of_records {W b : ℕ} (field : Fintype.card F ≤ 2^W)
    (m : Memory W) (size : (B).footprint<2^b) (word : 5*b+128≤W)
    (recordEnd : (B).records+11*((D).rows*(B).slots)+4≤2^W)
    (dictionaryEnd : (B).dictionary+(D).rows≤2^W) (maskEnd : (B).masks+(1+2*d)≤2^W)
    (tableEnd : (B).tableIds+(B).slots≤2^W)
    (coeff : Fintype.card F≤2+S+(D).count)
    (values : ∀ (row : Row (q+1) low) (slot : Fin (G).cells) (j : Fin 4),
       m ((B).readAt row.val slot.val j.val)=BitLayout.record N (FieldCode.ofCardLe field) ((R).cell row slot) (j.castLE (by decide)))
    (offsets : ∀ i, (m (masks+i.val)).val=((P).offset i).val) : ImageCapacity B m b := by
  have rows : (D).rows=2^d := rfl
  have grid : (D).header+(D).ticks≤2*(D).rows := by change S+f≤2*2^d; simpa [pow_add] using fit
  have rpos : 1<(D).rows := by rw [rows]; apply Nat.one_lt_two_pow; omega
  have stride : 0<(D).stride := by dsimp only [Shape.stride,Shape.track,shape,bucketShape]; positivity
  have dcount : 0<(D).count := by
    have edge : 0<((D).rows-1)*(D).edge := Nat.mul_pos (by omega) (by change 0<7*(w+1); positivity)
    unfold Shape.count; omega
  have ncells : 0<(B).slots := by
    change 0<(G).cells
    unfold TraceStaticRow.gateTable
    rw [TracePacketArray.one_count]
    have q : 0<Fintype.card (TraceUniformRow.Check F w p k) := Fintype.card_pos
    omega
  have count : (N).internal=(D).count := hidden_count hF hw hp base st hs hf r k
  refine ⟨rows,grid,dcount,ncells,stride,size,recordEnd,dictionaryEnd,maskEnd,tableEnd,word,?_,?_⟩
  · intro i hi
    change i<1+2*d at hi
    let z : Fin (1+(d+d)) := ⟨i,by omega⟩
    have capacity : 2^(q+1)*2^low = (D).rows := (pow_add 2 (q+1) low).symm.trans rows.symm
    exact (offsets z).trans_lt (((P).offset z).isLt.trans_eq capacity)
  · intro a i j ha hi hj
    let site : Row (q+1) low := ⟨a,by simpa only [rows,pow_add] using ha⟩
    let slot : Fin (G).cells := ⟨i,hi⟩
    let leg : Fin 4 := ⟨j,hj⟩
    rw [show m ((B).readAt a i j) = _ from values site slot leg]
    unfold BitLayout.record
    split
    · apply (Nat.mod_le _ _).trans_lt
      rw [←count]; exact record_le_source _
    · rw [FieldCode.encode_val_ofCardLe]
      exact ((Fintype.equivFin F) _).isLt.trans_le coeff

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
