import OAI.ThreeFlat.Diagonal.TraceSeedImage
import OAI.ThreeFlat.Diagonal.TraceBucketReady

namespace OAI
/-! # Native seeding supplies the actual first-leaf operand image and capacity -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM RAM RAM.TraceBucketAtom LaneCursor LaneCursor.RowLayout
open scoped Fin.CommRing
variable {F : Type*} [Fintype F] [CommRing F] {w W b p S f q low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3≤w+1) (hp : p≤2^(w+1))
    (base : ℕ) (st : Word w) (hs : S≤2^w) (hf : f≤2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+((q+1)+low))) (copies raw dict masks ids : ℕ)

theorem seeded_capacity (field : Fintype.card F≤2^W) (m : Memory W)
    (room : SeedRoom (TraceStaticRow.gateTable hF hw hp base f st r k ((q+1)+low)).cells
      (1+(((q+1)+low)+((q+1)+low))) (2^(q+1)*2^low) ids masks dict W)
    (size : (bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies raw dict masks ids).footprint<2^b)
    (words : 5*b+128≤W)
    (recordEnd : let bucket := bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies raw dict masks ids
      let gates := TraceStaticRow.gateTable hF hw hp base f st r k ((q+1)+low)
      raw+11*(bucket.shape.rows*gates.cells)+4≤2^W)
    (coeff : Fintype.card F≤2+S+
      (bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies raw dict masks ids).shape.count)
    (seeded : Banks hF hw hp base st hs hf r k fit ids masks dict m)
    (records : RawTickBuilder.loaded (network hF hw hp base st hs hf r k ((q+1)+low))
      (FieldCode.ofCardLe field) raw m) :
    ImageCapacity (bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies raw dict masks ids) m b := by
  apply capacity_of_records hF hw hp base st hs hf r k fit copies raw dict masks ids field m size words
    recordEnd _ _ _ coeff _ seeded.2.2
  · change dict+2^((q+1)+low)≤2^W
    simpa [pow_add] using room.wordEnd
  · change masks+(1+2*((q+1)+low))≤2^W
    have a := room.maskEnd
    have b := room.wordEnd
    omega
  · change ids+(TraceStaticRow.gateTable hF hw hp base f st r k ((q+1)+low)).cells≤2^W
    have a := room.labelEnd
    have b := room.maskEnd
    have c := room.wordEnd
    omega
  · exact ready_four hF hw hp base st hs hf r k fit copies raw dict masks ids (FieldCode.ofCardLe field) m records


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
