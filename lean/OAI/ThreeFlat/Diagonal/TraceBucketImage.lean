import OAI.ThreeFlat.Diagonal.TraceBitSourceOwner
import OAI.ThreeFlat.Diagonal.TraceBucketLUT
import OAI.ThreeFlat.Diagonal.TraceBucketInitial
import OAI.ThreeFlat.RAM.TraceBucketOperands

namespace OAI
/-! # Specialization of the native original-atom descriptor to the paired trace -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM LaneCursor LaneCursor.RowLayout TraceSourceOwner RAM RAM.TraceBucketAtom
variable {F : Type*} [Fintype F] [CommRing F] {w p S f q low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ)

noncomputable def tableId (g : (Fin 3→Bool)→F) : ℕ := (Fintype.equivFin _ g).val

/-- All coefficients from original trace cells use the same fixed finite
field library as the constant tests and the recursive join interpreter. -/
noncomputable def bucketShape (copies records dictionary masks ids : ℕ) : Layout :=
  let depth := (q+1)+low
  let gate := TraceStaticRow.gateTable hF hw hp base f st r k depth
  ⟨shape w p r k S f depth gate.internal,low,depth,gate.cells,copies,records,dictionary,masks,ids,
    tableId (fun z => if z 0=z 1 then (1:F) else 0),
    tableId (fun z => if z 0=true then (0:F) else 1),tableId (fun _ => (1:F))⟩

variable (fit : S+f≤2^(1+((q+1)+low))) (L : Lane (q+1)) (copies records dictionary masks ids : ℕ)
theorem bucketCounts :
    let shape₀ := bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies records dictionary masks ids
    let index := bitIndex (q:=q) (low:=low) hF hw hp base st hs hf r k fit L
    shape₀.gates=index.c ∧ shape₀.tags=index.t ∧ shape₀.bank=BucketIndex.bank copies index.t ∧
      shape₀.pinCount (finFunctionFinEquiv L).val=index.x := by
  intro shape₀ index
  refine ⟨rfl,rfl,?_,?_⟩
  · rfl
  · change min (S-(finFunctionFinEquiv L).val*2^low*2) (2*2^low)=TraceSourceOwner.pinCount S 1 low (finFunctionFinEquiv L).val
    simp [TraceSourceOwner.pinCount,pinSpan,Nat.min_comm,Nat.mul_comm,Nat.mul_assoc]

theorem bucketCellId (row : Row (q+1) low)
    (slot : Fin (TraceStaticRow.gateTable hF hw hp base f st r k ((q+1)+low)).cells) :
    let tiles := rectangular (lane:=q+1) (low:=low) hF hw hp base st hs hf r k fit
    let net := network hF hw hp base st hs hf r k ((q+1)+low)
    let gate := TraceStaticRow.gateTable hF hw hp base f st r k ((q+1)+low)
    tableId (net.table (tiles.cell row slot))=((HistoryCompiledRows.library gate).id slot).val := by
  exact rectangular_id (lane:=q+1) (low:=low) hF hw hp base st hs hf r k fit row slot

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
