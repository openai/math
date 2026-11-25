import OAI.ThreeFlat.Diagonal.TraceBucketComparisonRecord
import OAI.ThreeFlat.Diagonal.TraceBucketOriginalRecord
import OAI.ThreeFlat.Diagonal.TraceBucketHoleRecord
import OAI.ThreeFlat.Diagonal.TraceBucketRelayCorrect
import OAI.ThreeFlat.RAM.TraceBucketAtomValue
import OAI.ThreeFlat.RAM.TraceBucketPublicROM
import OAI.ThreeFlat.Diagonal.TraceBitHeaderOffsets

namespace OAI
/-! # Literal-free compiler for the first and every later physical history atom -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM LaneCursor LaneCursor.RowLayout TraceSourceOwner RAM RAM.TraceBucketAtom
open RAM.BitLayout
open scoped Classical Fin.CommRing
variable {F : Type*} [Fintype F] [CommRing F] {w p S f q low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+((q+1)+low))) (L : Lane (q+1)) (copies records dictBase masks ids : ℕ)
set_option quotPrecheck false
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k d
local notation "B" => bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies records dictBase masks ids
local notation "P" => layout hF hw hp base st hs hf r k fit
local notation "R" => rectangular hF hw hp base st hs hf r k fit
local notation "N" => network hF hw hp base st hs hf r k d
local notation "I" => bitIndex hF hw hp base st hs hf r k fit L
local notation "A" => bitAddress hF hw hp base st hs hf r k fit L I
local notation "L0" => (I).firstNetwork (r:=copies) A 0
local notation "ln" => (finFunctionFinEquiv L).val

private theorem maskValues (i) : ((P).offset i).val=TracePhysical.maskNat d i.val := by
  rw [layout_offset]; exact TracePhysical.offset_nat _ _

set_option maxHeartbeats 800000 in
theorem relay_record (stage : Fin (q+1)) (i : Fin (B).relays) (j : Fin 4) :
    TraceBucketRelay.values ((B).relayInputs ln i.val j.val stage.val) =
      TraceBucketRelay.metadata (if stage.val=0 then (I).x else 0) (tableId (F:=F))
        (RelayNetwork.network (r:=copies) (I).tag (P).mask stage) i j := by
  have pins := (bucketCounts hF hw hp base st hs hf r k fit L copies records dictBase masks ids).2.2.2
  unfold Layout.relayInputs
  rw [pins]
  exact TraceBucketRelay.values_metadata (r:=copies) (I).tag (P).mask stage (B).per d low
    (if stage.val=0 then (I).x else 0) (tableId (F:=F))
    (TraceBucketRelay.selected_slot (r:=copies) P (maskValues hF hw hp base st hs hf r k fit)) i j

/-- The native formula for a relay-stage record contains only the selected
slot comparisons. External prefix and all private variables occur at stage zero. -/
theorem later_record (m : ℕ→ℕ) (stage : Fin (q+1)) (later : stage.val≠0) (i : Fin (B).relays) (j : Fin 4) :
    atomNat B m ln i.val j.val stage.val =
      HistoryCompiledRows.metadata (tableId (F:=F)) (RelayNetwork.network (r:=copies) (I).tag (P).mask stage) i j := by
  rw [atomNat,ite_eq_left i.isLt,relay_record hF hw hp base st hs hf r k fit L copies records dictBase masks ids]
  simp only [later,ite_false]
  exact TraceBucketRelay.metadata_zero (tableId (F:=F))
    (RelayNetwork.network (F:=F) (r:=copies) (I).tag (P).mask stage) i j

theorem first_record (m : ℕ→ℕ)
    (values : ∀ (row : Row (q+1) low) (slot : Fin (G).cells) (j : Fin 3),
      m ((B).readAt row.val slot.val j.val)=sourceAddress ((N).source ((R).cell row slot) j))
    (labels : ∀ (j : Fin (G).cells), m (ids+j.val) = ((HistoryCompiledRows.library G).id j).val)
    (dict : ∀ a : Occurrence N, m (dictBase+((P).offset ((P).code a)).val)=((P).code a).val)
    (offsets : ∀ i, m (masks+i.val)=((P).offset i).val)
    (i : Fin (L0).cells) (j : Fin 4) :
    atomNat B m ln i.val j.val 0 = HistoryCompiledRows.metadata tableId L0 i j := by
  have gates : (B).gates=(I).c := rfl
  have tags : (B).tags=(I).t := rfl
  refine Fin.addCases (fun a => ?_) (fun rest => ?_) i
  · change atomNat B m ln a.val j.val 0 = _
    have inside : a.val < (B).relays := a.isLt
    rw [atomNat,ite_eq_left inside]
    apply Eq.trans (relay_record hF hw hp base st hs hf r k fit L copies records dictBase masks ids
      (0 : Fin (q+1)) a j)
    exact (TraceBucketRelay.mounted_metadata
      (RelayNetwork.network (F:=F) (r:=copies) (I).tag (P).mask 0) rfl
      (I).network A (I).attach (tableId (F:=F)) a j).symm
  · refine Fin.addCases (fun cells => ?_) (fun q => ?_) rest
    · refine Fin.addCases (fun g => ?_) (fun t => ?_) cells
      · refine Eq.trans ?_ ((I).metadata_original (r:=copies) A tableId g j).symm
        change atomNat B m ln ((B).relays+g.val) j.val 0=(I).original (r:=copies) tableId g j
        have gfit : g.val<(B).gates := g.isLt
        have outside : ¬(B).relays+g.val<(B).relays := by omega
        have inner : (B).relays+g.val<(B).relays+(B).gates := by omega
        simp only [atomNat,ite_eq_right outside,ite_eq_left inner]
        exact original_record hF hw hp base st hs hf r k fit L copies records dictBase masks ids m values labels dict g j
      · refine Eq.trans ?_ ((I).metadata_compare (r:=copies) A tableId t j).symm
        change atomNat B m ln ((B).relays+((B).gates+t.val)) j.val 0=(I).compareRow (r:=copies) A tableId t j
        rw [←Nat.add_assoc]
        have tfit : t.val<(B).tags := t.isLt
        have outer : ¬(B).relays+(B).gates+t.val<(B).relays := by omega
        have middle : ¬(B).relays+(B).gates+t.val<(B).relays+(B).gates := by omega
        have inner : (B).relays+(B).gates+t.val<(B).relays+(B).gates+(B).tags := by omega
        simp only [atomNat,ite_eq_right outer,ite_eq_right middle,ite_eq_left inner]
        exact comparison_record hF hw hp base st hs hf r k fit L copies records dictBase masks ids m values offsets t j
    · refine Eq.trans ?_ ((I).metadata_hole (r:=copies) A tableId q j).symm
      let row := (B).relays+(B).gates+(B).tags+q.val
      change atomNat B m ln ((B).relays+((B).gates+(B).tags+q.val)) j.val 0=_
      have address : (B).relays+((B).gates+(B).tags+q.val)=row:=by dsimp [row]; omega
      have afterRelay : ¬row < (B).relays:=by dsimp [row]; omega
      have afterGate : ¬row < (B).relays+(B).gates:=by dsimp [row]; omega
      have afterTag : ¬row < (B).relays+(B).gates+(B).tags:=by dsimp [row]; omega
      rw [address]
      simpa only [atomNat,ite_eq_right afterRelay,ite_eq_right afterGate,ite_eq_right afterTag]
        using hole_record hF hw hp base st hs hf r k fit L copies records dictBase masks ids q j

theorem public_first {W : ℕ} (m : Memory W) (original : Fin 1→Word W) (v : Fin 4→Word W)
    (cap : ℕ) (fits : Widths B v m cap)
    (values : ∀ (row : Row (q+1) low) (slot : Fin (G).cells) (e : Fin 3),
      (m ((B).readAt row.val slot.val e.val)).val=sourceAddress ((N).source ((R).cell row slot) e))
    (labels : ∀ j : Fin (G).cells, (m (ids+j.val)).val = ((HistoryCompiledRows.library G).id j).val)
    (dict : ∀ a : Occurrence N, (m (dictBase+((P).offset ((P).code a)).val)).val=((P).code a).val)
    (offsets : ∀ i, (m (masks+i.val)).val=((P).offset i).val)
    (i : Fin (L0).cells) (j : Fin 4)
    (row : (v 0).val=i.val) (field : (v 1).val=j.val) (lane : (v 2).val=ln) (stage : (v 3).val=0) :
    (publicProgram W).eval (publicData B original) m v=(HistoryCompiledRows.metadata tableId L0 i j : Word W) := by
  rw [publicProgram_eval,program_value B v original m cap fits,row,field,lane,stage]
  rw [first_record hF hw hp base st hs hf r k fit L copies records dictBase masks ids _ values labels dict offsets]

theorem public_later {W : ℕ} (m : Memory W) (original : Fin 1→Word W) (v : Fin 4→Word W)
    (cap : ℕ) (fits : Widths B v m cap) (stage : Fin (q+1)) (later : stage.val≠0)
    (i : Fin (B).relays) (j : Fin 4)
    (row : (v 0).val=i.val) (field : (v 1).val=j.val) (lane : (v 2).val=ln) (atStage : (v 3).val=stage.val) :
    (publicProgram W).eval (publicData B original) m v=
      (HistoryCompiledRows.metadata (tableId (F:=F)) (RelayNetwork.network (r:=copies) (I).tag (P).mask stage) i j : Word W) := by
  rw [publicProgram_eval,program_value B v original m cap fits,row,field,lane,atStage]
  rw [later_record hF hw hp base st hs hf r k fit L copies records dictBase masks ids _ stage later]


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
