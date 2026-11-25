import OAI.ThreeFlat.RAM.TraceBucketCapacityFits
import OAI.ThreeFlat.Diagonal.TraceBucketAtomCorrect
import OAI.ThreeFlat.Diagonal.TraceBucketRomFits
import OAI.ThreeFlat.RAM.RawTickBuilder

namespace OAI
/-! # A physically loaded trace drives the fixed native initial-atom program -/

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

theorem ready_four {W : ℕ} (code : FieldCode F W) (m : Memory W) (load : RawTickBuilder.loaded N code records m)
    (row : Row (q+1) low) (slot : Fin (G).cells) (j : Fin 4) :
    m ((B).readAt row.val slot.val j.val)=BitLayout.record N code ((R).cell row slot) (j.castLE (by decide)) := by
  have h := load ((R).cell row slot) (j.castLE (by decide))
  rwa [rectangular_cell_val] at h

private theorem lane_fit : (ln+1)*(B).lowRows≤(B).shape.rows := by
  change (ln+1)*2^low≤2^((q+1)+low)
  exact (Nat.mul_le_mul_right (2^low) (finFunctionFinEquiv L).isLt).trans_eq
    (pow_add 2 (q+1) low).symm

theorem ready_first {W b : ℕ} (code : FieldCode F W) (m : Memory W)
    (budget : ImageCapacity B m b) (load : RawTickBuilder.loaded N code records m)
    (labels : ∀ j : Fin (G).cells, (m (ids+j.val)).val = ((HistoryCompiledRows.library G).id j).val)
    (dict : ∀ a : Occurrence N, (m (dictBase+((P).offset ((P).code a)).val)).val=((P).code a).val)
    (offsets : ∀ i, (m (masks+i.val)).val=((P).offset i).val)
    (rest : Fin 1→Word W) (v : Fin 4→Word W) (i : Fin (L0).cells) (j : Fin 4)
    (row : (v 0).val=i.val) (field : (v 1).val=j.val) (lane : (v 2).val=ln) (stage : (v 3).val=0) :
    (publicProgram W).eval (publicData B rest) m v=(HistoryCompiledRows.metadata tableId L0 i j : Word W) := by
  have sizeB := budget.size.trans_le budget.two_power
  unfold Layout.footprint at sizeB
  have hidden : (N).internal=(B).shape.count := hidden_count hF hw hp base st hs hf r k
  apply public_first hF hw hp base st hs hf r k fit L copies records dictBase masks ids m rest v b ?_ ?_ labels dict offsets i j row field lane stage
  · apply budget.widths (by rw [lane]; exact lane_fit hF hw hp base st r k L copies records dictBase masks ids)
      (by rw [field]; exact j.isLt) (by rw [stage]; omega)
    rw [row]
    have bound := i.isLt
    change i.val<(B).relays+(((B).gates+(B).tags)+(B).lowRows*(B).shape.stride) at bound
    omega
  · intro site slot leg
    have h := load ((R).cell site slot) (leg.castLE (by decide))
    rw [rectangular_cell_val] at h
    change m ((B).readAt site.val slot.val leg.val)=_ at h
    rw [h]
    simp only [BitLayout.record,Fin.val_castLE,leg.isLt,dite_true]
    have src := record_le_source ((N).source ((R).cell site slot) leg)
    have bound : 2+S+(N).internal < 2^W := by
      rw [hidden]
      change 2+(B).shape.header+(B).shape.count < 2^W
      omega
    exact Nat.mod_eq_of_lt (src.trans bound)

theorem ready_later {W b : ℕ} (m : Memory W) (budget : ImageCapacity B m b)
    (rest : Fin 1→Word W) (v : Fin 4→Word W) (stage : Fin (q+1)) (later : stage.val≠0)
    (i : Fin (B).relays) (j : Fin 4) (row : (v 0).val=i.val) (field : (v 1).val=j.val)
    (lane : (v 2).val=ln) (atStage : (v 3).val=stage.val) :
    (publicProgram W).eval (publicData B rest) m v=
      (HistoryCompiledRows.metadata (tableId (F:=F)) (RelayNetwork.network (r:=copies) (I).tag (P).mask stage) i j : Word W) := by
  apply public_later hF hw hp base st hs hf r k fit L copies records dictBase masks ids m rest v b ?_ stage later i j row field lane atStage
  apply budget.widths (by rw [lane]; exact lane_fit hF hw hp base st r k L copies records dictBase masks ids)
    (by rw [field]; exact j.isLt) (by rw [atStage]; change stage.val≤(q+1)+low; omega)
    (by rw [row]; have := i.isLt; omega)


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
