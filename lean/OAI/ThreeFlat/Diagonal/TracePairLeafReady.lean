import OAI.ThreeFlat.Diagonal.TracePairLeaf
import OAI.ThreeFlat.Diagonal.TraceBucketReady
import OAI.ThreeFlat.RAM.TraceSuffixValue
import OAI.ThreeFlat.RAM.PhysicalScanLink

namespace OAI
/-! # Native initial records for only the genuinely independent H endpoint bits -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM LaneCursor LaneCursor.RowLayout TraceSourceOwner TraceSuffix
open RAM RAM.TraceBucketAtom RAM.DescriptorExpr
open scoped Classical Fin.CommRing
variable {F : Type*} [Fintype F] [CommRing F] {w p S f q low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3≤w+1) (hp : p≤2^(w+1))
    (base : ℕ) (st : Word w) (hs : S≤2^w) (hf : f≤2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+((q+1)+low))) (L : Lane (q+1)) (copies records dictBase masks ids : ℕ)
set_option quotPrecheck false
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k d
local notation "B" => bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies records dictBase masks ids
local notation "P" => layout hF hw hp base st hs hf r k fit
local notation "N" => network hF hw hp base st hs hf r k d
local notation "I" => bitIndex hF hw hp base st hs hf r k fit L
local notation "A" => bitAddress hF hw hp base st hs hf r k fit L I
local notation "L0" => (I).firstNetwork (r:=copies) A 0
local notation "ln" => (finFunctionFinEquiv L).val

/-- The ordinary fixed decoder and the typed public-suffix reader share a
single parameter bank. Only public three-word dimensions enter the wrapper. -/
def endpointProgram (W : ℕ) {K : ℕ} (bank : Fin (1+bankSize)→Fin K)
    (oracle : Term W K 1) (header «prefix» span : Fin K) : Term W K 4 :=
  TraceSuffixProgram.program ((publicProgram W).mapPublic bank) oracle header «prefix» span

theorem endpointProgram_size (W : ℕ) {K : ℕ} (bank : Fin (1+bankSize)→Fin K)
    (oracle : Term W K 1) (header «prefix» span : Fin K) :
    (endpointProgram W bank oracle header «prefix» span).binds ≤ 1000100+oracle.binds := by
  have z := TraceSuffixProgram.program_size ((publicProgram W).mapPublic bank) oracle header «prefix» span
  rw [Term.binds_mapPublic] at z
  have h := publicProgram_size W
  exact z.trans (by omega)

private theorem lane_end {n bits depth : ℕ} (inside : n < 2^depth) :
    laneStart bits n+2*2^bits ≤ 2*2^(depth+bits) := by
  calc
    _ = (n+1)*(2*2^bits) := by simp [laneStart,Nat.add_mul]
    _ ≤ 2^depth*(2*2^bits) := Nat.mul_le_mul_right _ inside
    _ = _ := by rw [Nat.pow_add]; ring

theorem endpoint_first {W b K : ℕ} (code : FieldCode F W) (m : Memory W) (budget : ImageCapacity B m b)
    (load : RawTickBuilder.loaded N code records m)
    (labels : ∀ j : Fin (G).cells, (m (ids+j.val)).val = ((HistoryCompiledRows.library G).id j).val)
    (dict : ∀ a : Occurrence N, (m (dictBase+((P).offset ((P).code a)).val)).val=((P).code a).val)
    (offsets : ∀ i, (m (masks+i.val)).val=((P).offset i).val)
    (T : ℕ) (extent : 2*T≤S) (pub : ℕ→Bool)
    (bank : Fin (1+bankSize)→Fin K) (oracle : Term W K 1) (header «prefix» span : Fin K)
    (params : Fin K→Word W) (original : Fin 1→Word W) (v : Fin 4→Word W)
    (table : params ∘ bank=publicData B original)
    (stepAt : params span=(2*2^low : ℕ)) (headerAt : params header=(S : Word W))
    (prefixAt : params «prefix»=(2*T : ℕ)) (lib : Fintype.card ((Fin 3→Bool)→F)≤2^W)
    (oracleAt : ∀ a, 2*T≤a → a<S → oracle.eval params m (fun _ => (a : Word W))=(pub a).toNat)
    (i : Fin (L0).cells) (j : Fin 4) (row : (v 0).val=i.val) (column : (v 1).val=j.val)
    (lane : (v 2).val=ln) (stage : (v 3).val=0) :
    (endpointProgram W bank oracle header «prefix» span).eval params m v=
      (HistoryCompiledRows.metadata tableId (pairLeaf hF hw hp base st hs hf r k fit L copies T extent pub) i j : Word W) := by
  have h := budget.size.trans_le budget.two_power
  unfold Layout.footprint at h
  let step := 2*2^low
  have z : (B).pinCount ln=(I).x := (bucketCounts hF hw hp base st hs hf r k fit L copies records dictBase masks ids).2.2.2
  have old : min step (S-laneStart low ln)=(I).x := by
    rw [bitIndex_pinCount]
    simp [step,laneStart,pinCount,pinSpan]
  have space : 2+((I).x+BucketIndex.ports copies (I).t)+(L0).internal≤2^W := by
    have bx : (I).x≤2*(B).lowRows := z ▸ Nat.min_le_right _ _
    change 2+((I).x+((B).bank+(B).bank))+(B).lowRows*(B).shape.stride≤2^W
    omega
  have ls : laneStart low ln+step≤2*(B).shape.rows := by
    exact lane_end (bits:=low) (finFunctionFinEquiv L).isLt
  unfold endpointProgram pairLeaf
  apply TraceSuffixProgram.program_metadata _ oracle header «prefix» span params m v S T step (laneStart low ln) pub
    L0 tableId (retained_le extent) i j stage column stepAt headerAt prefixAt (by rw [lane]; rfl) ?_
    (TraceSuffixProgram.metadata_small L0 tableId i j space (fun g => ((Fintype.equivFin _ g).isLt.trans_le lib))) old
    (retained_eq T low ln).symm extent (by change 2+(B).shape.header<_; omega) (by omega) (by omega) oracleAt
  rw [Term.eval_mapPublic,table]
  exact ready_first hF hw hp base st hs hf r k fit L copies records dictBase masks ids code m budget load labels dict offsets original v i j row column lane stage

theorem endpoint_later {W b K : ℕ} (m : Memory W) (budget : ImageCapacity B m b)
    (T : ℕ) (extent : 2*T≤S) (pub : ℕ→Bool)
    (bank : Fin (1+bankSize)→Fin K) (oracle : Term W K 1) (header «prefix» span : Fin K)
    (params : Fin K→Word W) (original : Fin 1→Word W) (v : Fin 4→Word W)
    (table : params ∘ bank=publicData B original)
    (stepAt : params span=(2*2^low : ℕ)) (headerAt : params header=(S : Word W))
    (prefixAt : params «prefix»=(2*T : ℕ)) (lib : Fintype.card ((Fin 3→Bool)→F)≤2^W)
    (jstage : Fin (q+1)) (later : jstage.val≠0) (i : Fin (B).relays) (j : Fin 4)
    (row : (v 0).val=i.val) (column : (v 1).val=j.val) (lane : (v 2).val=ln) (stage : (v 3).val=jstage.val) :
    (endpointProgram W bank oracle header «prefix» span).eval params m v=
      (HistoryCompiledRows.metadata (tableId (F:=F)) (RelayNetwork.network (r:=copies) (I).tag (P).mask jstage) i j : Word W) := by
  have h := budget.size.trans_le budget.two_power
  unfold Layout.footprint at h
  let step := 2*2^low
  have ls : laneStart low ln+step≤2*(B).shape.rows := by
    exact lane_end (bits:=low) (finFunctionFinEquiv L).isLt
  unfold endpointProgram
  apply TraceSuffixProgram.relay_metadata _ oracle header «prefix» span params m v S T step (laneStart low ln) _ pub
    (by rwa [stage]) stepAt headerAt prefixAt (by rw [lane]; rfl) ?_ ?_ extent (by change 2+(B).shape.header<_; omega)
    (by omega) (by omega)
  · rw [Term.eval_mapPublic,table]
    exact ready_later hF hw hp base st hs hf r k fit L copies records dictBase masks ids m budget original v jstage later i j row column lane stage
  · apply TraceSuffixProgram.metadata_small (RelayNetwork.network (r:=copies) (I).tag (P).mask jstage) (tableId (F:=F)) i j ?_
        (fun g => (Fintype.equivFin _ g).isLt.trans_le lib)
    change 2+((B).bank+(B).bank)+0≤2^W; omega


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
