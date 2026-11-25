import OAI.Hierarchy.HistorySelectedSeedDecode
import OAI.Hierarchy.TraceReceiverPreparedLeaf
import OAI.Hierarchy.TraceReceiverLeafRoom

namespace OAI
/-! # The physical template and mask preparation feeds the selected seed publisher -/

namespace Hierarchy.TraceReceiverSeedInstalled

open ThreeFlat Diagonal Diagonal.TraceBitHeader RAM Computability.VPVNP.BurstRAM PrivateRAM
open RAM.PhysicalProcedure Diagonal.PhysicalStage LaneCursor LaneCursor.RowLayout
open Filter
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Fintype F] [Field F] {w pc regs slots S base q low fuel b : ℕ}
    (M : Machine (64*w) pc regs slots) (fit : NativeTrace.Fits M S base ((q+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^(64*w)) (st : Word (64*w))
set_option quotPrecheck false
local notation "wordBits" => 64*w
local notation "traceDepth" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs slots traceDepth
local notation "N" => TraceBitHeader.network hF fit.width fit.labels base st fit.header fit.time regs slots traceDepth
local notation "n" => TraceReceiverTemplate.count G
local notation "off" => TraceReceiverMaskBanks.count (q+1) low

/-- The word image of the two executed procedures satisfies the exact installed
predicate of the native selected cursor writer. -/
theorem installed (raw gateBase dict masks tmp : ℕ) (mem : Memory wordBits)
    (beforeD : gateBase+n≤dict) (beforeM : gateBase+n≤ masks)
    (sr : dict+2^(q+1)*2^low≤tmp) (dr : masks+off≤tmp) (space : tmp+2*off < 2^wordBits)
    (apart : dict+2^(q+1)*2^low≤ masks ∨ masks+off≤dict) :
    HistorySelectedSeedDecode.Installed (F:=F) (q:=q) (low:=low) (S:=S) (f:=fuel) hF fit.width fit.labels
      base st fit.header fit.time regs slots fit.grid raw dict masks gateBase hF
      (TraceReceiverMaskLoop.output (q+1) low dict masks tmp
        (TraceReceiverTemplate.image gateBase
          (TraceReceiverTemplate.words M fit hF st (FieldCode.ofCardLe hF) raw gateBase) mem)) := by
  have gates := TraceReceiverPreparedLeaf.mounted M fit hF st raw gateBase dict masks tmp mem beforeD beforeM sr dr space
  have msk := TraceReceiverPreparedLeaf.masks_read M fit hF st raw gateBase dict masks tmp mem sr dr space apart
  exact ⟨gates,msk.1,msk.2⟩

/-- Loading the stage library below every virtual seed operand retains the
three issued readouts in the actual resulting memory. -/
theorem after_codebook (raw gateBase dict masks : ℕ) {entries : ℕ} (start : ℕ)
    (values : Fin entries→Word wordBits) (m : Memory wordBits)
    (prior : HistorySelectedSeedDecode.Installed (F:=F) (q:=q) (low:=low) (S:=S) (f:=fuel) hF fit.width fit.labels
      base st fit.header fit.time regs slots fit.grid raw dict masks gateBase hF m)
    (t : start+entries≤gateBase) (u : start+entries≤dict) (v : start+entries≤ masks) :
    HistorySelectedSeedDecode.Installed (F:=F) (q:=q) (low:=low) (S:=S) (f:=fuel) hF fit.width fit.labels
      base st fit.header fit.time regs slots fit.grid raw dict masks gateBase hF
      (TraceReceiverTemplate.image start values m) := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [TraceReceiverTemplate.image_outside start values m (.inr (by omega))]
    exact prior.mounted i hi
  · intro i
    rw [TraceReceiverTemplate.image_outside start values m (.inr (by omega))]
    exact prior.dictionary i
  · intro i
    rw [TraceReceiverTemplate.image_outside start values m (.inr (by omega))]
    exact prior.offsets i

/-- Putting the virtual record window below the compact table, then the sparse
and dense mask arrays in order, pays all read bounds of the native row decoder. -/
theorem fits (copies raw gateBase dict masks tmp : ℕ)
    (gap : raw+11*max (N).cells (2^traceDepth*(G).cells)+4≤gateBase)
    (beforeD : gateBase+n≤dict) (beforeM : dict+2^traceDepth≤ masks)
    (dense : masks+off≤tmp) (space : tmp+2*off < 2^wordBits)
    (safe : ∀ (v : Fin (2^traceDepth)) i, (TraceBitDescriptor.records (p:=pc) (r:=regs) (k:=slots) (d:=traceDepth)
      fit.width base S fuel i).Fits wordBits v.val)
    (size : (bucketShape (q:=q) (low:=low) (S:=S) (f:=fuel) hF fit.width fit.labels base st regs slots
      copies raw dict masks (gateBase+FixedTraceImage.count G)).footprint < 2^b)
    (word : 5*b+128≤wordBits) (coeff : Fintype.card F≤wordBits) (labels : Fintype.card ((Fin 3→Bool)→F)≤2^wordBits) :
    HistorySelectedSeedDecode.Fits (q:=q) (low:=low) (S:=S) (f:=fuel) (b:=b) (W:=wordBits)
      hF fit.width fit.labels base st fit.header fit.time regs slots copies raw dict masks gateBase := by
  have dictMasks : dict ≤ masks := (Nat.le_add_right dict (2^traceDepth)).trans beforeM
  have masksTmp : masks ≤ tmp := (Nat.le_add_right masks off).trans dense
  have tmpRoom : tmp < 2^wordBits := (Nat.le_add_right tmp (2*off)).trans_lt space
  have bound := beforeD.trans_lt (dictMasks.trans_lt (masksTmp.trans_lt tmpRoom))
  have tableRoom := TraceReceiverTemplate.room G gateBase bound
    (TraceStaticRow.table_internal_le_cells hF fit.width fit.labels base fuel st regs slots traceDepth)
  have nsmall := Nat.le_max_left (N).cells (2^traceDepth*(G).cells)
  have rsmall := Nat.le_max_right (N).cells (2^traceDepth*(G).cells)
  have ids : FixedTraceImage.count G+(G).cells≤n := by simp [TraceReceiverTemplate.count]
  refine ⟨tableRoom.1,safe,tableRoom.2.1,tableRoom.2.2.1,tableRoom.2.2.2.1,tableRoom.2.2.2.2,
    by omega,by omega,by omega,(by omega : raw+11*(N).cells≤dict).trans dictMasks,
    size,word,?_,?_,?_,?_,?_,labels⟩
  · change raw+11*(2^traceDepth*(G).cells)+4≤2^wordBits
    omega
  · change dict+2^traceDepth≤2^wordBits
    omega
  · change masks+(1+2*traceDepth)≤2^wordBits
    dsimp [TraceReceiverMaskBanks.count] at dense
    omega
  · change gateBase+FixedTraceImage.count G+(G).cells≤2^wordBits
    omega
  · have wordPart : wordBits≤(1+6*pc+slots)*wordBits := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right wordBits (by omega : 1≤1+6*pc+slots)
    have allRows := Nat.le_mul_of_pos_left ((1+6*pc+slots)*wordBits) (Nat.two_pow_pos traceDepth)
    apply (coeff.trans (wordPart.trans allRows)).trans
    dsimp only [bucketShape,TraceSourceOwner.Shape.count,TraceSourceOwner.shape]
    omega

/-- All three immutable input banks can be placed beyond the native stage
scratch, with a separate virtual record window starting at address zero. -/
theorem storage (large : 7≤w) (depth : traceDepth≤2*w+1) (small : n≤2^(w/100)) :
    let J := 2^(32*w)
    let gateBase := 26*J
    let dict := 27*J
    let masks := dict+2^traceDepth
    let tmp := masks+off
    11*max (N).cells (2^traceDepth*(G).cells)+4 ≤ gateBase ∧ gateBase+n≤dict ∧
      dict+2^(q+1)*2^low≤ masks ∧ masks+off=tmp ∧ tmp+2*off<2^wordBits := by
  dsimp only
  have row := TraceBitHeader.count_cells (F:=F) hF fit.width fit.labels base st fit.header fit.time regs slots traceDepth
  rw [row,max_self]
  have fieldSize : 11*(G).cells+4 ≤ n := by
    simp only [TraceReceiverTemplate.count,FixedTraceImage.count,FixedTraceProgram.P]
    omega
  have rowLen := Nat.mul_le_mul_left (2^traceDepth) fieldSize
  have pos : 1≤2^traceDepth := Nat.two_pow_pos _
  have vlen : 11*(2^traceDepth*(G).cells)+4 ≤ 2^traceDepth*n := by nlinarith
  have prod : 2^traceDepth*n≤2^(32*w) := by
    calc
      _ ≤ 2^traceDepth*2^(w/100) := Nat.mul_le_mul_left _ small
      _ = 2^(traceDepth+w/100) := (pow_add ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have table : n ≤ 2^(32*w) := small.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have high := (TraceReceiverMaskLoop.sector_room (high:=27*2^(32*w)) (lane:=q+1) (low:=low)
    large depth (by omega)).2
  rw [←pow_add] at high
  exact ⟨by omega,by omega,by rw [←pow_add],rfl,by omega⟩

/-- The actual serialized template meets the numerical hypothesis of `storage`
for every sufficiently large receiver width. -/
theorem eventual_count : ∀ᶠ z : ℕ in Filter.atTop,
    TraceReceiverTemplate.coefficient*(z+1)^14 ≤ 2^(z/100) :=
  TraceDistribution.polynomial_room _ _

end
end Hierarchy.TraceReceiverSeedInstalled

end OAI
