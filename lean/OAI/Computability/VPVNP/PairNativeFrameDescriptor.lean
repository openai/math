import OAI.Computability.VPVNP.PairNativeFrameLeaf
import OAI.Computability.VPVNP.PairTerminalLayout
import OAI.Computability.VPVNP.PairTerminalPrefixLayout
import OAI.Computability.VPVNP.PairSimulationCounters

/-! # Geometry fields of the native terminal bootstrap and prefix scan

Six header cells survive the width-prefix scan. The separately computed
role offset is passed in a saved register. Together these seven values
determine the geometry installed by each final vertex.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeFrame
open BurstRAM BurstRAM.PrivateRAM CompressorRecords DescriptorSpace Compression TerminalPrefix
open scoped Fin.CommRing

variable {w a g : ℕ}

theorem regions_eq (degree n firstRow rowWords labels : ℕ) :
    regions degree n firstRow rowWords labels =
      TerminalLayout.privateRegions degree n (firstRow+rowWords) labels := rfl

/-- Agreement of six terminal-header cells with the supplied row interval, row stride, two
radices and auxiliary shadow span. -/
structure Readback (m : Memory w) (header : Word w) (firstRow rowWords stride baseRadix laneRadix : ℕ)
    (shadowSpan : Word w) : Prop where
  row : m (header+4).val = (firstRow : Word w)
  words : m (header+5).val = (rowWords : Word w)
  pitch : m (header+15).val = (stride : Word w)
  base : m (header+18).val = (baseRadix : Word w)
  lane : m (header+19).val = (laneRadix : Word w)
  span : m (header+20).val = shadowSpan

private theorem offset_val (header : Word w) {j : ℕ} (fit : header.val+32 ≤ 2^w) (hj : j < 32) :
    (header + (j : Word w)).val = header.val+j := by
  rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : j < 2^w),Nat.mod_eq_of_lt (by omega)]

theorem bootstrap_readback (L : Layout) (last : ℕ) (A : TerminalBootstrap.Header L last) (cap r : ℕ)
    (pub : Fin 11 → Word w) (m : Memory w) (state : Word w) (ready : TerminalBootstrap.Ready L last A pub m)
    (exp : (pub 7).val = r) (hr : r < w) (reserve : 32 ≤ L.base+2^r*2^r)
    (room : L.base+2^r*2^r ≤ 2^w) :
    Readback (after m (TerminalBootstrap.report L.shape cap pub state m).events) (Worker.header pub)
      (endAddress L) (A.rowWords cap) (cap+2) A.baseRadix A.laneRadix (TerminalBootstrap.shadowSpan pub m) := by
  have hb := header_val L pub r ready.workspace exp hr reserve room
  have fit : (Worker.header pub).val+32 ≤ 2^w := by rw [hb,TerminalBootstrap.address]; omega
  have actual := (TerminalBootstrap.native L last A cap pub m state ready r exp hr reserve room).2.2.1
  have field (j : Fin 21) :
      after m (TerminalBootstrap.report L.shape cap pub state m).events (Worker.header pub + (j.val : Word w)).val =
      TerminalBootstrap.values L last A cap pub m j := by
    rw [offset_val _ fit (by have := j.isLt; omega),hb]; exact actual j
  exact ⟨field 4,field 5,field 15,field 18,field 19,field 20⟩

variable {header span : Word w} {m : Memory w} {firstRow rowWords stride baseRadix laneRadix : ℕ}

theorem Readback.transfer (h : Readback m header firstRow rowWords stride baseRadix laneRadix span)
    {later : Memory w} (stable : ∀ j ∈ ([4,5,15,18,19,20] : List ℕ),
      later (header+(j : Word w)).val = m (header+(j : Word w)).val) :
    Readback later header firstRow rowWords stride baseRadix laneRadix span :=
  ⟨(stable 4 (by decide)).trans h.row,(stable 5 (by decide)).trans h.words,
    (stable 15 (by decide)).trans h.pitch,(stable 18 (by decide)).trans h.base,
    (stable 19 (by decide)).trans h.lane,(stable 20 (by decide)).trans h.span⟩

theorem Readback.after_scan {pub : Fin 11 → Word w} (h : Readback m (Worker.header pub)
    firstRow rowWords stride baseRadix laneRadix span) {X : State a g} {T : IncidenceDirectory w}
    {prefixBase : Word w} {rs : List (Report w)} (run : Segment.Run pub X T prefixBase m rs)
    (fit : (Worker.header pub).val+32 ≤ 2^w) (below : prefixBase.val+arcCount X ≤ (Worker.header pub).val) :
    Readback (after m (eventLog rs)) (Worker.header pub) firstRow rowWords stride baseRadix laneRadix span := by
  apply h.transfer
  intro j hj
  have options : j = 4 ∨ j = 5 ∨ j = 15 ∨ j = 18 ∨ j = 19 ∨ j = 20 := by simpa using hj
  have addr := offset_val (Worker.header pub) fit (by omega : j < 32)
  have a12 : (Worker.header pub+12).val = (Worker.header pub).val+12 := offset_val _ fit (by decide : 12<32)
  have a14 : (Worker.header pub+14).val = (Worker.header pub).val+14 := offset_val _ fit (by decide : 14<32)
  have fresh := run.stored.outside (Worker.header pub+(j : Word w)).val (by rw [addr,a12]; omega)
    (.inr (by rw [addr]; omega))
  rw [fresh]
  apply ite_eq_right
  rw [addr,a14]; omega

/-- A completed vertex adds its histogram strictly below the terminal
header. Every following vertex therefore reads the same six operands. -/
theorem Readback.addHistogram (h : Readback m header firstRow rowWords stride baseRadix laneRadix span)
    {t : ℕ} (base grammar : ℕ) (hist : Fin t → ℕ) (below : base+grammar+t ≤ header.val)
    (fit : header.val+32 ≤ 2^w) :
    Readback (Counters.addHistogram base grammar hist m) header firstRow rowWords stride baseRadix laneRadix span := by
  apply h.transfer
  intro j hj
  have opts : j = 4 ∨ j = 5 ∨ j = 15 ∨ j = 18 ∨ j = 19 ∨ j = 20 := by simpa using hj
  apply Counters.addHistogram_outside
  right
  rw [offset_val header fit (by omega : j < 32)]
  omega

theorem Readback.regions_eq (h : Readback m header firstRow rowWords stride baseRadix laneRadix span)
    (degree : ℕ) (pub : Fin 11 → Word w) (n labels : ℕ) (hn : (pub 6).val=n) (hl : (pub 9).val=labels)
    (fit : firstRow+rowWords < 2^w) :
    fromHeader degree pub header m = TerminalLayout.privateRegions degree n (firstRow+rowWords) labels := by
  rw [fromHeader,h.row,h.words,Fin.val_natCast,Fin.val_natCast,
    Nat.mod_eq_of_lt (by omega : firstRow < 2^w),Nat.mod_eq_of_lt (by omega : rowWords < 2^w),hn,hl]
  exact NativeFrame.regions_eq ..

/-- Pointwise coincidence of all twelve stored words with the terminal
layout, including the histogram, live role displacement and cache base. -/
theorem Readback.fields_eq (h : Readback m header firstRow rowWords stride baseRadix laneRadix span)
    (degree : ℕ) (pub : Fin 11 → Word w) (role : Word w) (n labels : ℕ) (hn : (pub 6).val=n)
    (hl : (pub 9).val=labels) (fit : firstRow+rowWords < 2^w) (j : Fin 12) :
    fields degree pub header role m j =
      (TerminalLayout.geometry (TerminalLayout.privateRegions degree n (firstRow+rowWords) labels)
        firstRow stride baseRadix laneRadix (pub 3).val span.val role.val n j : Word w) := by
  have hword : pub 6 = (n : Word w) := hn ▸ (Fin.cast_val_eq_self _).symm
  have eqn := h.regions_eq degree pub n labels hn hl fit
  unfold fields; rw [eqn]
  fin_cases j <;> first | exact h.row | exact h.words | exact h.pitch | exact h.base | exact h.lane |
    exact h.span.trans (Fin.cast_val_eq_self _).symm | exact (Fin.cast_val_eq_self _).symm | exact hword | rfl

/-- The pointer at live length lies below the geometry, since the private
layout contains an argument interval for each absolute node address up to
the exclusive row end. -/
theorem Readback.pointer_before (h : Readback m header firstRow rowWords stride baseRadix laneRadix span)
    (degree : ℕ) (pub : Fin 11 → Word w) (positive : 0 < firstRow) (fit : firstRow+rowWords < 2^w) :
    (pub 6).val < frameBase (fromHeader degree pub header m) := by
  rw [h.regions_eq degree pub _ _ rfl rfl fit]
  change (pub 6).val < (pub 6).val + (firstRow+rowWords)*(2*degree*(pub 6).val+1) + (pub 9).val
  have hp : 0 < (firstRow+rowWords)*(2*degree*(pub 6).val+1) :=
    Nat.mul_pos (by omega) (Nat.succ_pos _)
  exact (Nat.lt_add_of_pos_right hp).trans_le (Nat.le_add_right _ _)

/-- The genuine decoder's address, radix and span data from the same
selected bootstrap and the prepared auxiliary shadow. -/
theorem Readback.leaf_operands {p r k n a' H s : ℕ} {L : PrimedInputRAM.Lengths} {Q : PrimedInputRAM.Layout L n a' H w}
    (h : Readback m header firstRow rowWords stride baseRadix laneRadix span) (degree : ℕ)
    (pub : Fin 11 → Word w) (role : Word w) (pc : LeafImage.Label → Fin p) (reg : LeafImage.Reg ↪ Fin r)
    (operand : LeafImage.Pub → Fin k) (ret : Fin p) (M : Machine w p r k)
    (assigned : M.publicData ∘ operand = leafWords degree pub header role m ∘ LeafGeometryLoad.slot)
    (data : PrimedCounter.Data Q s) (b l cap : ℕ) (pitch : stride=cap+2) (rb : baseRadix=2^b)
    (rl : laneRadix=2^l) (fits : max stride (max baseRadix laneRadix) < 2^w)
    (spanVal : span.val = LiveAuxiliaryHeaders.span L data.hist.length)
    (range : (pub 3).val+span.val ≤ 2^w)
    (shadow : ∀ i < span.val, (m ((pub 3).val+i)).val = (data.initial i).val)
    (hn : (pub 6).val=n) :
    LeafFront.Operands (LeafImage.front pc reg operand ret) M m data (fromHeader degree pub header m) b l cap ∧
    M.publicData (operand .size) = (n : Word w) := by
  apply NativeFrame.leaf_operands degree pub header role m pc reg operand ret M assigned data b l cap
  · rw [h.pitch,Fin.val_natCast,Nat.mod_eq_of_lt (by omega)]; exact pitch
  · rw [h.base,Fin.val_natCast,Nat.mod_eq_of_lt (by omega)]; exact rb
  · rw [h.lane,Fin.val_natCast,Nat.mod_eq_of_lt (by omega)]; exact rl
  · rw [h.span]; exact spanVal
  · rw [h.span]; exact range
  · rw [h.span]; exact shadow
  · exact hn

end PairSimulation.NativeFrame

end VPVNP
end Computability
end OAI
