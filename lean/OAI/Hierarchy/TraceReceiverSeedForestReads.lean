import OAI.Hierarchy.HistorySelectedSeedDecode
import OAI.Hierarchy.TraceReceiverSeedWords
import OAI.ThreeFlat.Diagonal.TracePairLeafShape

namespace OAI
/-! # The selected seed emitter reads the literal leaf of the assembled physical forest -/

namespace Hierarchy.TraceReceiverSeedForestReads
open ThreeFlat Diagonal Diagonal.TraceBitHeader PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor LaneCursor.RowLayout RAM RAM.TraceBucketAtom
open RAM.HistoryInitialSeed HistorySelectedSeedDecode TraceReceiverSeedWords
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Fintype F] [Field F] {W pc regs slots S base k low fuel b : ℕ}

omit [Field F] in
private theorem transfer {p q : ℕ} {N : BitNetwork F p} {T : BitNetwork F q}
    (arity : p=q) (nets : HEq N T) (start : ℕ) :
    (N).cells=T.cells ∧ (N).internal=T.internal ∧
      recordAt (W:=W) tableId N start = recordAt tableId T start := by
  subst q
  cases eq_of_heq nets
  exact ⟨rfl,rfl,rfl⟩

variable (M : Machine W pc regs slots) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F≤2^W) (st : Word W) (B : Block F) (hk : 2≤k+1)
    (v : PairedCursor.Site (k+1)) (raw dict masks gateBase : ℕ)
set_option quotPrecheck false
local notation "d" => (k+1)+low
local notation "G" => TraceStaticRow.gateTable hF t.width t.labels base fuel st regs slots d
local notation "N" => TraceBitHeader.network hF t.width t.labels base st t.header t.time regs slots d
local notation "ids" => gateBase+FixedTraceImage.count G
local notation "shape" => bucketShape (q:=k) (low:=low) (S:=S) (f:=fuel) hF t.width t.labels base st regs slots B.cursorCopies raw dict masks ids
local notation "I" => TraceSourceOwner.bitIndex hF t.width t.labels base st t.header t.time regs slots t.grid v.2
local notation "P" => TraceBitHeader.layout hF t.width t.labels base st t.header t.time regs slots t.grid
local notation "L" => wordsLayout M t hF st B hk
local notation "tree" => (forest M t hF st B hk v).compile
local notation "zeroNet" => (I).firstNetwork (r:=B.cursorCopies) (TraceSourceOwner.bitAddress hF t.width t.labels base st t.header t.time regs slots t.grid v.2 I) 0
local notation "relay" => RelayNetwork.network (F:=F) (r:=B.cursorCopies) (I).tag (P).mask v.1

/-- All native cursor dimensions follow from the supplied stage, lane and
shape alone, before the runtime establishes the protected memory regions. -/
theorem forest_dimensions (Y : HistoryInitialSeed.Layout) (z : Site)
    (same : Y.trace=shape) (_lane : z.lane=(finFunctionFinEquiv v.2).val)
    (time : z.stage=v.1.val) (ext : z.extPins=width M t hF st v) :
    (L).ports.form.width v=z.extPins+2*Y.trace.bank ∧ (tree).cells=z.rows Y ∧ (tree).internal=z.bits Y := by
  have dims := relayLeaf_shape hF t.width t.labels base st t.header t.time regs slots t.grid v.2
    B.cursorCopies raw dict masks ids v.1
  have half := portWidth M t hF st B hk v
  have arity : (L).ports.form.width v=z.extPins+2*Y.trace.bank := by
    change width M t hF st v+(L).ports.halfBits v=_
    rw [←half,dims.2.2,same,ext]
  refine ⟨arity,?_⟩
  by_cases first : v.1=0
  · have zero : z.stage=0 := by simpa only [first,Fin.val_zero] using time
    have eqv : HEq tree zeroNet := by simpa only [first] using forest_first M t hF st B hk v first
    have ports : (L).ports.form.width v=(I).x+BucketIndex.ports B.cursorCopies (I).t := by
      change width M t hF st v+(L).ports.halfBits v=_
      rw [←half]
      simp [TraceReceiverSeedWords.width,first]
    obtain ⟨cells,bits,records⟩ := transfer (W:=W) ports eqv (z.stream Y)
    have fc : (zeroNet).cells=z.rows Y := by simp only [Site.rows,zero,HistoryInitialSeed.Layout.hidden,same]; rfl
    have fb : (zeroNet).internal=z.bits Y := by simp only [Site.bits,zero,HistoryInitialSeed.Layout.hidden,same]; rfl
    exact ⟨cells.trans fc,bits.trans fb⟩
  · have positive : v.1.val≠0 := fun h=>first (Fin.ext h)
    have nz : z.stage≠0 := by simpa only [time] using positive
    have ports : (L).ports.form.width v=BucketIndex.ports B.cursorCopies (I).t := by
      change width M t hF st v+(L).ports.halfBits v=_
      rw [←half]
      simp [TraceReceiverSeedWords.width,first]
    obtain ⟨cells,bits,records⟩ := transfer (W:=W) ports (forest_later M t hF st B hk v first) (z.stream Y)
    have rc : (relay).cells=z.rows Y := by simpa only [Site.rows,ite_eq_right nz,Nat.add_zero,same] using dims.1
    have rb : (relay).internal=z.bits Y := by simpa only [Site.bits,ite_eq_right nz] using dims.2.1
    exact ⟨cells.trans rc,bits.trans rb⟩

/-- The same canonical seed tree supplies all three operand dimensions, plus
its own compiled four-word records at the actual selected site pointer. -/
theorem forest_receipt (Y : HistoryInitialSeed.Layout) (z : Site) (rest : Fin 1→Word W) (src : Memory W)
    (image : Installed (q:=k) (low:=low) (S:=S) (f:=fuel) hF t.width t.labels base st t.header t.time regs slots
      t.grid raw dict masks gateBase hF src)
    (size : Fits (q:=k) (low:=low) (S:=S) (f:=fuel) (b:=b) (W:=W) hF t.width t.labels base st t.header t.time
      regs slots B.cursorCopies raw dict masks gateBase)
    (template : Protected Y z gateBase (TraceReceiverTemplate.count G))
    (dictionary : Protected Y z dict (2^d)) (mask : Protected Y z masks (1+(d+d)))
    (same : Y.trace=shape) (lane : z.lane=(finFunctionFinEquiv v.2).val) (laneFit : z.lane<2^W)
    (time : z.stage=v.1.val) (stageFit : z.stage<2^W) (ext : z.extPins=width M t hF st v) :
    (L).ports.form.width v=z.extPins+2*Y.trace.bank ∧ (tree).cells=z.rows Y ∧ (tree).internal=z.bits Y ∧
      HistorySelectedSeed.RawReads Y z
        (TraceRawLookup.virtual W ⟨raw,(N).cells,ids+(G).cells⟩ (publicProgram W)) (publicData shape rest) src
        (recordAt tableId tree (z.stream Y)) := by
  obtain ⟨arity,rows,privateBits⟩ := forest_dimensions M t hF st B hk v raw dict masks gateBase Y z same lane time ext
  have half := portWidth M t hF st B hk v
  refine ⟨arity,rows,privateBits,?_⟩
  by_cases first : v.1=0
  · have zero : z.stage=0 := by simpa only [first,Fin.val_zero] using time
    have eqv : HEq tree zeroNet := by simpa only [first] using forest_first M t hF st B hk v first
    have ports : (L).ports.form.width v=(I).x+BucketIndex.ports B.cursorCopies (I).t := by
      change width M t hF st v+(L).ports.halfBits v=_
      rw [←half]
      simp [TraceReceiverSeedWords.width,first]
    obtain ⟨cells,_,records⟩ := transfer (W:=W) ports eqv (z.stream Y)
    have fc : (zeroNet).cells=z.rows Y := cells.symm.trans rows
    rw [records]
    exact first_reads hF t.width t.labels base st t.header t.time regs slots t.grid v.2 B.cursorCopies raw dict masks gateBase
      hF Y z rest src image size template dictionary mask lane laneFit zero fc
  · have positive : v.1.val≠0 := fun h=>first (Fin.ext h)
    have ports : (L).ports.form.width v=BucketIndex.ports B.cursorCopies (I).t := by
      change width M t hF st v+(L).ports.halfBits v=_
      rw [←half]
      simp [TraceReceiverSeedWords.width,first]
    obtain ⟨cells,_,records⟩ := transfer (W:=W) ports (forest_later M t hF st B hk v first) (z.stream Y)
    have rc : (relay).cells=z.rows Y := cells.symm.trans rows
    rw [records]
    exact later_reads hF t.width t.labels base st t.header t.time regs slots t.grid v.2 B.cursorCopies raw dict masks gateBase
      hF Y z rest src image size template dictionary mask lane laneFit v.1 time positive stageFit rc

end
end Hierarchy.TraceReceiverSeedForestReads

end OAI
