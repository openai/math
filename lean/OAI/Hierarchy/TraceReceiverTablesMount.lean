import OAI.Hierarchy.TraceReceiverLeafOperands
import OAI.Hierarchy.TraceReceiverLibraryMount
import OAI.Hierarchy.TraceReceiverSeedInstalled

namespace OAI
/-! # The authentic verifier mask and positive stage library of one local receiver -/

namespace Hierarchy.TraceReceiverTablesMount
open ThreeFlat Diagonal PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open GridRegisteredSetting TraceReceiverLeafSetup PhysicalProcedure HistoryStageBody.Physical
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {w pc regs slots S base fuel axes : ℕ}
variable (D : RunData F (64*w) pc regs slots S base fuel axes (w/2)) (l : GridNativeImage.Layout)
set_option quotPrecheck false
local notation "W" => 64*w
local notation "dep" => (axes+1)+w/2
local notation "delta" => TraceReceiverMaskBanks.count (axes+1) (w/2)
local notation "V" => TraceReceiverTemplate.words D.machine D.fit D.field D.state (FieldCode.ofCardLe D.field) 0 (gateBase D)
local notation "L" => libraryWords D.block W
local notation "tapeText" => SelfAdvice.textSize W pc slots
local notation "args" => GridStructuralHeader.parameters D.block (axes+1) D.passes l.selectorCap
    D.machine D.fit D.field D.state 0 (gateBase D)

def decode : Procedure W := (PhysicalInputPhases.packing W (templateSrc D l) (gateBase D) (templateSize D)).seq
  (TraceReceiverMaskLoop.program W (axes+1) (w/2) (dict D) (masks D) (tmp D))

def lib : Procedure W := PhysicalInputPhases.packing W (librarySrc D l) (start w) L

def masked (m : Memory W) : Memory W := TraceReceiverMaskLoop.output (axes+1) (w/2) (dict D) (masks D) (tmp D)
  (TraceReceiverTemplate.image (gateBase D) V m)

def output (m : Memory W) : Memory W := TraceReceiverTemplate.image (start w) (data D.block W W) (masked D m)

def decodeWork : ℕ := templateSize D*(5*W+6)+6+TraceReceiverMaskLoop.work W (axes+1) (w/2) (dict D) (masks D)
def libWork : ℕ := libraryWords D.block (64*w)*(5*(64*w)+6)+6

def installed (m : Memory W) := HistorySelectedSeedDecode.Installed (q:=axes) (low:=w/2) (S:=S) (f:=fuel)
  D.field D.fit.width D.fit.labels base D.state D.fit.header D.fit.time regs slots D.fit.grid 0
  (dict D) (masks D) (gateBase D) D.field m

/-- The source is the same prefix the receiver used to replay the compressor.
Each subsequent execution has a concrete memory, operand receipt and cost. -/
theorem run {p : ℕ} (textFit : tapeText≤w^2) (self : Fin (w^2)→Bool) (index : Word W)
    (sel : Fin (l.selectorCap+1)→Bool) (input : ℕ→Bool) (m : Memory W) (safe : ℕ)
    (headerFit : (GridReceiverHeader.header tapeText textFit self index args sel).length≤p)
    (covered : 2+(GridReceiverHeader.header tapeText textFit self index args sel).length ≤ safe)
    (read : ∀ i : Fin (GridReceiverHeader.header tapeText textFit self index args sel).length,
      input i.val=(GridReceiverHeader.header tapeText textFit self index args sel)[i.val])
    (frame : ∀ z,z < safe → m z=TickMountedPins.memory (w:=W) (fun j : Fin p=>input j.val) z)
    (large : 7≤w) (depth : dep≤2*w+1) (small : templateSize D≤2^(w/100))
    (inputRoom : 2+p ≤ start w) (tableHigh : start w+L≤gateBase D) (wordRoom : start w+L<2^W) :
    (decode D l).Exec m (masked D m) (decodeWork D) ∧
    (lib D l).Exec (masked D m) (output D m) (libWork D) ∧
    installed D (output D m) ∧ Mounted D.block W W (start w) (output D m) ∧
    ∀ z,z<gateBase D → (z< start w ∨ start w+L≤z) → output D m z=m z := by
  let head:=GridReceiverHeader.header tapeText textFit self index args sel
  have env:=TraceReceiverSeedInstalled.storage D.machine D.fit D.field D.state large depth small
  change _ ∧ gateBase D+templateSize D≤dict D ∧ dict D+2^(axes+1)*2^(w/2)≤ masks D ∧
    masks D+delta=tmp D ∧ tmp D+2*delta<2^W at env
  obtain ⟨_,before,banks,temporary,address⟩:=env
  have off : dict D≤ masks D := (Nat.le_add_right _ _).trans banks
  have maskTmp : masks D≤tmp D := (Nat.le_add_right _ _).trans temporary.le
  have tmpRoom : tmp D<2^W := (Nat.le_add_right _ _).trans_lt address
  have templateRoom : gateBase D+templateSize D<2^W := (before.trans (off.trans maskTmp)).trans_lt tmpRoom
  have gateRoom : gateBase D<2^W := (Nat.le_add_right _ _).trans_lt templateRoom
  have gateDict : gateBase D≤dict D := (Nat.le_add_right _ _).trans before
  have source : templateSrc D l+W*templateSize D≤2+head.length := by
    have bound := TraceReceiverHeaderMount.covered D.block (axes+1) D.passes l.selectorCap
      D.machine D.fit D.field D.state 0 (gateBase D) tapeText textFit self index sel []
    rw [List.append_nil] at bound
    exact bound
  have headRoom : 2+head.length≤gateBase D := by dsimp only [head]; omega
  have restored : ∀ z,z<2+head.length → m z=TickMountedPins.memory (w:=W) (TraceReceiverHeaderMount.tape head []) z :=
    fun z hz=>(frame z (hz.trans_le covered)).trans (TraceReceiverHeaderMount.frame_prefix (F:=F) (w:=w) (text:=tapeText) head input headerFit read z hz)
  have run0 : (decode D l).Exec m (masked D m) (decodeWork D) :=
    TraceReceiverPreparedLeaf.run_after D.machine D.fit D.field D.state 0 (gateBase D) (dict D) (masks D) (tmp D)
      D.block (axes+1) D.passes l.selectorCap tapeText textFit self index sel [] m (2+head.length) restored source
      (by omega) (banks.trans maskTmp) temporary.le address (.inr (source.trans headRoom)) templateRoom
      ((source.trans headRoom).trans_lt gateRoom)
  have low : ∀ z,z<gateBase D → masked D m z=m z := fun z hz=>TraceReceiverPreparedLeaf.below
    D.machine D.fit D.field D.state 0 (gateBase D) (dict D) (masks D) (tmp D) m
    gateDict (gateDict.trans off) (banks.trans maskTmp) temporary.le address hz
  have maskImage : installed D (masked D m) := TraceReceiverSeedInstalled.installed D.machine D.fit D.field D.state
    0 (gateBase D) (dict D) (masks D) (tmp D) m before (before.trans off) (banks.trans maskTmp) temporary.le address (.inl banks)
  obtain ⟨run1,codebook,unchanged⟩:=TraceReceiverLibraryMount.run_on_header D.block (axes+1) D.passes l.selectorCap
    D.machine D.fit D.field D.state 0 (gateBase D) tapeText textFit self index sel input (masked D m) headerFit inputRoom read
    (fun z hz=>(low z (hz.trans_le headRoom)).trans (frame z (hz.trans_le covered))) wordRoom
  exact ⟨run0,run1,TraceReceiverSeedInstalled.after_codebook D.machine D.fit D.field D.state 0 (gateBase D) (dict D) (masks D)
    (start w) (data D.block W W) (masked D m) maskImage tableHigh (by omega) (by omega),codebook,
    fun z hz apart=>(unchanged z apart).trans (low z hz)⟩

/-- Uniform scalar admission for both real table scans. The only size supplied
by the local tape is its own public pin count. -/
theorem admission (B : Block F) : ∀ᶠ w : ℕ in Filter.atTop,
    ∀ {pc regs slots S base fuel axes p : ℕ} (D : RunData F (64*w) pc regs slots S base fuel axes (w/2)),
      D.block=B → pc≤64*w → regs≤64*w → slots≤64*w → (axes+1)+w/2≤2*w+1 → p≤2^(16*w) →
      7≤w ∧ templateSize D≤2^(w/100) ∧ 2+p ≤ start w ∧
        start w+libraryWords D.block (64*w)≤gateBase D ∧ start w+libraryWords D.block (64*w)<2^(64*w) := by
  filter_upwards [TraceReceiverLibraryMount.placement B,TraceReceiverLibraryMount.sector_room B,
    TraceReceiverSeedInstalled.eventual_count,Filter.eventually_ge_atTop (Fintype.card F+7)] with w place bound size late
  intro pc regs slots S base fuel axes p D same hp hr hs depth pinSize
  have qty:=TraceReceiverTemplate.count_bound D.machine D.fit D.field D.state (by omega) hp hr hs (by omega)
  have upper : start w+libraryWords D.block (64*w)≤gateBase D := by
    simpa only [start, gateBase, GridDescription.sector, same] using place.2
  have word : start w+libraryWords D.block (64*w)<2^(64*w) := by
    simpa only [start, same] using bound.2
  exact ⟨by omega,qty.trans size,(Nat.add_le_add_left pinSize _).trans place.1,upper,word⟩

/-- One fixed polynomial covers both word-packing scans and the native mask
scan, uniformly over all evaluator tapes and their assigned local bits. -/
theorem eventual_work (B : Block F) : ∀ᶠ w : ℕ in Filter.atTop,
    ∀ {pc regs slots S base fuel axes : ℕ} (D : RunData F (64*w) pc regs slots S base fuel axes (w/2)),
      D.block=B → pc≤64*w → regs≤64*w → slots≤64*w → (axes+1)+w/2≤2*w+1 →
      decodeWork D+libWork D≤2^(w/100) := by
  let a:=326*TraceReceiverTemplate.coefficient+6
  let b:=326*GridStructuralHeader.libraryCoefficient B+6
  filter_upwards [TraceDistribution.polynomial_room (a+1024+b) 15,
    Filter.eventually_ge_atTop (Fintype.card F+7)] with w poly large
  intro pc regs slots S base fuel axes D same hp hr hs depth
  have pack : templateSize D*(5*(64*w)+6)+6≤a*(w+1)^15 :=
    TraceReceiverTemplate.work_bound D.machine D.fit D.field D.state (by omega) hp hr hs (by omega)
  have stage : libWork D≤b*(w+1)^15 := by
    simpa only [libWork,same,b] using TraceReceiverLibraryMount.work_bound B w
  have linear : w+1≤(w+1)^15 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<w+1) (by decide : 1≤15)
  have scan : TraceReceiverMaskLoop.work (64*w) (axes+1) (w/2) (dict D) (masks D)≤1024*(w+1)^15 := by
    rw [TraceReceiverMaskLoop.linear_work]
    unfold TraceReceiverMaskBanks.count
    omega
  calc
    _ ≤ a*(w+1)^15+1024*(w+1)^15+b*(w+1)^15 := Nat.add_le_add (Nat.add_le_add pack scan) stage
    _ = (a+1024+b)*(w+1)^15 := by ring
    _ ≤ _ := poly

end
end Hierarchy.TraceReceiverTablesMount

end OAI
