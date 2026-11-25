import OAI.Hierarchy.TaggedWidePackedWindowReads
import OAI.Hierarchy.TaggedWideWindowLocal
import OAI.Hierarchy.TaggedWideWindowFullLocal
import OAI.Hierarchy.TaggedWidePrintedCutReceipt
import OAI.Hierarchy.TaggedWideWindowPrintedCut

namespace OAI
/-! # Native local-program evaluation of the funded window cut -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProtocolRAMFrozenWindow ProtocolRAMSupergroupDirectory
open AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows ProtocolRAMEmit
open Tagged TaggedShorterBudget Tagged.WideStack ProtocolRAMReportedPorts
open TaggedShorterSupergroups Filter
open Computability.VPVNP.BurstRAM PrivateRAM
open Tagged.WideControlJoin ProtocolStackContraction CoreBoard.PhysicalTerm
open scoped Classical BigOperators Topology Fin.CommRing
set_option maxRecDepth 2048
attribute [local irreducible] Native.wordBits Nat.pow

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ C : ℝ} {u : ℝ→ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ)
local notation "jobs" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "geometry" => typeMenu κ A v.W m k jobs ell v.stage_positive (fun _=>short+ell)
local notation "menu" => (geometry).menu u δ ξ
local notation "roleCount" => copies k jobs
local notation "groupDir" x => stageDir (x).h v.W roleCount (2*roleCount)
  (show 2*roleCount≤2^(2*roleCount) from Nat.lt_two_pow_self.le)
local notation "portCount" x => 2^(superAddress v.W (2*roleCount) (x).h)
local notation "slotCountAt" x => purchaseSlots (x).h v.W k jobs ell

variable (x : WideParent κ A)
local notation "b" => (v.widePlacement x.h x.w).catalogue
variable (prices : v.PhysicalCounts u A δ ξ m) (positive : 0≤κ)
    (buy : ∀i : Fin (m+1),Purchased F (v.wideWindowMenu (κ := κ) (A := A) m ell short u δ ξ) x i (purchaseSlots x.h v.W k v.wideJobs ell)
      (purchaseCandidates x.h v.W k v.wideJobs (purchaseSlots x.h v.W k v.wideJobs ell) (((v.wideWindowMenu (κ := κ) (A := A) m ell short u δ ξ)).height i x)
        (purchaseModules v.W u δ ξ (v.wideWindowMenu (κ := κ) (A := A) m ell short u δ ξ) x i)) (purchaseModules v.W u δ ξ (v.wideWindowMenu (κ := κ) (A := A) m ell short u δ ξ) x i) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ (v.wideWindowMenu (κ := κ) (A := A) m ell short u δ ξ) x)
    (metadata : ∀i : Fin (m+1),1+((v.wideWindowMenu (κ := κ) (A := A) m ell short u δ ξ)).height i x+((v.wideWindowMenu (κ := κ) (A := A) m ell short u δ ξ)).height i x≤((v.wideWindowMenu (κ := κ) (A := A) m ell short u δ ξ)).payload i x)
    (π : Equiv.Perm (Fin (2^x.h))) (marks : Marks x.h v.W k v.wideJobs)
    (order : Fin ((v.widePlacement x.h x.w).catalogue).coreRows≃Edges v.sampler x.h (2^v.W) k)
    (size : v.wideJobs*(PurchaseFrozen.count x.h (2^v.W) k*
      PurchaseFrozen.paths x.h v.sampler.degree (publicTiles k v.W-1))=((v.widePlacement x.h x.w).catalogue).boughtRows)
    (raw : Fin ((v.widePlacement x.h x.w).catalogue).rows→ ProtocolRAMEmit.Row) (bits : Catalogue v.sampler π (publicTiles k v.W-1) marks→ℕ)
    («rec» : Alignment ((v.widePlacement x.h x.w).catalogue) v.sampler π (publicTiles k v.W-1) marks v.radius raw (fun j=>(raw j).width)
      (((v.widePlacement x.h x.w).catalogue).ordinal v.sampler π (publicTiles k v.W-1) marks order size))
    (read : ∀e,(raw ((((v.widePlacement x.h x.w).catalogue).ordinal v.sampler π (publicTiles k v.W-1) marks order size) e)).width=bits e)
    (R : ℕ) (paid : TermBudget p q Q Λ (2^x.h) x.w v.radius (∑_j:Columns x.h (2^v.W)×Fin k,R)
      (scaleOf v.sampler π (publicTiles k v.W-1) marks)
      (fun e=>(lenCode v.sampler π (publicTiles k v.W-1) marks v.radius e:ℝ)) (fun e=>(bits e:ℝ)/x.w))
    (keep : («rec».geometry x.w R).links.Keep (2^x.h))
    (idRead : ∀j,(raw j).link=j.val)
    (widthRoom : ∀j,(raw j).width≤2^ell*x.w)
    (port : Bool→ Fin ((v.widePlacement x.h x.w).catalogue).rows→ Fin (WideMemory.H x.h v.W k v.wideJobs))
    (anchor : {j : Fin ((v.widePlacement x.h x.w).catalogue).rows // 0< pieces (atScale (((v.widePlacement x.h x.w).catalogue).transport order) (fun _=>0) 0 raw) x.w j}×Bool ↪
      Fin (WideMemory.dir x.h v.W k v.wideJobs).groups × Fin (WideMemory.H x.h v.W k v.wideJobs))
    (owner : ∀j side,(anchor (j,side)).1.val=(raw j.val).group)
    (pin : ∀j side,(anchor (j,side)).2=port side j.val)
local notation "ins" => fun i : Fin (m+1) => v.printed_installed m ell short v.stage_positive prices positive x i
  (buy i) groupsFit (metadata i) π b marks order size raw bits «rec» read R paid keep idRead widthRoom
  port anchor owner pin
local notation "B" t => (ins t).bank
variable {Ex Se E H J Tail : Type} [Fintype Ex] [Fintype Se] [Fintype E] [Fintype H] [Fintype J] [Fintype Tail]
    (cap : E→ℕ) (tail : ((Bool × ((e:E) × Fin (cap e))) ⊕ (H ⊕ J)) ≃ Tail)
local notation "ord" => Equiv.sumCongr (Equiv.refl (Leaf.Pos (Leaf.banks ins))) tail
local notation "P" => Leaf.Pos (Leaf.banks ins) ⊕ Tail


variable (buffer : ℕ) (dated : WideCPU.Dated (events v.mesh).length) (wbits romStart tapeSize : ℕ)
local notation "l" => v.wideWindowProgramLayout x m ell short u δ ξ buffer dated wbits romStart
variable (gateRoom : v.GateRoom x.h x.w wbits (v.wideWindowProgramLayout x m ell short u δ ξ buffer dated wbits romStart) tapeSize)
local notation "cpu" => (v.wideGates x.h x.w wbits l tapeSize gateRoom).2
local notation "old" => atScale ((b).transport order) (fun _=>0) 0 raw
local notation "dirBase" => v.wideGroupROM x dated wbits romStart
local notation "tape" => v.wideWindowWords (W := Native.wordBits x.h (2^v.W) Native.copies) x m ell short u δ ξ buffer dated wbits romStart
local notation "dest" => CatalystArchive.TerminalLayout.destination (v.wideSignedPage x.h x.w
  (v.fixedTerminalStock (v.widePlacement x.h x.w) x.h x.w))
variable (t : Fin (m+1))
local notation "fmt" => (l).windows t
local notation "src" => (l).inputs t
local notation "start" => (fmt).window.base ((l).windowBase t)
variable (mem before : Memory (Native.wordBits x.h (2^v.W) Native.copies)) (fit : ((v.wideWindowProgramLayout x m ell short u δ ξ buffer dated wbits romStart).windows t).Limits (Native.wordBits x.h (2^v.W) Native.copies) (atScale (((v.widePlacement x.h x.w).catalogue).transport order) (fun _=>0) 0 raw))
    (retain : ∀j,(v.wideGroupROM x dated wbits romStart)≤ j → j< (v.wideGroupROM x dated wbits romStart)+2*span (WideMemory.dir x.h v.W k v.wideJobs).groups → @Eq (Word (Native.wordBits x.h (2^v.W) Native.copies)) (before j) ((v.wideWindowWords (W := Native.wordBits x.h (2^v.W) Native.copies) x m ell short u δ ξ buffer dated wbits romStart) mem j))
    (initial : Memory (Native.wordBits x.h (2^v.W) Native.copies))
    (reported : ∀a,(CatalystArchive.TerminalLayout.destination (v.wideSignedPage x.h x.w (v.fixedTerminalStock (v.widePlacement x.h x.w) x.h x.w)))≤ a → a< (CatalystArchive.TerminalLayout.destination (v.wideSignedPage x.h x.w (v.fixedTerminalStock (v.widePlacement x.h x.w) x.h x.w)))+9*((v.widePlacement x.h x.w).catalogue).rows → @Eq (Word (Native.wordBits x.h (2^v.W) Native.copies)) (before a) (ProtocolRAMEmit.emitted (CatalystArchive.TerminalLayout.destination (v.wideSignedPage x.h x.w (v.fixedTerminalStock (v.widePlacement x.h x.w) x.h x.w))) raw initial a))
    (rowsFit : 3*((v.widePlacement x.h x.w).catalogue).rows<2^(Native.wordBits x.h (2^v.W) Native.copies))
    (portsRead : ∀side (j : ProtocolRAMPackedPlacement.Live (atScale (((v.widePlacement x.h x.w).catalogue).transport order) (fun _=>0) 0 raw) x.w),
      (if side then ((v.wideWindowProgramLayout x m ell short u δ ξ buffer dated wbits romStart).inputs t).right else ((v.wideWindowProgramLayout x m ell short u δ ξ buffer dated wbits romStart).inputs t).left).read before (j.val.val:Word (Native.wordBits x.h (2^v.W) Native.copies))=
        ((port side j.val).val*2^ell:ℕ))
local notation "groupRead" => fun j _=>v.wideWindow_owner_read (W := Native.wordBits x.h (2^v.W) Native.copies) x m ell short u δ ξ buffer dated wbits
  romStart t raw initial before reported rowsFit j
local notation "active" => fun j h=> (owner ⟨j,h⟩ false) ▸ (anchor (⟨j,h⟩,false)).1.isLt
local notation "actual" => v.wideCutAnchor x m ell short u δ ξ buffer dated wbits romStart
  t mem before old fit (ins t) retain active groupRead portsRead
local notation "inside" => v.wideWindow_observed (u:=u) (δ:=δ) (ξ:=ξ) x m ell short buffer
  (v.wideFormatROM x dated wbits romStart) l rfl (Nat.le_refl _) t
local notation "bound" => ((fmt).scatter_end ((l).windowBase t)).trans inside

section Program
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune
open WideCalendarSites

variable {X : Type} {d reserve M den : ℕ} {eventPin : Event → WireTelescope.CalendarTape.Slot X}
    {es : List Event} {state : Equiv.Perm (Row x.h) → X}
    (Z : CalendarTerms F x.h d k x.w reserve M den eventPin es state)
    {E₁ E₂ Hist : Type} [Fintype E₁] [Fintype E₂] [Fintype Hist]
    (privateOrder : E₁ ≃ E₂) (privateCap : E₂ → ℕ) (historyCap : Hist → ℕ) (dates view : ℕ)

local notation "groups" => (WideMemory.dir x.h v.W k v.wideJobs).groups
local notation "lanes" => 2^ell
local notation "data" => CalendarTerms.Shared (geometry).index privateCap historyCap groups
  (portCount x) lanes dates view x.w
local notation "rout" => Z.nativeRouting data
local notation "ex" => OpenPins x.h x.w (rout).catalyst
local notation "se" => Fin (rout).selectors
local notation "site" => Fin (siteLast x.h d k+1)
local notation "gates" => v.wideGates x.h x.w wbits l tapeSize gateRoom
local notation "nHist" => dates * Fintype.card ((j : Hist) × Fin (historyCap j))
local notation "endPins" => (Fin groups × Fin (portCount x)) × Fin view
local notation "numbering" => CalendarTerms.privateWorkspace (geometry).index privateOrder
  privateCap historyCap groups (portCount x) lanes dates view x.w
local notation "wordSize" => Native.wordBits x.h (2^v.W) Native.copies
local notation "liveBanks" => Leaf.banks (F := F) (T := Fin (m+1))
  («groups» := groups) («ports» := portCount x) («lanes» := lanes) (w := x.w) (m := m)
  (N := (b).rows) (cls := fun i : Fin (m+1) => i.val) (records := fun _ : Fin (m+1) => old) ins

set_option maxHeartbeats 600000 in
include prices positive buy groupsFit metadata π marks order size raw bits «rec» read R paid keep
  idRead widthRoom port anchor owner pin buffer dated wbits romStart tapeSize gateRoom t
  mem before fit retain initial reported rowsFit portsRead Z privateOrder privateCap historyCap dates view in
omit [Fintype E₁] in
/-- Evaluation of the literal purchased cut in the compiled local program. Both halves
of a private row follow its original board numbering, and the chronological bits pass
unchanged through that numbering. -/
theorem wideWindow_receipt_cut
    (head : (gates).1.Head → (ex ⊕ se) ⊕ Bool) (paidHead : (cpu).Head → (ex ⊕ se) ⊕ Bool)
    (flag pad privateGate plane timeline : Net F (SitePins ex se data cpu))
    (enter finish : site → Net F (SitePins ex se data cpu))
    (row : site → Fin es.length → Net F (SitePins ex se data cpu))
    (large : purchaseWordHeight v.W k v.wideJobs ell ≤ x.h)
    (out : Memory wordSize)
    (stored : ∀ q : (fmt).Cell,
      @Eq (Word wordSize) (out ((fmt).address ((l).windowBase t) q)) ((actual).word old q))
    (exterior : ex → Bool) (selectors : se → Bool)
    (z : ∀ i : Fin (m+1), (liveBanks i).Slots) (y : PrivatePorts (privateCap ∘ privateOrder))
    (hist : Fin nHist → Bool) (output : endPins → Bool) :
    let core := v.wideWindowLocalPrograms (u := u) (δ := δ) (ξ := ξ)
      x m ell short wbits buffer tapeSize dated romStart gateRoom Z privateCap historyCap dates view
      head paidHead flag pad privateGate plane timeline enter finish row large
    ((buy t).cut (core.read t)).closed
      (CalendarTerms.readPins («B» := cpu) numbering exterior selectors ((cpu).terminal out)
        (Leaf.write liveBanks (privateCap ∘ privateOrder) z y hist output)) =
      (liveBanks t).settings.close (z t) := by
  intro core
  let tailOrder := Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl Bool)
      (Equiv.sigmaCongrLeft (β := fun e => Fin (privateCap e)) privateOrder))
    (Equiv.refl (Fin nHist ⊕ endPins))
  exact v.wideWindow_printed_cut (Ex := ex) (Se := se) m ell short x prices positive
    buy groupsFit metadata π marks order size raw bits «rec» read R paid keep idRead widthRoom
    port anchor owner pin (privateCap ∘ privateOrder) tailOrder buffer dated wbits romStart
    tapeSize gateRoom t mem before fit retain initial reported rowsFit portsRead
    large out stored exterior selectors z y hist output

private theorem extend_output_word {n w : ℕ} (widthEq : n=w) (m : Memory n) (a val : ℕ)
    (h : m a=(val:Word n)) : (cast (congrArg Memory widthEq) m) a=(val:Word w) := by
  subst w
  exact h

set_option maxHeartbeats 600000 in
include prices positive buy groupsFit metadata π marks order size raw bits «rec» read R paid keep
  idRead widthRoom port anchor owner pin buffer dated wbits romStart t mem before fit retain
  initial reported rowsFit portsRead Z privateOrder privateCap historyCap dates view in
omit [Fintype E₁] in
/-- The final dense gate can include later signed replay and spill phases. Its physical
observation of the original window is sufficient for the same purchased cut. -/
theorem wideWindow_receipt_cut_at
    (large : purchaseWordHeight v.W k v.wideJobs ell ≤ x.h)
    (first fullGate : Gate)
    (firstHead : first.Head → (ex ⊕ se) ⊕ Bool) (fullHead : fullGate.Head → (ex ⊕ se) ⊕ Bool)
    (atFlag : Fin first.u)
    (keepNet padNet freeNet planeNet timelineNet : Net F (SitePins ex se data fullGate))
    (enterNet finishNet : site → Net F (SitePins ex se data fullGate))
    (rowNet : site → Fin es.length → Net F (SitePins ex se data fullGate))
    (upper : (l).pruneScratch+(l).pruneRows+1 ≤ fullGate.u)
    (widthEq : wordSize = fullGate.W)
    (dense : ∀ i, (fullGate.addr i).val=i.val)
    (out : Memory wordSize)
    (stored : ∀ q : (fmt).Cell,
      @Eq (Word wordSize) (out ((fmt).address ((l).windowBase t) q)) ((actual).word old q))
    (exterior : ex → Bool) (selectors : se → Bool)
    (z : ∀ i : Fin (m+1), (liveBanks i).Slots) (y : PrivatePorts (privateCap ∘ privateOrder))
    (hist : Fin nHist → Bool) (output : endPins → Bool) :
    let program := v.wideWindowLocalProgramsAt (u := u) (δ := δ) (ξ := ξ)
      x m ell short wbits buffer dated romStart Z privateCap historyCap dates view first fullGate
      firstHead fullHead atFlag keepNet padNet freeNet planeNet timelineNet enterNet finishNet rowNet
      upper widthEq.le large
    ((buy t).cut (program.read t)).closed
      (CalendarTerms.readPins («B» := fullGate) numbering exterior selectors
        (fullGate.terminal (cast (congrArg Memory widthEq) out))
        (Leaf.write liveBanks (privateCap ∘ privateOrder) z y hist output)) =
      (liveBanks t).settings.close (z t) := by
  intro program
  let tailOrder := Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl Bool)
      (Equiv.sigmaCongrLeft (β := fun e => Fin (privateCap e)) privateOrder))
    (Equiv.refl (Fin nHist ⊕ endPins))
  apply v.printed_cut_receipt (gate := fullGate) (Ex := ex) (Se := se)
    m ell short v.stage_positive prices positive x buy groupsFit metadata
    π b marks order size raw bits «rec» read R paid keep idRead widthRoom port anchor owner pin
    (privateCap ∘ privateOrder) tailOrder t start ((bound).trans upper)
    ((purchase_word_fit (u := u) (δ := δ) (ξ := ξ) v.W m k v.wideJobs ell short
      v.stage_positive x large t).trans widthEq.le)
    (cast (congrArg Memory widthEq) out) (by rw [← widthEq]; exact (by omega : 1 < 10).trans_le fit.small) _
    exterior selectors z y hist output
  intro field
  rw [dense]
  apply extend_output_word widthEq
  exact (stored (.inr field)).trans
    ((fmt).originalAnchor_field (W := wordSize) (portCount x) lanes src old before fit (ins t)
      (v.wideWindow_live_sources (W := wordSize) x m ell short u δ ξ buffer dated wbits romStart mem before t
        old fit retain (ins t).port active groupRead portsRead).1
      active
      (v.wideWindow_live_sources (W := wordSize) x m ell short u δ ξ buffer dated wbits romStart mem before t
        old fit retain (ins t).port active groupRead portsRead).2 field)


end Program


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
