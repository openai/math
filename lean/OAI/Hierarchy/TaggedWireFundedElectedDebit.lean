import OAI.Hierarchy.TaggedWireFundedTargetStage
import OAI.Hierarchy.TaggedWireElectedDebitWire
import OAI.Hierarchy.TaggedWireChosenStripSource

namespace OAI
/-! # Native padded debits on the same original row as the reference ballot operator -/
noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit PurchaseStage RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical Fin.CommRing

variable {A B C H F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype H] [Field F]
  {k sites N w q D z d : ℕ} [Nonempty (Fin sites)] [Nonempty (Fin k)] [Nonempty (Role C H (A⊕B) k)]
  {M ε tree : ℝ} {len : H→ℝ} {cap : A→ℝ}

variable {e : Role C H (A⊕B) k → Chord sites}

namespace StripInput
variable {menu : Probe.FixedMenu F e
    (demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap)
    ε tree N}
  (x : _root_.OAI.Hierarchy.ProtocolRAM.CatalystArchive.StripInput (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) menu w z d q D)



omit [Nonempty (Fin k)] in
private theorem aligned_debit_ordinal (f : Format z d k q D) (b : Batch q D) (m : Memory w)
    (formEq : x.form=f) (ballotEq : x.ballot=b) (memoryEq : x.mem=m)
    (i : Fin f.market.rows) (port : Fin D) :
    ((x.alignedPlan f b m formEq ballotEq memoryEq).enum ⟨i,port⟩).val = port.val + D * i.val := by
  subst f b m
  rfl
end StripInput
end Hierarchy.ProtocolRAM.CatalystArchive

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Strip WireTelescope CatalystArchive StockCommit RepairHistogram
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor Probe ChosenPackets RowRouting
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped BigOperators Classical Fin.CommRing

variable {k n K w : ℕ} {A B Ball F : Type}
  [Field F] [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
variable {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
local notation "roles" => ColumnWires.ends (horizontal n) extra
variable (labels : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (rt : Fin (Fintype.card (TreeSite n k)))
  {N z rawD D : ℕ} [Nonempty (Fin (Fintype.card (TreeSite n k)))] [Nonempty (Fin k)]
  [Nonempty (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)]
  {M ε tree : ℝ} {len : Fin n→ℝ} {cap : A→ℝ}
local notation "req" => ColumnWires.demand (I:=C) (H:=Fin n) (k:=k) (Sum.inl (α:=A) (β:=B))
variable {menu : Probe.FixedMenu F
    (fun e : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k =>
      @DistinctPair.chord _ _ ⟨labels⟩ (ColumnWires.ends (horizontal n) extra e))
    (ColumnWires.demand (I:=TreeColumn n) (H:=Fin n) (k:=k) (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => ColumnWires.quote (I:=TreeColumn n) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) ''
      Set.Icc 0 cap) ε tree N}
  (i : menu.index) {q : ℕ} (x : StripInput menu w z rawD q D)

  (form : Format z rawD k q D) (batch : Batch q D) (tape : Memory w)
  (formEq : x.form = form) (ballotEq : x.ballot = batch) (memEq : x.mem = tape)
  (j : Fin form.market.rows) (live : j∈StockCommit.liveRows batch tape form.market.rows)
  (arity : (batch.termCount.read tape (batch.packet.eval tape (j.val : Word w))).val = (menu.packet i).terms)
  (selected : (batch.packet.eval tape (j.val : Word w)).val = (Fintype.equivFin menu.index i).val+1)
  (pad : Chord K) (bound : (menu.packet i).terms≤q)
local notation "needs" => (fun z : PositiveDemand req i.val.val=>req z.val)
local notation "Q" => stripPacket labels roles needs place u rt (menu.packet i)
local notation "wire" => stripDebitWire (D:=D) pad (reportedRole place roles u)

include live arity selected bound in
omit [Fintype Ball] [Nonempty (Fin k)] in
private theorem native_debit_widths : (Q).wants batch.copies = Probe.optionWidths wire (fun port =>
    consumedBits (fresh form.pricedArea form.stockSource).columns tape
      ((x.alignedPlan form batch tape formEq ballotEq memEq).enum ⟨j,port⟩)) := by
  subst form batch tape
  exact chosen_strip_source labels rt i x j live arity selected pad bound
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

set_option quotPrecheck false
set_option hygiene false
set_option cleanup.letToHave false
set_option maxRecDepth 12000
set_option maxHeartbeats 650000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open Filter Strip StripDirectory ChosenPackets RepairHistogram PurchaseFrozen
open LinearAlgebra.SpectralBooks ChordGraph
open CalendarTape StockCommit ProtocolRAM.PurchaseStage ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "boards" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger boards v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h


local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "f" => v.nativeFormats P h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "slots" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "order" => wideRouteOrder h D k


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h D) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "mid" => v.wideSignedMidAt h width size stock M π order

local notation "funded" => v.wideFundedRaw h width v.maxBits seed
local notation "original" => v.wideSignedWords h width stock v.radius π.symm order funded
local notation "V" => v.catalystMarkets P h width
local notation "input" => fun _ : Equiv.Perm (Row h)=>original
local notation "dims" => v.wide_stock_sizes h width age budget small
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

local notation "slab" => v.slab (v.seed P h width) P width
local notation "EF" => Slab.effects slab boards F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
  (P).catalogue banks source table target owners
local notation "pageRoom" => v.original_selector_room P h width (dims).words.addresses
local notation "copyRoom" => v.original_copy_room P h width r banks source table target owners (dims).copies
local notation "floorE" e => (A).base v.mesh e
local notation "ceilE" e => (A).base v.mesh e+(A).stride
local notation "top" => (A).endAddress v.mesh


namespace FundedDate
variable {v h width size π seed age budget small} {a : Attempt} {tail x}
    {t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x} {c : (slots (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
    (extent : (A).endAddress v.mesh≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
local notation "entry" => run C H.prior (origin H.code)
local notation "b" => ProtocolRAM.PurchaseStage.enabledBatch ((C).layout a) (repair C a)
local notation "snap" y => HistogramShelf.snapshot C a y
local notation "paid" => v.stage P h width r banks source table target owners a entry
local notation "format" => (reader).format
local notation "signal" i => (b).selected (snap x) ((i).val:Word w)
local notation "I" => Fin ((C).layout a).candidates


local notation "ar" => (v.nativeFormats P h width a).pricedArea
local notation "s₀" => (v.nativeFormats P h width a).stockSource
local notation "st" => v.taskCommit P h width a
local notation "tag" => RepairHistogram.kind (goods:=(ar).goods) (st).plan.bank (st).columns paid
local notation "credits" => RepairHistogram.installedBits (n:=(ar).occurrences) (st).columns paid
local notation "readback" => H.readbackRun extent tall floor
local notation "co" => checkedOut C ((A).endAddress v.mesh) (origin H.code)
local notation "ids" => (repair C a).keys
local notation "head" => StripChart.header F (v.nativeBoards P h width) a
local notation "bought" => v.nativeFormats P h width


local notation "goods" => Commodity (Fin (2^h)) N k
local notation "dates" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "ord" => v.nativeSlots P h width a
local notation "cat" => (P).catalogue
local notation "plan" => H.stripPlan extent tall floor (dims).strip

variable {mark : Marks h v.W k dates} {earlier : Memory w}
    {ends : Fin (cat).rows→Site h D k×Site h D k} [Nonempty (Fin k)] {number : ℕ}
    (sourceRow : v.ElectedSource h width π.symm mark ends earlier a number)
    (i : I) (hit : signal i) (atom : v.widePacketMenuIndex h a) (rt : Fin (v.wideBallotParties h a))
    (pad : Chord (siteLast h D k+1)) (bound : (sourceRow.placed atom rt).data.terms≤v.menu.alphabet)
    (arity : ((b).termCount.read paid ((b).packet.eval paid (i.val:Word w))).val=v.widePacketTerms h a atom)
    (code : ((b).packet.eval paid (i.val:Word w)).val=v.widePacketNumber h a atom)

include extent tall floor hit bound arity code in
omit [Nonempty (Fin k)] in
theorem routed_debit_row :
    (sourceRow.placed atom rt).wants (b).copies=Probe.optionWidths (sourceRow.debitWire pad)
      (fun port=>consumedBits (st).columns paid ((plan).enum ⟨i,port⟩)) := by
  have on:=(H.priced_row_iff extent tall floor i).2 hit
  cases sourceRow with
  | payload ph tr record index address witness material =>
    let a := Attempt.outer ph tr
    let fit:=v.payload_paid_fit P h width r banks source table target owners ph tr (origin H.code)
      entry H.prior _ H.cut (readback).resident (dims).strip small
    let raw:=v.payloadStageInput P h width r banks source table target owners ph tr entry fit
    have rawBound : ((v.payloadPacketMenu N).packet atom).terms ≤ (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet :=
      bound.trans_eq (v.catalogue_words (v.seed P h width) width).1.symm
    let _ : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
    let _ : Nonempty (Fin (v.wideBallotParties h (.outer ph tr))) := ⟨rt⟩
    have realized := native_debit_widths (k:=k) (n:=PayloadStrip.edgeCount N)
      (extra:=LocalCommodity.extraEnds (PayloadStrip.commodity N k) (PayloadStrip.noProbe N))
      (place:=SiteDirectory.payloadParties (d:=D) (k:=k) π.symm) (u:=record) (menu:=v.payloadPacketMenu N)
      SiteNaming.labels rt atom raw (v.nativeFormats P h width a) (b) paid
      (v.payloadStage_format P h width r banks source table target owners ph tr entry fit)
      (v.payloadStage_ballot P h width r banks source table target owners ph tr entry fit)
      (v.payloadStage_memory P h width r banks source table target owners ph tr entry fit)
      i on arity code pad rawBound
    have samePlan : plan = raw.alignedPlan (v.nativeFormats P h width a) (b) paid
        (v.payloadStage_format P h width r banks source table target owners ph tr entry fit)
        (v.payloadStage_ballot P h width r banks source table target owners ph tr entry fit)
        (v.payloadStage_memory P h width r banks source table target owners ph tr entry fit) := rfl
    simp only [samePlan, ElectedSource.placed, ElectedSource.debitWire, FixedProtocolFormat.taskCommit, a] at realized ⊢
    refine Eq.trans ?_ (realized.trans ?_)
    · rfl
    · refine congrArg₂ Probe.optionWidths ?_ ?_
      · funext port
        rfl
      · funext port
        apply congrArg (consumedBits (n:=(st).occurrences) (st).columns paid)
        apply Fin.ext
        trans port.val + max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)) * i.val
        · apply StripInput.aligned_debit_ordinal (x:=raw)
        · symm
          apply StripInput.aligned_debit_ordinal (x:=raw)
  | purchased ph tr sj it hp ht unique path index address witness material =>
    let a := Attempt.inner ph tr sj it
    let fit:=v.purchased_paid_fit P h width r banks source table target owners ph tr sj it (origin H.code)
      entry H.prior _ H.cut (readback).resident (dims).strip small
    let raw:=v.purchasedStageInput P h width r banks source table target owners ph tr sj it entry fit
    have rawBound : (v.purchasePacketMenu.packet atom).terms ≤ (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet :=
      bound.trans_eq (v.catalogue_words (v.seed P h width) width).1.symm
    let _ : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
    let _ : Nonempty (Fin (v.wideBallotParties h (.inner ph tr sj it))) := ⟨rt⟩
    have realized := native_debit_widths (k:=k) (n:=ChainStrip.edgeCount v.depth)
      (extra:=LocalCommodity.extraEnds (ChainStrip.commodity v.depth k) (ChainStrip.probe v.depth))
      (place:=SiteDirectory.boughtParties π.symm v.sampler (mark (v.earnedDay ph tr hp ht)) (unique _))
      (u:=path) (menu:=v.purchasePacketMenu) SiteNaming.labels rt atom raw (v.nativeFormats P h width a) (b) paid
      (v.purchasedStage_format P h width r banks source table target owners ph tr sj it entry fit)
      (v.purchasedStage_ballot P h width r banks source table target owners ph tr sj it entry fit)
      (v.purchasedStage_memory P h width r banks source table target owners ph tr sj it entry fit)
      i on arity code pad rawBound
    have samePlan : plan = raw.alignedPlan (v.nativeFormats P h width a) (b) paid
        (v.purchasedStage_format P h width r banks source table target owners ph tr sj it entry fit)
        (v.purchasedStage_ballot P h width r banks source table target owners ph tr sj it entry fit)
        (v.purchasedStage_memory P h width r banks source table target owners ph tr sj it entry fit) := rfl
    simp only [samePlan, ElectedSource.placed, ElectedSource.debitWire, FixedProtocolFormat.taskCommit, a] at realized ⊢
    refine Eq.trans ?_ (realized.trans ?_)
    · rfl
    · refine congrArg₂ Probe.optionWidths ?_ ?_
      · funext port
        rfl
      · funext port
        apply congrArg (consumedBits (n:=(st).occurrences) (st).columns paid)
        apply Fin.ext
        trans port.val + max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)) * i.val
        · apply StripInput.aligned_debit_ordinal (x:=raw)
        · symm
          apply StripInput.aligned_debit_ordinal (x:=raw)

variable {c' : (slots (.attempt a)).choice x} (ref : v.FundedDate h width size π seed age budget small t c')
local notation "fixed" => ref.packetAt extent tall floor i hit
local notation "root" => v.wideBallotRoot h a
local notation "fmt" => (reader).format

omit [Nonempty (Fin k)] in
theorem same_debit_row : (ref.row extent tall floor i).input=Probe.optionWidths ((fixed).installed.debitWire pad)
    (fun port=>consumedBits (st).columns paid ((plan).enum ⟨i,port⟩)) := by
  let view:=(v.funded_ballot_views h width size extent π seed age budget small t c').1
  have letters:=(view.1 i).trans ((fixed).arity root).symm
  have bound : ((fixed).menu root).data.terms≤v.menu.alphabet:=letters ▸ ((fmt).width a x i).trans_eq (v.catalogue_words (v.seed P h width) width).1
  have positive:=(Probe.NativeHistogram.alphabet_pos ((fixed).menu root).data).trans_le bound
  have seen:=H.priced_election extent tall floor i fixed positive
  have elected : (ref.row extent tall floor i).input = ((fixed).menu root).wants (b).copies :=
    (fmt).electedRow_source a x x view
      (fun j active => (ref.packetAt extent tall floor j active).menu root)
      (fun j active => (ref.packetAt extent tall floor j active).arity root) i hit
  exact elected.trans
    (routed_debit_row (H:=H) (extent:=extent) (tall:=tall) (floor:=floor) (sourceRow:=(fixed).installed)
      (i:=i) (hit:=hit) (atom:=(fixed).atom) (rt:=root) (pad:=pad) (bound:=bound) (arity:=seen.2) (code:=seen.1))

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
