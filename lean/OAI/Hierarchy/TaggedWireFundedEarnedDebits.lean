import OAI.Hierarchy.TaggedWireFundedEarnedCredits
import OAI.Hierarchy.TaggedWireChosenStripDebit
import OAI.Hierarchy.TaggedWireElectedDebitWire
import OAI.Hierarchy.TaggedWireFundedDebitDate

namespace OAI
/-! # Classifying the two kinds of physical debit on an actual elected funded row -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Strip WireTelescope CatalystArchive StockCommit RepairHistogram PurchaseStage
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor Probe ChosenPackets RowRouting StripPaths PacketTurns
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical Fin.CommRing

variable {sam : PurchaseSampler} {h d k n K w : ℕ} {A B Ball F : Type} [Field F] [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "Good" => Commodity (Fin (2^h)) (Stages h d) k
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
    {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
    {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K} {addr : A → Commodity (Fin (2^h)) (Stages h d) k}
    {m : Memory w} {reg : Word w}
local notation "roles" => ColumnWires.ends (horizontal n) extra
local notation "line" => reportedRole place roles u
variable (g : EarnedInstall p b π extra place u endRow name addr m reg)
  {sites N z rawD D : ℕ} [Nonempty (Fin sites)] [Nonempty (Fin k)] [Nonempty (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)]
  {M ε tree : ℝ} {len : Fin n→ℝ} {cap : A→ℝ}
local notation "req" => ColumnWires.demand (I:=C) (H:=Fin n) (k:=k) (Sum.inl (α:=A) (β:=B))
variable {e : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k → Chord sites}
    {menu : Probe.FixedMenu F e
      (ColumnWires.demand (I:=TreeColumn n) (H:=Fin n) (k:=k) (Sum.inl (α:=A) (β:=B)))
      ((fun y:A→ℝ => ColumnWires.quote (I:=TreeColumn n) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) ''
        Set.Icc 0 cap) ε tree N}
    (i : menu.index) {q : ℕ} (x : StripInput menu w z rawD q D)
    (nativeForm : Format z rawD k q D) (batch : Batch q D) (tape : Memory w)
    (formEq : x.form = nativeForm) (batchEq : x.ballot = batch) (tapeEq : x.mem = tape)
    (j : Fin nativeForm.market.rows) (live : j∈liveRows batch tape nativeForm.market.rows)
    (arity : (batch.termCount.read tape (batch.packet.eval tape (j.val:Word w))).val=(menu.packet i).terms)
    (selected : (batch.packet.eval tape (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1)
local notation "hdr" => (⟨x.start,nativeForm.market.rows,D⟩ : PortHeader)
local notation "a" => nativeForm.pricedArea
local notation "s" => nativeForm.stockSource
local notation "st" => fresh a s
local notation "keyMap" => pairKeys (Columns h d) k
variable {payload : ℕ} {chart : Chart w q D} {ev : Attempt} {before : Memory w}
local notation "recover" col => CatalystArchive.select (D:=D) (hdr).fieldTerm (hdr).ballTerm
  (ownerExpr (H:=Fin n) (E:=A⊕B) (k:=k) col)

omit [Nonempty (Fin k)] in
private theorem native_debit_index (port : Fin D) :
    ((x.alignedPlan nativeForm batch tape formEq batchEq tapeEq).enum ⟨j,port⟩).val =
      port.val + D*j.val := by
  subst nativeForm batch tape
  rfl

include g live arity selected formEq batchEq tapeEq in
set_option maxHeartbeats 2000000 in
omit [Fintype Ball] [Nonempty (Fin k)] in
private theorem EarnedInstall.aligned_chosen_debit (bound : (menu.packet i).terms≤q) (column : C→Expr)
    (date : CatalystArchive.Date chart ev before (recover column) ((a).direct+(a).occurrences) (a).occurrences
      (Fintype.card (Columns h d)*k) payload)
    (labels : LabelSource) (physical : chart.commit ev=pricedSegment a s labels w batch)
    (ready : Calendar.ready chart (.attempt ev) before) (board : EventBoard st w)
    (stage : tape=stageInput a s labels (postOutput (chart.layout ev) (repair chart ev) (prepared chart ev before)))
    (wide : payload<2^w) (keyRoom : Fintype.card (Columns h d)*k≤2^w) (head : (hdr).Loaded before)
    (colWord : ∀c,(column c).eval before (j.val:Word w)=(p.column c).eval m reg)
    (code : Good≃Fin nativeForm.pricedArea.goods) (slots : ∀u,(x.addr u).eval tape (j.val:Word w)=
      ((code (addr u)).val:Word w)) (pad : Chord K) (v : Fin D) (occ : Fin nativeForm.pricedArea.occurrences)
    (indexEq : occ.val = v.val+D*j.val) :
    let debit:=consumedBits (st).columns tape occ
    Finsupp.single (stripDebitWire pad line v) debit=
      (kind (goods:=(a).goods) (st).plan.bank (st).columns tape occ).elim 0 (fun good=>(ordinalGoods π name code).chordWidth good debit)+
      (catalystGraph name).chordWidth ((keyMap).symm (date.entry.owner (Fin.cast date.shape.symm occ)))
        (date.entry.bits (Fin.cast date.shape.symm occ)) := by
  subst nativeForm batch tape
  have same : x.plan.enum ⟨j,v⟩ = occ := Fin.ext indexEq.symm
  subst occ
  exact g.chosen_strip_debit (menu:=menu) i x j live arity selected bound column date labels physical ready board stage wide keyRoom head colWord code slots pad v

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open Filter Strip StripDirectory ChosenPackets RepairHistogram PurchaseFrozen
open LinearAlgebra.SpectralBooks ChordGraph
open CalendarTape StockCommit PurchaseStage ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h


local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "slots" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "order" => wideRouteOrder h D k


variable (size : ℕ) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h (2^v.W)) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
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
local notation "EF" => Slab.effects slab s F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
  (P).catalogue banks source table target owners
local notation "pageRoom" => v.original_selector_room P h width (dims).words.addresses
local notation "copyRoom" => v.original_copy_room P h width r banks source table target owners (dims).copies
local notation "floorE" e => (A).base v.mesh e
local notation "ceilE" e => (A).base v.mesh e+(A).stride
local notation "top" => (A).endAddress v.mesh


namespace FundedDate
variable {v h width size π seed age budget small} {a : Attempt} {tail : List Event}
    {x : Memory (Native.wordBits h (2^v.W) Native.copies)}
    {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt a::tail) x} {c : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
    (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
local notation "entry" => run C H.prior (origin (H.code))
local notation "b"  => PurchaseStage.enabledBatch ((C).layout a) (repair C a)
local notation "snap" y:arg => HistogramShelf.snapshot C a y
local notation "paid" => v.stage P h width r banks source table target owners a entry
local notation "format" => (reader).format
local notation "signal" i:arg => (b).selected (snap x) ((i).val:Word w)
local notation "I" => Fin ((C).layout a).candidates


local notation "ar" => (v.nativeFormats P h width a).pricedArea
local notation "s₀" => (v.nativeFormats P h width a).stockSource
local notation "st" => v.taskCommit P h width a
local notation "tag" => RepairHistogram.kind (goods:=(ar).goods) (st).plan.bank (st).columns paid
local notation "credits" => RepairHistogram.installedBits (n:=(ar).occurrences) (st).columns paid
local notation "currentReadback" => H.readbackRun extent tall floor
local notation "co" => checkedOut C ((A).endAddress v.mesh) (origin (H.code))
local notation "ids" => (repair C a).keys
local notation "head" => StripChart.header F (v.nativeBoards P h width) a
local notation "bought" => v.nativeFormats P h width


local notation "goods" => Commodity (Fin (2^h)) N k
local notation "dates" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "ord" => v.nativeSlots P h width a
local notation "stamp" => v.stamp P h width r banks source table target owners a
local notation "mask" => v.earnedClass P h width a
local notation "mate" => v.earnedMate P h width a
local notation "ct" => (A).base v.mesh (.attempt a)
local notation "cat" => (P).catalogue
local notation "plan" => H.stripPlan extent tall floor (dims).strip
local notation "prim" e:arg => primaryHit (ar) (s₀) stamp paid co e
local notation "second" e:arg => secondaryHit (ar) (s₀) mask mate paid co e
local notation "eventPorts" => StripChart.header F (v.nativeBoards P h width) a

local notation "account" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea bits stride)
local notation "take" => RepairHistogram.consumedBits (n:=(ar).occurrences) (st).columns paid
local notation "name" => (siteNumber h D k).toEmbedding
local notation "keys" => pairKeys (Columns h D) k
local notation "portCount" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))

variable {mark : Marks h v.W k dates} {previous : Memory w}
    {ends : Fin (cat).rows→Site h D k×Site h D k} [Nonempty (Fin k)]
    {rowIdx : ℕ} (srcRow : v.ElectedSource h width π.symm mark ends previous a rowIdx)
    (i : I) (atRow : rowIdx=i.val) (hit : signal i)
    (atom : v.widePacketMenuIndex h a)
    (arity : ((b).termCount.read paid ((b).packet.eval paid (i.val:Word w))).val=v.widePacketTerms h a atom)
    (selected : ((b).packet.eval paid (i.val:Word w)).val=v.widePacketNumber h a atom)
    (bound : v.widePacketTerms h a atom≤v.menu.alphabet)
    (stageLow : PrefixAgreement.Low ct paid previous) (oldLow : PrefixAgreement.Low ct entry previous)
    (day : CatalystArchive.Date C a entry ((account).term (.attempt a)) ((ar).direct+(ar).occurrences) (ar).occurrences num width)
    (keyRoom : num≤2^w) (pad : Chord (siteLast h D k+1)) (vPort : Fin portCount)

include hit atRow extent tall floor stageLow oldLow selected arity bound keyRoom in
omit [Nonempty (Fin k)] in
theorem routed_debits :
    let occ:=(plan).enum ⟨i,vPort⟩
    let amount:=take occ
    Finsupp.single (srcRow.debitWire pad vPort) amount=
      (tag occ).elim 0 (fun g=>(CoreBoard.ordinalGoods π.symm name (ord)).chordWidth g amount)+
      (catalystGraph name).chordWidth ((keys).symm (day.entry.owner (Fin.cast day.shape.symm occ)))
        (day.entry.bits (Fin.cast day.shape.symm occ)) := by
  have evt : Event.attempt a ∈ events v.mesh := by
    have tapeEq : events v.mesh = H.prior ++ .attempt a :: tail := H.cut.events
    rw [tapeEq]
    simp
  have room : ct<2^w:=((Nat.le_add_right ..).trans ((A).within v.mesh (.attempt a) evt)).trans_lt (currentReadback).endFits
  have fits:=v.wide_earned_before h width a room
  have layout:=((currentReadback).boards a evt).1
  have board:=eventBoard (ar) (s₀) (b) layout.inputs layout.window.room
  have live:=(H.priced_row_iff extent tall floor i).2 hit
  have loaded : (eventPorts).Loaded entry := by
    have headerEq : eventPorts=(v.publicHeader P h width).ports.header 0 := by
      cases a <;> simp only [PortROM.Table.header,Fin.val_zero,Nat.zero_mul,Nat.add_zero] <;> rfl
    have past : (eventPorts).stop≤ ct:=headerEq ▸ (((v.publicHeader P h width).ports.end_le 0).trans
      ((v.stock_port_room P h width).trans (Nat.le_add_right ..)))
    exact (H.checkout_ports extent tall floor).frame (fun z _ hz=>
      (H.before z (hz.trans_le past)).symm.trans (H.checkout_input z (hz.trans_le past)).symm)
  cases srcRow with
  | payload ph tr record idx orig g material=>
    subst atRow
    let a:=Attempt.outer ph tr
    let _ : Nonempty (PayloadRole N k):=⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
    let _ : Nonempty (Fin (v.wideBallotParties h a)):=⟨v.wideBallotRoot h a⟩
    let shape:=v.payload_paid_fit P h width r banks source table target owners ph tr (origin (H.code))
      entry H.prior _ H.cut (currentReadback).resident (dims).strip small
    let x0:=v.payloadStageInput P h width r banks source table target owners ph tr entry shape
    let p0:=v.payloadPricePorts P h width
    have addr (u : PayloadStrip.Quotes N k) : (x0.addr u).eval paid (i.val:Word w)=
        (((ord) (PayloadStrip.rowAddress record u)).val:Word w) :=
      ((StripPorts.OriginalFits.read fits stageLow).stock u (i.val:Word w)).trans (material u)
    have samePlan : plan = x0.alignedPlan (v.nativeFormats P h width a) (b) paid
        (v.payloadStage_format P h width r banks source table target owners ph tr entry shape)
        (v.payloadStage_ballot P h width r banks source table target owners ph tr entry shape)
        (v.payloadStage_memory P h width r banks source table target owners ph tr entry shape) := rfl
    have occVal : ((plan).enum ⟨i,vPort⟩).val = vPort.val + portCount*i.val := by
      rw [samePlan]
      apply native_debit_index (x:=x0)
    have result := g.aligned_chosen_debit (menu := v.payloadPacketMenu N) atom x0 (v.nativeFormats P h width a) (b) paid
      (v.payloadStage_format P h width r banks source table target owners ph tr entry shape)
      (v.payloadStage_ballot P h width r banks source table target owners ph tr entry shape)
      (v.payloadStage_memory P h width r banks source table target owners ph tr entry shape)
      i live arity selected (bound.trans_eq (v.catalogue_words (v.seed P h width) width).1.symm)
      p0.column day stamp rfl H.cut.currentReady board rfl (dims).widthFit keyRoom loaded
      (fun u=>(StripPorts.OriginalFits.read fits oldLow).column u (i.val:Word w)) (ord) addr pad vPort ((plan).enum ⟨i,vPort⟩) occVal
    simp only [ElectedSource.debitWire, taskCommit, a] at result ⊢
    refine Eq.trans ?_ (result.trans ?_) <;> rfl
  | purchased ph tr sj it hp ht unique path idx orig g material=>
    subst atRow
    let a:=Attempt.inner ph tr sj it
    let _ : Nonempty (PurchasedRole v.depth k):=⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
    let _ : Nonempty (Fin (v.wideBallotParties h a)):=⟨v.wideBallotRoot h a⟩
    let shape:=v.purchased_paid_fit P h width r banks source table target owners ph tr sj it (origin (H.code))
      entry H.prior _ H.cut (currentReadback).resident (dims).strip small
    let x0:=v.purchasedStageInput P h width r banks source table target owners ph tr sj it entry shape
    let p0:=v.purchasedPricePorts P h width ph tr
    have addr (u : ChainStrip.Axes v.depth k) : (x0.addr u).eval paid (i.val:Word w)=
        (((ord) (stripAddress v.sampler π.symm v.depth (mark (v.earnedDay ph tr hp ht)) path u)).val:Word w) :=
      ((StripPorts.OriginalFits.read fits stageLow).stock u (i.val:Word w)).trans (material u)
    have samePlan : plan = x0.alignedPlan (v.nativeFormats P h width a) (b) paid
        (v.purchasedStage_format P h width r banks source table target owners ph tr sj it entry shape)
        (v.purchasedStage_ballot P h width r banks source table target owners ph tr sj it entry shape)
        (v.purchasedStage_memory P h width r banks source table target owners ph tr sj it entry shape) := rfl
    have occVal : ((plan).enum ⟨i,vPort⟩).val = vPort.val + portCount*i.val := by
      rw [samePlan]
      apply native_debit_index (x:=x0)
    have result := g.aligned_chosen_debit (menu := v.purchasePacketMenu) atom x0 (v.nativeFormats P h width a) (b) paid
      (v.purchasedStage_format P h width r banks source table target owners ph tr sj it entry shape)
      (v.purchasedStage_ballot P h width r banks source table target owners ph tr sj it entry shape)
      (v.purchasedStage_memory P h width r banks source table target owners ph tr sj it entry shape)
      i live arity selected (bound.trans_eq (v.catalogue_words (v.seed P h width) width).1.symm)
      p0.column day stamp rfl H.cut.currentReady board rfl (dims).widthFit keyRoom loaded
      (fun u=>(StripPorts.OriginalFits.read fits oldLow).column u (i.val:Word w)) (ord) addr pad vPort ((plan).enum ⟨i,vPort⟩) occVal
    simp only [ElectedSource.debitWire, taskCommit, a] at result ⊢
    refine Eq.trans ?_ (result.trans ?_) <;> rfl


include extent tall floor in
omit [Nonempty (Fin k)] in
/-- The bit release is read even on idle and padded ports. When all debit
words for a row are zero, this forces its catalyst withdrawal to vanish. -/
theorem posted_debits
    (day : CatalystArchive.Date C a entry ((account).term (.attempt a)) ((ar).direct+(ar).occurrences) (ar).occurrences num width)
    (e : Fin (ar).occurrences) :
    day.entry.bits (Fin.cast day.shape.symm e)=if tag e=none then take e else 0 := by
  have live : Event.attempt a ∈ events v.mesh := by
    have tapeEq : events v.mesh = H.prior ++ .attempt a :: tail := H.cut.events
    rw [tapeEq]
    simp
  have layout:=((currentReadback).boards a live).1
  exact day.issued_at stamp (b) rfl H.cut.currentReady (eventBoard (ar) (s₀) (b) layout.inputs layout.window.room)
    (dims).widthFit e

section
variable {someOther : (slots (.attempt a)).choice x}
variable (ref : v.FundedDate h width size π seed age budget small t someOther)

omit [Nonempty (Fin k)] in
theorem routed_original_debit (extent : (A).endAddress v.mesh≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
    (expanse : v.wideFundedSize h width v.maxBits≤ size) (capAge : v.wideFundedHeight≤h)
    (i : I) (on : signal i) (pad : Chord (siteLast h D k+1)) (vi : Fin portCount) :
    let day:=H.originalDebitDate expanse capAge
    let occ:=(H.stripPlan extent tall floor (dims).strip).enum ⟨i,vi⟩
    let debit:=take occ
    Finsupp.single ((ref.packetAt extent tall floor i on).installed.debitWire pad vi) debit=
      (tag occ).elim 0 (fun g=>(CoreBoard.ordinalGoods π.symm name (ord)).chordWidth g debit)+
      (catalystGraph name).chordWidth ((keys).symm (day.entry.owner (Fin.cast day.shape.symm occ)))
        (day.entry.bits (Fin.cast day.shape.symm occ)) := by
  let _ : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  let u:=ref.packetAt extent tall floor i on
  let rt:=v.wideBallotRoot h a
  have read:=(v.funded_ballot_views h width size extent π seed age budget small t c).1
  have eqn := (read.1 i).trans u.nativeTerms
  have bound : v.widePacketTerms h a u.atom≤v.menu.alphabet:=eqn ▸ (((format).width a x i).trans_eq (v.catalogue_words (v.seed P h width) width).1)
  have pos : 0<v.menu.alphabet := ((Probe.NativeHistogram.alphabet_pos (u.menu rt).data).trans_le
    ((u.installed.terms u.atom rt).le.trans bound))
  have code:=H.priced_election extent tall floor i u pos
  exact routed_debits (H:=H) (extent:=extent) (tall:=tall) (floor:=floor) (srcRow:=u.installed)
    (i:=i) (atRow:=rfl) (hit:=on) (atom:=u.atom) (arity:=code.2) (selected:=code.1) (bound:=bound)
    (stageLow:=H.priced_before ref) (oldLow:=fun z low => (H.before z low).symm.trans (ref.checkout_input z low).symm)
    (day:=H.originalDebitDate expanse capAge) (keyRoom:=(H.pair_room expanse capAge).le) (pad:=pad) (vPort:=vi)

end
end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
