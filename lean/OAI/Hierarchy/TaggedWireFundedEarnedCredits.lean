import OAI.Hierarchy.TaggedWireFundedTargetStage
import OAI.Hierarchy.TaggedWireChosenStripTarget
import OAI.Hierarchy.ProbeFixedEarnedLabels
import OAI.Hierarchy.ProbeFixedWideEarnedTree
import OAI.Hierarchy.TaggedWireFundedEarnedAgreement

namespace OAI
/-! # Physical load of a chosen original strip on the two alternative histogram histories -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Strip WireTelescope CatalystArchive StockCommit RepairHistogram
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor Probe ChosenPackets RowRouting StripPaths PacketTurns
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped BigOperators Classical Fin.CommRing

variable {sam : PurchaseSampler} {h d k n K w : ℕ} {A B Ball F : Type}
  [Field F] [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "Good" => Commodity (Fin (2^h)) (Stages h d) k
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
  {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
  {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K} {addr : A → Commodity (Fin (2^h)) (Stages h d) k}
  {m archived : Memory w} {reg : Word w}
variable (g : EarnedInstall p b π extra place u endRow name addr m reg)
  (labels : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (rt : Fin (Fintype.card (TreeSite n k)))
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
  (nativeForm : Format z rawD k q D) (batch : Batch q D) (tape : Memory w)
  (formEq : x.form = nativeForm) (batchEq : x.ballot = batch) (tapeEq : x.mem = tape)
local notation "aligned" => x.alignedPlan nativeForm batch tape formEq batchEq tapeEq
variable
  (j : Fin nativeForm.market.rows) (live : j∈liveRows batch tape nativeForm.market.rows)
  (arity : (batch.termCount.read tape (batch.packet.eval tape (j.val:Word w))).val=(menu.packet i).terms)
  (selected : (batch.packet.eval tape (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1)
  (pad : Chord K) (ordinal : Commodity (Fin (2^h)) (Stages h d) k ↪ Fin nativeForm.pricedArea.goods)
  (slots : ∀a,(x.addr a).eval tape (j.val:Word w)=((ordinal (addr a)).val:Word w))
variable (bound : (menu.packet i).terms≤q) (chosen : Histogram (Fin (menu.packet i).terms) batch.copies)
  (digits : ∀t : Fin (menu.packet i).terms, ((batch.field (t.castLE bound)).eval tape (j.val:Word w)).val=((chosen.val t).val))
local notation "needs" => (fun z : PositiveDemand req i.val.val=>req z.val)
local notation "route" => g.tender labels needs rt (menu.packet i) batch.copies pad
local notation "loaded" => (route).install.load ((route).bits chosen)
local notation "st" => fresh nativeForm.pricedArea nativeForm.stockSource
local notation "nativeTag" => kind (goods:=nativeForm.pricedArea.goods) (st).plan.bank (st).columns tape
variable (stamp : LabelSource) (mask mate : Expr) (cut : ℕ)
  (low : PrefixAgreement.Low cut archived m)
  (fits : ∀ r : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k, (p.primary b r).Fits w cut)
  (primary : ∀ r : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k, paidRole r →
    stamp.edge.eval archived (((PortPadding.inject x.ports (Fintype.equivFin _ r)).val+D*j.val : ℕ):Word w)=
      (p.primary b r).eval archived reg)
  (on : ∀ r : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k,
    mask.eval archived (((PortPadding.inject x.ports (Fintype.equivFin _ r)).val+D*j.val : ℕ):Word w)≠0 ↔
      EarnedInstall.usesMate r)
  (second : ∀ c axis, mate.eval archived (((PortPadding.inject x.ports
      (Fintype.equivFin (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k) (.catalyst c axis))).val+D*j.val : ℕ):Word w)=
    (p.mate b (.catalyst c axis : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)).eval archived reg)
local notation "firstAt" e => (aligned).rowCredit j (primaryHit nativeForm.pricedArea nativeForm.stockSource stamp tape archived e)
local notation "secondAt" e => (aligned).rowCredit j (secondaryHit nativeForm.pricedArea nativeForm.stockSource mask mate tape archived e)


include live arity selected slots low fits primary on second digits in
omit [Nonempty (Fin k)] in
/-- Transport the elected strip credit through its compiled format, ballot and stage memory. -/
private theorem EarnedInstall.aligned_chosen_credits :
    (∀good : Good,loaded (stockRow (p:=b.rows) (stockOrder h d k good))=
      (aligned).rowCredit j (fun occ=>(nativeTag) occ=some (ordinal good))) ∧
    (∀e : Fin b.rows,loaded (paidRow (g:=Fintype.card Good) e)=(firstAt e)+(secondAt e)+
      ∑ l:T,if ((p.primary b (treeRole n k l:R)).eval archived reg).val=e.val
        then batch.copies*(menu.packet i).selectorBits else 0) := by
  subst nativeForm batch tape
  exact g.chosen_strip_target (menu:=menu) labels rt i x j live arity selected pad ordinal slots
    bound chosen digits stamp mask mate cut low fits primary on second

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 2200000
set_option cleanup.letToHave false
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


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h)))
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

/-- Select the strip's original packet-number ordering for either native menu. -/
def ballotOrdinal (z : ℕ) : (event : Attempt) → v.widePacketMenuIndex z event → Fin (v.ballotAtoms z event)
  | .outer ..,i=>Fintype.equivFin _ i
  | .inner ..,i=>Fintype.equivFin _ i

theorem ballotOrdinal_word (z : ℕ) (e : Attempt) (u : v.widePacketMenuIndex z e) :
    (ballotOrdinal (v:=v) z e u).val+1=v.widePacketNumber z e u := by cases e <;>rfl

variable {mark : Marks h v.W k dates} {previous : Memory w}
    {ends : Fin (cat).rows→Site h D k×Site h D k} [Nonempty (Fin k)]
    {rowIdx : ℕ} (sourceRow : v.ElectedSource h width π.symm mark ends previous a rowIdx)
    (i : I) (atRow : rowIdx=i.val) (hit : signal i)
    (atom : v.widePacketMenuIndex h a) (rt : Fin (v.wideBallotParties h a))
    (pad : Chord (siteLast h D k+1))
    (mass : Histogram (Fin (sourceRow.placed atom rt).data.terms) (b).copies)
    (bound : (sourceRow.placed atom rt).data.terms≤v.menu.alphabet)
    (digits : ∀t : Fin (sourceRow.placed atom rt).data.terms,
      (((b).field (t.castLE (bound.trans_eq (v.catalogue_words (v.seed P h width) width).1.symm))).eval paid (i.val:Word w)).val=(mass.val t).val)
    (arity : ((b).termCount.read paid ((b).packet.eval paid (i.val:Word w))).val=v.widePacketTerms h a atom)
    (code : ((b).packet.eval paid (i.val:Word w)).val=v.widePacketNumber h a atom)
    (before : PrefixAgreement.Low ct paid previous) (archive : PrefixAgreement.Low ct co previous)

local notation "route" => sourceRow.routing atom rt (b).copies pad
local notation "load" => (route).install.load ((route).bits mass)
local notation "trees" e:arg => ∑l : TreeLink (v.ballotTreeEdges h a) k,
  if ((v.ballotTreePort P h width a l).eval co (i.val:Word w)).val=(e).val then
    (b).copies*v.ballotSelectorBits h a (ballotOrdinal (v:=v) h a atom) else 0


omit [Nonempty (Fin k)] in
include sourceRow archive atRow extent tall floor in
theorem routed_tree_range (l : TreeLink (v.ballotTreeEdges h a) k) :
    ((v.ballotTreePort P h width a l).eval co (i.val:Word w)).val<(cat).rows := by
  have event : Event.attempt a ∈ events v.mesh := by
    have eqn : events v.mesh = H.prior ++ .attempt a :: tail := H.cut.events
    rw [eqn]
    simp
  have word : ct<2^w:=((Nat.le_add_right ..).trans ((A).within v.mesh (.attempt a) event)).trans_lt (currentReadback).endFits
  have fits:=v.wide_earned_before h width a word
  cases sourceRow with
  | payload ph tr record index address g material=>
    subst atRow
    exact g.tree_range_at co _ archive (StripPorts.OriginalFits.primary fits) l
  | purchased ph tr sj it hp ht uniq path index address g material=>
    subst atRow
    exact g.tree_range_at co _ archive (StripPorts.OriginalFits.primary fits) l

include extent tall floor hit atRow before archive code arity digits in
omit [Nonempty (Fin k)] in
/-- All hypotheses about data in this lemma are unaggregated native input
reads. Selecting either constructor runs the actual strip's packet compiler. -/
theorem routed_credits :
    (∀good : goods,load (stockRow (p:=(cat).rows) (stockOrder h D k good))=
      (plan).rowCredit i (fun e=>tag e=some ((ord) good))) ∧
    (∀e : Fin (cat).rows,load (paidRow (g:=Fintype.card goods) e)=
      (plan).rowCredit i (prim e)+(plan).rowCredit i (second e)+trees e) := by
  have event : Event.attempt a ∈ events v.mesh := by
    have eqn : events v.mesh = H.prior ++ .attempt a :: tail := H.cut.events
    rw [eqn]
    simp
  have word : ct<2^w := ((Nat.le_add_right ..).trans ((A).within v.mesh (.attempt a) event)).trans_lt (currentReadback).endFits
  have fits:=v.wide_earned_before h width a word
  have portCap : max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))≤2^w := (dims).roles
  have room : (cat).rows<2^w := (Classical.choose_spec (eventually_atTop.1 v.wide_row_room) h
    (max_le_iff.mp (max_le_iff.mp tall).2).1 width).1
  have loaded:=H.checkout_ports extent tall floor
  have live:=(H.priced_row_iff extent tall floor i).2 hit
  cases sourceRow with
  | payload ph tr record index address g material =>
    subst atRow
    let a:=Attempt.outer ph tr
    let _ : Nonempty (PayloadRole N k):=⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
    let _ : Nonempty (Fin (v.wideBallotParties h a)):=⟨v.wideBallotRoot h a⟩
    let shape:=v.payload_paid_fit P h width r banks source table target owners ph tr (origin (H.code))
      entry H.prior _ H.cut (currentReadback).resident (dims).strip small
    let raw:=v.payloadStageInput P h width r banks source table target owners ph tr entry shape
    have locations (u : PayloadStrip.Quotes N k) : (raw.addr u).eval paid (i.val:Word w)=
        (((ord) (PayloadStrip.rowAddress record u)).val:Word w) :=
      ((StripPorts.OriginalFits.read fits before).stock u (i.val:Word w)).trans (material u)
    have label (u : PayloadRole N k) := v.payload_earned_labels P h width r banks source table target owners ph tr
      co i u loaded portCap room
    have result:=g.aligned_chosen_credits (menu:=v.payloadPacketMenu N) SiteNaming.labels rt atom raw
      (v.nativeFormats P h width a) (b) paid
      (v.payloadStage_format P h width r banks source table target owners ph tr entry shape)
      (v.payloadStage_ballot P h width r banks source table target owners ph tr entry shape)
      (v.payloadStage_memory P h width r banks source table target owners ph tr entry shape)
      i live arity code pad (ord).toEmbedding locations
      (bound.trans_eq (v.catalogue_words (v.seed P h width) width).1.symm) mass digits stamp mask mate ct archive (StripPorts.OriginalFits.primary fits) (fun u _=> (label u).1)
      (fun u=>(label u).2.1) (fun c j=>(label (.catalyst c j)).2.2)
    have selector : v.ballotSelectorBits h (.outer ph tr) (ballotOrdinal (v:=v) h (.outer ph tr) atom) = ((v.payloadPacketMenu N).packet atom).selectorBits :=
      congrArg (fun u : (v.payloadPacketMenu N).index => ((v.payloadPacketMenu N).packet u).selectorBits)
        ((Fintype.equivFin (v.payloadPacketMenu N).index).symm_apply_apply atom)
    have samePlan : plan = v.payloadStage_compile P h width r banks source table target owners ph tr entry shape := rfl
    simp only [selector, samePlan, payloadStage_compile, ElectedSource.routing, ballotTreePort, taskCommit, a] at result ⊢
    exact result
  | purchased ph tr sj it hp ht uniq path index address g material =>
    subst atRow
    let a:=Attempt.inner ph tr sj it
    let _ : Nonempty (PurchasedRole v.depth k):=⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
    let _ : Nonempty (Fin (v.wideBallotParties h a)):=⟨v.wideBallotRoot h a⟩
    let shape:=v.purchased_paid_fit P h width r banks source table target owners ph tr sj it (origin (H.code))
      entry H.prior _ H.cut (currentReadback).resident (dims).strip small
    let raw:=v.purchasedStageInput P h width r banks source table target owners ph tr sj it entry shape
    have locations (u : ChainStrip.Axes v.depth k) : (raw.addr u).eval paid (i.val:Word w)=
        (((ord) (stripAddress v.sampler π.symm v.depth (mark (v.earnedDay ph tr hp ht)) path u)).val:Word w) :=
      ((StripPorts.OriginalFits.read fits before).stock u (i.val:Word w)).trans (material u)
    obtain ⟨_,_,js,nt⟩:=scheduled_inner v.mesh ph tr sj it event
    have held (f : Fin (eventPorts).ports) := H.retained_role extent tall floor
      (phase:=⟨ph,hp⟩) (trial:=⟨tr,ht⟩) (j:=⟨sj,js⟩) (n:=⟨it,nt⟩) i hit f
    have label (u : PurchasedRole v.depth k) (cash : paidRole u) :=
      v.purchased_earned_labels P h width r banks source table target owners ph tr sj it co previous i u g.placed
        cash loaded portCap room ct archive (fits.primary u) (fun _=>held _)
    have on (u : PurchasedRole v.depth k) := (v.purchased_mate_at P h width ph tr sj it co i u loaded portCap room).1
    have result:=g.aligned_chosen_credits (menu:=v.purchasePacketMenu) SiteNaming.labels rt atom raw
      (v.nativeFormats P h width a) (b) paid
      (v.purchasedStage_format P h width r banks source table target owners ph tr sj it entry shape)
      (v.purchasedStage_ballot P h width r banks source table target owners ph tr sj it entry shape)
      (v.purchasedStage_memory P h width r banks source table target owners ph tr sj it entry shape)
      i live arity code pad (ord).toEmbedding locations
      (bound.trans_eq (v.catalogue_words (v.seed P h width) width).1.symm) mass digits stamp mask mate ct archive (StripPorts.OriginalFits.primary fits) (fun u cash=>(label u cash).1)
      (fun u => (Iff.of_eq (congrArg (fun bit : Word w => bit ≠ 0) (on u))).trans
        (catalystBit_nonzero u (by unfold Native.wordBits; omega)))
      (fun c j=>(label (.catalyst c j) (by trivial)).2.2)
    have selector : v.ballotSelectorBits h (.inner ph tr sj it) (ballotOrdinal (v:=v) h (.inner ph tr sj it) atom) = (v.purchasePacketMenu.packet atom).selectorBits :=
      congrArg (fun u : v.purchasePacketMenu.index => (v.purchasePacketMenu.packet u).selectorBits)
        ((Fintype.equivFin v.purchasePacketMenu.index).symm_apply_apply atom)
    have samePlan : plan = v.purchasedStage_compile P h width r banks source table target owners ph tr sj it entry shape := rfl
    simp only [selector, samePlan, purchasedStage_compile, ElectedSource.routing, ballotTreePort, taskCommit, a] at result ⊢
    exact result

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
