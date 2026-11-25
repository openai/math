import OAI.Hierarchy.TaggedWireFundedAttemptRows
import OAI.Hierarchy.TaggedWireFundedEarnedCredits
import OAI.Hierarchy.TaggedWireMeasuredOutput
import OAI.Hierarchy.TaggedWireElectedLoop
import OAI.Hierarchy.ProbeFixedWideBroadcastBits
import OAI.Hierarchy.TaggedWireEarnedGraphTransport

namespace OAI
/-! # Exact stock and bought-edge width produced by each branch of the funded election -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 2400000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
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
local notation "f" => v.nativeFormats P h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "order" => wideRouteOrder h D k


variable (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
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
local notation:max "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open Filter CalendarTape ChosenPackets LinearAlgebra.SpectralBooks ChordGraph
open PurchaseFrozen PurchaseStage StockCommit RepairHistogram Strip StripDirectory CatalogueRows
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical BigOperators

variable {a : Attempt} {tail x} (t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x)
  (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
local notation "event" => Event.attempt a
local notation "u" => (es).length-(event::tail).length
local notation "ref" => v.wide_reference_date h width size extent π seed age budget small t
local notation:max "date" c:arg => v.wide_funded_date h width size extent π seed age budget small t c
local notation "choice" => (slots event).choice x
local notation "rows" => (ref).2.row extent tall floor
local notation "routes" => (ref).2.tender extent tall floor
local notation "o" => v.nativeSlots P h width a
local notation "place" => siteNumber h D k
local notation "G" => CoreBoard.ordinalGoods π.symm place o
local notation "K" => catalystGraph place
local notation "b" => (P).catalogue
local notation "pre" => (b).coreMount π.symm place (v.wideOrder h width) x
local notation "shape" => v.wideCursorWidth h width size π seed age budget small


local notation "Good" => Commodity (Fin (2^h)) N k
local notation "physical" => (b).physicalEnds (π:=π.symm)
  (marks:=v.birthMarks P h width r banks source table target owners (origin ((ref).2.code)))
  (P).routes.directory (v.wideOrder h width) rfl
local notation "name" => (siteNumber h D k).toEmbedding
local notation "stockG" => earnedInventory π.symm name
local notation "billG" => earnedCatalogue physical name
local notation "key" => (stockOrder h D k).symm.trans o
local notation "fmt" => (reader).format
local notation "ballot" => enabledBatch ((C).layout a) (repair C a)
local notation "I" => Fin ((C).layout a).candidates
local notation:max "picked" i:arg => (ballot).selected (HistogramShelf.snapshot C a x) ((i).val:Word w)
local notation:max "atom" i:arg hh:arg => ((ref).2.packetAt extent tall floor i hh)
local notation "root" => v.wideBallotRoot h a
local notation "menu" => fun i hi=>(atom i hi).menu root
local notation "arity" => fun i hi=>(atom i hi).arity root
local notation "rt" => fun i hi=>(atom i hi).route root (publicChord h D k)
local notation "area" => (v.nativeFormats P h width a).pricedArea
local notation "sources" => (v.nativeFormats P h width a).stockSource
local notation "fee" => v.stamp P h width r banks source table target owners a
local notation "msk" => v.earnedClass P h width a
local notation "opp" => v.earnedMate P h width a
local notation "bos" => v.nativeTrees P h width a
local notation "tree" => PaidWidths.paidBroadcast area (bos).positions (bos).owner (bos).parity (bos).edge (bos).sourceRow
  (ballot).copies v.maxBits
local notation:max "St" c:arg => v.stage P h width r banks source table target owners a (run C (date c).prior (origin ((date c).code)))
local notation:max "checkout" c:arg => checkedOut C ((A).endAddress v.mesh) (origin ((date c).code))
local notation "treeLinks" => TreeLink (v.ballotTreeEdges h a) k
local notation:max "treeQty" m:arg i:arg packet:arg e:arg => ∑l : treeLinks,if ((v.ballotTreePort P h width a l).eval m ((i).val:Word w)).val=(e).val then
  (ballot).copies*v.ballotSelectorBits h a (FundedDate.ballotOrdinal (v:=v) h a packet) else 0

/-- The tree menus have constant size in the height variable, because the
number of permutation fabric stages is fixed by the public block width. -/
def earnedTreeHeight := max v.maxBits
  (max (Fintype.card (TreeLink (PayloadStrip.edgeCount (publicStages v.W)) k))
    (Fintype.card (TreeLink (ChainStrip.edgeCount v.depth) k)))

/-- Each side is evaluated at its own accepted signed history; only the
original placement of the selected row family is fixed at the common prefix. -/
theorem earned_target_rows (treeHeight : v.earnedTreeHeight≤h) :
    ∀c : choice,(∑i:I,((routes) i).post (c i))=
      (stockG).chordWidths (fun i=>(date c).gain (key i))+(billG).chordWidths (date c).paid := by
  let _ : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  intro c
  let H:=date c
  let date0:=(ref).2
  let native:=origin H.code
  let out:=checkout c
  let entry:=run C H.prior native
  let st:=St c
  let physicalPlan:=H.stripPlan extent tall floor (dims).strip
  let Q:=H.readbackRun extent tall floor
  have dated : Event.attempt a ∈ events v.mesh := by
    have eventEq : events v.mesh = H.prior ++ Event.attempt a :: tail := H.cut.events
    rw [eventEq]
    simp
  have cap : (b).rows<2^w := (Classical.choose_spec (eventually_atTop.1 v.wide_row_room) h
    (max_le_iff.mp (max_le_iff.mp tall).2).1 width).1
  have eventWindow : (A).base v.mesh (.attempt a)<2^w :=
    ((Nat.le_add_right ..).trans ((A).within v.mesh (.attempt a) dated)).trans_lt Q.endFits
  have oldLow:=H.checkout_agree date0
  let view:=(v.funded_ballot_views h width size extent π seed age budget small t c).1
  let keep:=fun i:I=>committed (ballot) (HistogramShelf.snapshot C a entry) (i.val:Word w)
  have agrees (i:I) : keep i↔picked i :=
    ⟨fun on=>(H.ballot extent i).2.2.mpr on.1,H.committed_at extent i⟩
  let branch:=fun (i:I) (on:picked i)=>cast (congrArg₂ (fun n d=>Histogram (Fin n) d)
    ((view.1 i).trans ((atom i on).arity root).symm) ((view.2 i).trans (ite_eq_left on))) (c i)
  let qty:=fun (i:I) (e:Fin (b).rows)=>if hi:picked i then treeQty out i ((atom i hi).atom) e else 0
  let localRead (i:I) (on:picked i) :=
    let selectedPacket:=atom i on
    have letters:= (view.1 i).trans (selectedPacket.arity root).symm
    have count:=(view.2 i).trans (ite_eq_left on)
    have bound : (selectedPacket.menu root).data.terms≤v.menu.alphabet:=letters ▸ ((fmt).width a x i).trans_eq (v.catalogue_words (v.seed P h width) width).1
    have pos:=(Probe.NativeHistogram.alphabet_pos (selectedPacket.menu root).data).trans_le bound
    have seen:=H.priced_election extent tall floor i selectedPacket pos
    H.routed_credits extent tall floor selectedPacket.installed i rfl on selectedPacket.atom root (publicChord h D k)
      (branch i on) bound (fun j=>H.tender_digits extent tall floor i letters count j) seen.2 seen.1
      (H.priced_before date0) oldLow
  have full : (area).occurrences≤2^w := by
    have lo : (area).occurrences≤(area).stop:=by
      unfold Area.stop Area.output Area.excess Area.clip Area.src Area.broadcast
      omega
    exact lo.trans ((v.attempt_room P h width a).trans (((A).within v.mesh _ dated).trans Q.endFits.le))
  have activeStock (i : I) (hi : picked i) (goodIndex : Fin (Fintype.card Good)) :
      ((rt i hi).install.load ((rt i hi).bits (branch i hi))) (stockRow (p:=(b).rows) goodIndex)=
        physicalPlan.rowCredit i (fun j=>kind (goods:=(area).goods) (fresh area sources).plan.bank (fresh area sources).columns st j=some (key goodIndex)) := by
    have value := (localRead i hi).1 ((stockOrder h D k).symm goodIndex)
    simp only [physicalPlan, st, H, FundedDate.ElectedPacket.route, taskCommit, Equiv.apply_symm_apply, Equiv.trans_apply] at value ⊢
    exact value
  have activePaid (i:I) (hi:picked i) (e:Fin (b).rows) :
      ((rt i hi).install.load ((rt i hi).bits (branch i hi))) (paidRow («g»:=Fintype.card Good) e)=
      physicalPlan.rowCredit i (primaryHit area sources fee st out e)+physicalPlan.rowCredit i (secondaryHit area sources msk opp st out e)+qty i e := by
    have value := (localRead i hi).2 e
    simp only [physicalPlan, st, out, H, FundedDate.ElectedPacket.route, qty, dite_eq_left hi] at value ⊢
    exact value
  let nativeAtom:=fun i:Subtype keep=>FundedDate.ballotOrdinal (v:=v) h a (atom i.val ((agrees i.val).mp i.property)).atom
  have forest (e:Fin (b).rows) : (tree).load out e=∑i:I,qty i e := by
    have cc (i:Subtype keep) : (ballot).packet.eval (HistogramShelf.snapshot C a entry) (i.val.val:Word w)=
        (((nativeAtom i).val+1:ℕ):Word w) := by
      let selectedPacket:=atom i.val ((agrees i.val).mp i.property)
      rw [←(H.ballot extent i.val).1]
      have same : ((ballot).packet.eval (HistogramShelf.snapshot C a x) (i.val.val:Word w)).val=(nativeAtom i).val+1 :=
        selectedPacket.nativeCode.trans (FundedDate.ballotOrdinal_word (v:=v) h a selectedPacket.atom).symm
      exact (Fin.cast_val_eq_self _).symm.trans (congrArg (fun n : ℕ=>(n:Word w)) same)
    have valid (i:Subtype keep) (l:treeLinks) := H.routed_tree_range extent tall floor
      (atom i.val ((agrees i.val).mp i.property)).installed i.val rfl oldLow l
    have ge:=max_le_iff.mp treeHeight
    have bitRoom : v.maxBits<2^w:=ge.1.trans_lt ((Nat.lt_two_pow_self (n:=h)).trans (v.date_prefix_fit h))
    have copies : (ballot).copies≤2^h:=(v.ordinary_dimensions P h width a).2.le.trans ((Nat.div_le_self ..).trans small)
    have prod : (ballot).copies*v.maxBits<2^w:=(Nat.mul_le_mul_right _ copies).trans_lt (GlobalTests.linear_room h D v.maxBits ge.1)
    have pTree : Fintype.card (TreeLink (PayloadStrip.edgeCount N) k)≤2^w:=by
      rw [show N=publicStages v.W from fixed_stage_count ..]
      exact (max_le_iff.mp ge.2).1.trans ((Nat.lt_two_pow_self (n:=h)).trans (v.date_prefix_fit h)).le
    have bTree : Fintype.card (TreeLink (ChainStrip.edgeCount v.depth) k)≤2^w:=
      (max_le_iff.mp ge.2).2.trans ((Nat.lt_two_pow_self (n:=h)).trans (v.date_prefix_fit h)).le
    have pos : 0<(b).coreRows := by
      let vertex : Columns h D:=.inl 0
      let radius : CoreBoard.Edges v.sampler h D k:=.inl (.inl (vertex,(⟨0,v.positive⟩,false)))
      exact (Nat.zero_le _).trans_lt ((v.wideOrder h width).symm radius).isLt
    have nativeLoad := Q.forest_broadcast_load a H.prior tail entry out H.cut (fun _ _=>rfl) (dims).strip bitRoom prod cap pos
      pTree bTree nativeAtom cc valid e
    have zero : (∑i : {j:I//¬keep j},qty i.val e)=0 :=
      Finset.sum_eq_zero (fun i _=>dite_eq_right (fun hi=>i.property ((agrees _).mpr hi)))
    have split := Fintype.sum_subtype_add_sum_subtype keep (fun j:I=>qty j e)
    have keptSum : (∑i : Subtype keep,qty i.val e)=∑i:I,qty i e :=
      (Nat.add_zero _).symm.trans ((congrArg ((∑i : Subtype keep, qty i.val e) + ·) zero.symm).trans split)
    refine nativeLoad.trans (Eq.trans ?_ keptSum)
    change (∑i : Subtype keep, treeQty out i.val ((atom i.val ((agrees i.val).mp i.property)).atom) e) =
      ∑i : Subtype keep,qty i.val e
    apply Finset.sum_congr rfl
    intro i _
    simp only [qty, dite_eq_left ((agrees i.val).mp i.property)]
  apply (fmt).measured_target a x x area sources fee msk opp st out stockG billG (publicChord h D k)
    view menu arity rt c physicalPlan key tree qty full (H.checkout_credits extent tall floor)
    (fun i off live=>off ((H.priced_row_iff extent tall floor i).mp live))
    (fun i off e=>dite_eq_right off) activeStock activePaid forest
  · intro i
    exact CoreBoard.commodityGraph_distinct π.symm (siteNumber h D k) (siteNumber h D k).injective _
  · intro i hit e loop
    exact (atom i hit).installed.routing_loop_zero (atom i hit).atom root (ballot).copies (publicChord h D k)
      (branch i hit) e ((siteNumber h D k).injective loop)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
