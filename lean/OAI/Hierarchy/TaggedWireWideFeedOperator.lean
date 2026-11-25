import OAI.Hierarchy.ProtocolRAMDateSpillDirectory
import OAI.Hierarchy.ProbeFixedWirePaidEnds
import OAI.Hierarchy.TaggedWireFeedPaidLoad
import OAI.Hierarchy.TaggedWireWideGoodsChange
import OAI.Hierarchy.TaggedWireFeedRebase
import OAI.Hierarchy.TaggedWirePhysicalTerm
import OAI.Hierarchy.ProbeFixedWirePaidChronology
import OAI.Hierarchy.ProbeFixedWireUsedAt

namespace OAI
/-! # Genuine deterministic site matrix at an original outer or reserve feed -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl

local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tbl" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "C" => v.wideSignedChart h width stock
local notation "bs" => v.stockBanks P h width
local notation "es" => events v.mesh
local notation "order" => wideRouteOrder h D k
local notation "good" => Commodity (Fin (2^h)) N k


local notation "place" => siteNumber h D k
local notation "rows" => (P).catalogue.rows
local notation "placed" => (P).catalogue.coreMount
local notation "axes" => Columns h D×Fin k

/-- All date and stock addresses in this action come from the original raw
checkout. The first two receipts refer to the preceding paid prefix, and the
third enumerates the actual native spill paths at this single release. -/
def wire_feed_operator_at (size : ℕ) (extent : (A).endAddress v.mesh≤ size)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (late : v.wideStockHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (dimension : 2*v.keepLimit+2≤2^h)
    (bits : ℕ) (u : Fin (es).length) (b : Boundary) (atFeed : (es)[u.val]=.feed b) :
    let mid:=v.wideSignedMidAt h width size stock v.radius π order raw
    let pre:=StockBound.state C mid u.val
    let post:=StockBound.state C mid (u.val+1)
    let oldMount:=placed π place (v.wideOrder h width) pre
    let newMount:=placed π place (v.wideOrder h width) post
    let U:=v.wireAt h width bits π u.val pre
    let V:=v.wireAt h width bits π (u.val+1) post
    let prePaid:=v.wirePaidAt h width bits u.val pre
    let postPaid:=v.wirePaidAt h width bits (u.val+1) post
    let bump:=PaidWidths.total (edges:=rows) (v.wideEventSlices h width bits (.feed b)) post
    let spill:=fun i : good=>(post ((FeedLayout.atEvent («N»:=N) v.mesh A (v.nativeFormats P h width)
      (P).joint.initial width v.keepLimit b).overflow+PurchaseInventory.slot i)).val
    (∀e,0<prePaid e→(oldMount.actual.tail e=newMount.actual.tail e ∧ oldMount.actual.head e=newMount.actual.head e)) →
    (∀e,postPaid e=prePaid e+bump e) → (∀e,bump e=routeLoad newMount.ordinary spill e) →
    {gate : SiteMatrix (State U) (State V) F //
      ∀x,(LinearAlgebra.SpectralBooks.ChordGraph.raw F U).coeff x=
        SiteMatrix.act gate (LinearAlgebra.SpectralBooks.ChordGraph.raw F V).coeff x} := by
  intro mid pre post oldMount newMount U V prePaid postPaid bump spill ends add load
  let auth:=v.wide_paid_feed_stock h width size extent v.radius π raw late budget small dimension
  have next : post=after C (.feed b) pre := (StockBound.state_succ C mid u.val u.isLt).trans (congrArg (fun evt=>after C evt pre) atFeed)
  have cut : Slot C mid (.feed b) ((es).take u.val) ((es).drop (u.val+1)) pre := by
    exact (congrArg (fun evt => Calendar.Slot C mid evt ((es).take u.val) ((es).drop (u.val+1)) pre) atFeed).mp
      (ordinal_slot C mid u auth.nativeStock.mounted_all)
  let T:=v.dated_feed_transfer P h width r old src tbl dst owners mid auth b cut
  let passive:=fun i : good=>v.feedPassive (z:=h) width b i
  have receipt (i : good):=v.wire_feed_quantities h width size extent v.radius π raw late budget small
    dimension u.val u.isLt b atFeed cut i
  have beforeBits (i : good) : v.wireGoodsAt h width u.val pre i=passive i+T.old i+T.active i := (receipt i).1
  have afterBits (i : good) : v.wireGoodsAt h width (u.val+1) post i=passive i+T.held i+T.kept i := by
    rw [next];exact (receipt i).2.1
  have spilled : spill=T.spill := by
    funext i
    rw [show T.spill i=(after C (.feed b) pre
      ((FeedLayout.atEvent («N»:=N) v.mesh A (v.nativeFormats P h width) (P).joint.initial width v.keepLimit b).overflow+
       PurchaseInventory.slot i)).val from
      (v.dated_feed_reads P h width r old src tbl dst owners mid auth b cut i).2.2.2.2]
    change (post _).val=_
    rw [next]
  have paid (e : Fin rows) : postPaid e=prePaid e+routeLoad newMount.ordinary T.spill e := by rw [add,load,spilled]
  have room:=(v.wide_stock_sizes h width late budget small).words.addresses
  have axesFit : (fun a : axes=>fuel v.mesh*width-v.wireUsedAt h width (u.val+1) post a)=
      fun a : axes=>fuel v.mesh*width-v.wireUsedAt h width u.val pre a := by
    funext a
    have amount:=v.wire_used_retired_step h width mid auth.nativeStock.mounted_all room u a
    change v.wireUsedAt h width (u.val+1) post a=v.wireUsedAt h width u.val pre a+
      v.wireWithdrawal h width ((es)[u.val]) post a at amount
    simp only [atFeed,wireWithdrawal,Nat.add_zero] at amount
    rw [amount]
  exact FeedTransfer.ledgerOperator (F:=F) newMount oldMount.actual prePaid postPaid passive
    (v.wireGoodsAt h width u.val pre) (v.wireGoodsAt h width (u.val+1) post) _ _ T
    (siteNumber h D k).injective (publicChord h D k) (ProtocolRAMDateSpillRank.spillEnum newMount order)
    (FeedTransfer.paid_geometry _ _ _ ends)
    paid beforeBits afterBits axesFit

/-- Uniform archive horizon for the chronological scan of all previously
reported paid fields, independent of the run or the private inputs. -/
def feedPrefixHeight := Classical.choose (Filter.eventually_atTop.1 v.wide_wire_paid)

/-- At a sufficiently large original height the positive scatter and the
geometric route load are the actual measured widths of this one event. -/
def wire_feed_from_ends (size : ℕ) (extent : (A).endAddress v.mesh≤ size)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (late : v.wideStockHeight≤h)
    (prefixAge : v.feedPrefixHeight≤h) (readAge : v.feedPaidHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (dimension : 2*v.keepLimit+2≤2^h)
    (bits : ℕ) (u : Fin (es).length) (b : Boundary) (atFeed : (es)[u.val]=.feed b) :
    let mid:=v.wideSignedMidAt h width size stock v.radius π order raw
    let pre:=StockBound.state C mid u.val
    let post:=StockBound.state C mid (u.val+1)
    let oldMount:=placed π place (v.wideOrder h width) pre
    let newMount:=placed π place (v.wideOrder h width) post
    let U:=v.wireAt h width bits π u.val pre
    let V:=v.wireAt h width bits π (u.val+1) post
    (∀e,0<v.wirePaidAt h width bits u.val pre e→
      oldMount.actual.tail e=newMount.actual.tail e ∧ oldMount.actual.head e=newMount.actual.head e) →
    {gate : SiteMatrix (State U) (State V) F //
      ∀x,(LinearAlgebra.SpectralBooks.ChordGraph.raw F U).coeff x=
        SiteMatrix.act gate (LinearAlgebra.SpectralBooks.ChordGraph.raw F V).coeff x} := by
  intro mid pre post oldMount newMount U V ends
  let auth:=v.wide_paid_feed_stock h width size extent v.radius π raw late budget small dimension
  have next : post=after C (.feed b) pre := (StockBound.state_succ C mid u.val u.isLt).trans (congrArg (fun evt=>after C evt pre) atFeed)
  have cut : Slot C mid (.feed b) ((es).take u.val) ((es).drop (u.val+1)) pre := by
    exact (congrArg (fun evt => Calendar.Slot C mid evt ((es).take u.val) ((es).drop (u.val+1)) pre) atFeed).mp
      (ordinal_slot C mid u auth.nativeStock.mounted_all)
  apply v.wire_feed_operator_at h width size extent π raw late budget small dimension bits u b atFeed ends
  · intro e
    have paid:=((Classical.choose_spec (Filter.eventually_atTop.1 v.wide_wire_paid)) h prefixAge width
      small budget size extent π raw bits).2 u e
    change _=_+PaidWidths.total (v.wideEventSlices h width bits ((es)[u.val])) post e at paid
    rwa [atFeed] at paid
  · intro e
    have paid:=v.wire_feed_paid_load h width size bits extent π raw readAge late small budget dimension u b atFeed cut e
    let T:=v.dated_feed_transfer P h width r old src tbl dst owners mid auth b cut
    have weights : T.spill=fun i : good=>(after C (.feed b) pre
        ((FeedLayout.atEvent («N»:=N) v.mesh A (v.nativeFormats P h width) (P).joint.initial width v.keepLimit b).overflow+
          PurchaseInventory.slot i)).val := funext fun i=>
      (v.dated_feed_reads P h width r old src tbl dst owners mid auth b cut i).2.2.2.2
    change PaidWidths.total (edges:=rows) (v.wideEventSlices h width bits (.feed b)) post e=
      routeLoad (placed π place (v.wideOrder h width) post).ordinary
        (fun i : good=>(post ((FeedLayout.atEvent («N»:=N) v.mesh A (v.nativeFormats P h width)
          (P).joint.initial width v.keepLimit b).overflow+PurchaseInventory.slot i)).val) e
    rw [next,←weights]
    exact paid

/-- One fixed horizon suffices simultaneously for every permutation, calendar
date, width, private selector and release, including all previously bought rows. -/
def feedOperatorHeight := max (max v.wideStockHeight v.feedPrefixHeight)
  (max (max v.feedPaidHeight (Classical.choose (Filter.eventually_atTop.1 v.wire_paid_ends)))
    (2*v.keepLimit+2))

private theorem feedOperatorBounds {h : ℕ} (large : v.feedOperatorHeight≤h) :
    v.wideStockHeight≤h ∧ v.feedPrefixHeight≤h ∧ v.feedPaidHeight≤h ∧
    Classical.choose (Filter.eventually_atTop.1 v.wire_paid_ends)≤h ∧ 2*v.keepLimit+2≤h := by
  change max (max v.wideStockHeight v.feedPrefixHeight)
    (max (max v.feedPaidHeight (Classical.choose (Filter.eventually_atTop.1 v.wire_paid_ends)))
      (2*v.keepLimit+2)) ≤ h at large
  simp only [max_le_iff] at large
  exact ⟨large.1.1, large.1.2, large.2.1.1, large.2.1.2, large.2.2⟩

/-- The deterministic physical site matrix at each feed, from the original
checkout and the actual chronological stocks immediately before and after it. -/
def wire_feed_operator (size : ℕ) (extent : (A).endAddress v.mesh≤ size)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (large : v.feedOperatorHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    (bits : ℕ) (u : Fin (es).length) (b : Boundary) (atFeed : (es)[u.val]=.feed b) :
    let mid:=v.wideSignedMidAt h width size stock v.radius π order raw
    let pre:=StockBound.state C mid u.val
    let post:=StockBound.state C mid (u.val+1)
    let U:=v.wireAt h width bits π u.val pre
    let V:=v.wireAt h width bits π (u.val+1) post
    {gate : SiteMatrix (State U) (State V) F //
      ∀x,(LinearAlgebra.SpectralBooks.ChordGraph.raw F U).coeff x=
        SiteMatrix.act gate (LinearAlgebra.SpectralBooks.ChordGraph.raw F V).coeff x} := by
  intro mid pre post U V
  let bounds := feedOperatorBounds v large
  have stockAge := bounds.1
  have prefixAge := bounds.2.1
  have readAge := bounds.2.2.1
  have endAge := bounds.2.2.2.1
  have dimension := bounds.2.2.2.2
  apply v.wire_feed_from_ends h width size extent π raw stockAge prefixAge readAge budget small
    (dimension.trans (Nat.lt_two_pow_self (n:=h)).le) bits u b atFeed
  intro e pos
  have paid:=((Classical.choose_spec (Filter.eventually_atTop.1 v.wide_wire_paid)) h prefixAge width
    small budget size extent π raw bits).2 u e
  have nextPos : 0<v.wirePaidAt h width bits (u.val+1) post e := by
    exact lt_of_lt_of_le pos ((Nat.le_add_right ..).trans paid.ge)
  have ends:=(Classical.choose_spec (Filter.eventually_atTop.1 v.wire_paid_ends)) h endAge width
    small budget size extent π raw bits
  have beforeEnds:=ends u.val u.isLt.le e pos
  have afterEnds:=ends (u.val+1) u.isLt e nextPos
  exact ⟨beforeEnds.1.trans afterEnds.1.symm,beforeEnds.2.trans afterEnds.2.symm⟩

private theorem feedPresentationRoom {h : ℕ} (age : v.feedOperatorHeight ≤ h) :
    v.wideStockHeight ≤ h ∧ 2*v.keepLimit+2 ≤ 2^h := by
  change max (max v.wideStockHeight v.feedPrefixHeight)
    (max (max v.feedPaidHeight (Classical.choose (Filter.eventually_atTop.1 v.wire_paid_ends)))
      (2*v.keepLimit+2)) ≤ h at age
  simp only [max_le_iff] at age
  exact ⟨age.1.1, age.2.2.trans (Nat.lt_two_pow_self (n:=h)).le⟩

def wireFeedPresentation (size : ℕ) (extent : (A).endAddress v.mesh≤ size)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (large : v.feedOperatorHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    (bits : ℕ) (u : Fin (es).length) (b : Boundary) (atFeed : (es)[u.val]=.feed b)
    {U V : Widths (siteLast h D k+1)} (op : SiteMatrix (State U) (State V) F) : Prop :=
    let mid:=v.wideSignedMidAt h width size stock v.radius π order raw
    let pre:=StockBound.state C mid u.val
    let post:=StockBound.state C mid (u.val+1)
    let B:=placed π place (v.wideOrder h width) post
    let auth:=v.wide_paid_feed_stock h width size extent v.radius π raw (feedPresentationRoom v large).1
      budget small (feedPresentationRoom v large).2
    let cut : Slot C mid (.feed b) ((es).take u.val) ((es).drop (u.val+1)) pre:=
      (congrArg (fun evt => Calendar.Slot C mid evt ((es).take u.val) ((es).drop (u.val+1)) pre) atFeed).mp
        (ordinal_slot C mid u auth.nativeStock.mounted_all)
    let T:=v.dated_feed_transfer P h width r old src tbl dst owners mid auth b cut
    let carry:=FeedTransfer.passWidth B (v.wirePaidAt h width bits u.val pre) (v.feedPassive (z:=h) width b)
      (fun a=>fuel v.mesh*width-v.wireUsedAt h width u.val pre a)
    FeedTransfer.Presents (U:=U) (V:=V) B (siteNumber h D k).injective (publicChord h D k) (ProtocolRAMDateSpillRank.spillEnum B order)
      carry T op

attribute [local irreducible] wideStockHeight feedOperatorHeight widePlacement wideSources
  wideTestHeight voteHeight dated_feed_transfer commodityGraph catalystGraph
  LinearAlgebra.SpectralBooks.PortGraph.chordWidths
  siteNumber permutationFabric ProbeStage.rounds

/-- Hardware view of the very same deterministic operator. The occurrence
equivalence is the native core-directory order, and the carry and transfer
contain exactly the three archived width families and the four live reads. -/
theorem wire_feed_presents (size : ℕ) (extent : (A).endAddress v.mesh≤ size)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (large : v.feedOperatorHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    (bits : ℕ) (u : Fin (es).length) (b : Boundary) (atFeed : (es)[u.val]=.feed b) :
    let mid:=v.wideSignedMidAt h width size stock v.radius π order raw
    let pre:=StockBound.state C mid u.val
    let post:=StockBound.state C mid (u.val+1)
    v.wireFeedPresentation h width size extent π raw large budget small bits u b atFeed
      (U:=v.wireAt h width bits π u.val pre) (V:=v.wireAt h width bits π (u.val+1) post)
      (v.wire_feed_operator h width size extent π raw large budget small bits u b atFeed).1 := by
  intro mid pre post
  unfold wireFeedPresentation
  dsimp only
  unfold wire_feed_operator
  unfold wire_feed_from_ends wire_feed_operator_at
  unfold FeedTransfer.ledgerOperator
  apply FeedTransfer.presents_rebased

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
