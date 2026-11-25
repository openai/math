import OAI.Hierarchy.ProbeFixedBoughtFlagRead
import OAI.Hierarchy.ProbeFixedWidePaidReadout
import OAI.Hierarchy.ProbeFixedStripCounts
import OAI.Hierarchy.ProbeFixedWideStockRun
import OAI.Hierarchy.ProbeFixedModeLifetimes
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueSupport

namespace OAI
/-! # Original acquired edges and their literal endpoint records at signed checkout -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CoreRoute StripChart
open PurchaseFrozen StripDirectory CatalystArchive BoughtSockets ReportSockets CatalogueRows PurchaseStage StockCommit
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A))
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tab" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "order" => wideRouteOrder h D k
local notation "dir" => (P).routes.directory
local notation "chart" => v.wideSignedChart h width stock
local notation "numDays" => v.wideJobs
local notation "groups" => WideMemory.groups h v.W
local notation "packing" => WideMemory.dir h v.W k v.wideJobs
local notation "baseCol" => CoreCatalogue.top h v.W (WideMemory.K h v.W) (packing).groups
  (WideMemory.H h v.W k v.wideJobs) (P).catalogue.coreRows
variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "mid" => v.wideSignedMidAt h width size stock v.radius π order raw
local notation "out" => v.wideSignedCheckoutAt h width size stock v.radius π order raw
local notation "days" => v.birthMarks P h width r banks src tab dst owners mid
local notation "dt" => outerDates v.mesh
local notation "mkt" => fun a : Fin numDays=>v.frozenMarket P h width (dt a).1.val (dt a).2.val
local notation "froz" => fun a : Fin numDays=>v.frozenInput P h width r banks src tab dst owners mid (dt a).1.val (dt a).2.val
local notation "mode" => fun a : Fin numDays=>observedMode chart mid (dt a).1.val (dt a).2.val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Literal original ordinals, signed CT endpoint numbers and original length code
for precisely the acquired rows, read at the output of the genuine calendar. -/
def WideBoughtCatalogue : Prop :=
  ∀j : Fin (P).catalogue.boughtRows, (P).catalogue.bought.flag.eval out (j.val:Word w)≠0 ↔
    ∃e : Bought v.sampler π v.depth days,
      ((dir).header h D k v.sampler.degree v.depth).enum ⟨e.1,BoughtLocation.relative e.2⟩=j ∧
      Located v.sampler π v.depth days v.radius ((P).catalogue.bought.view out (j.val:Word w)) (.inr e)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem wide_bought_catalogue_at (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (large : v.wideStockHeight≤h)
    (datesFit : numDays≤2^w) (small : width≤2^h) (budget : v.keepLimit*width+1≤2^h) :
    v.WideBoughtCatalogue h width size π raw := by
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  let flagsDir : BoughtSockets.Directory numDays:={dir with shelf:=fun a=>(mkt a).shelf}
  have sizes:=v.wide_stock_sizes h width large budget small
  have limits:=sizes.words.addresses
  have stockRun:=v.wide_stock_at h width size extent v.radius π raw large budget small
  have whole:=stockRun.mounted_all
  have archive:=v.mode_archive P h width r banks src tab dst owners mid stockRun
    (fun a dated=>(v.wide_stock_layout h width size extent v.radius π raw sizes.words budget sizes.width
      sizes.alphabet sizes.rowsMass sizes.roles a dated).1)
  obtain ⟨_,_,boot,pub,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size extent stock v.radius π order raw limits
  have receipt:=v.wide_paid_checkout_reads h width r banks src tab dst owners π mid ((A).endAddress v.mesh)
    boot pub limits whole le_rfl
  have ⟨geom,heap,keyLow,keyInput⟩:=v.paid_initial_tables h width π mid boot
  have installed (a : Fin numDays) : ∃fixture,
      (flagsDir.shelf a).Incoming (k:=k) v.sampler π v.depth (mkt a).phase (mkt a).temperature (mkt a).kind (froz a) ∧
      ∀i : Key h D k,(flagsDir.shelf a).Prepared v.sampler v.depth fixture i (froz a) := by
    obtain ⟨test,input,prepared,_⟩:=v.activation_parent P h width r banks src tab dst owners mid π
      (dt a).1 (dt a).2 (dt a).1.isLt (dt a).2.isLt whole geom heap keyLow keyInput
    exact ⟨test,input,prepared⟩
  choose fixture incoming prepared using installed
  have literal (a : Fin numDays) :
      (dir).shelf a=((s).outer (dt a).1.val (dt a).2.val).market.shelf ∧
      (dir).flagBase a=(Calendar.repair chart (.outer (dt a).1.val (dt a).2.val)).purchaseOut := by
    have data:=v.sourcePair_uses h width (WideMemory.K h v.W) (packing).groups (WideMemory.H h v.W k v.wideJobs)
      (P).catalogue.coreRows (CoreCatalogue.pointBits h v.W) 0 (v.wideJoint h width) r banks src tab dst owners
      (dt a).1 (dt a).2
    have rank : finProdFinEquiv ((dt a).1,(dt a).2)=a:=finProdFinEquiv.apply_symm_apply a
    rw [rank] at data
    exact ⟨data.1,data.2.1⟩
  have fits (a : Fin numDays) : (flagsDir.shelf a).flagsBase v.sampler h D k v.depth+
      count h D k*paths h v.sampler.degree v.depth<2^w :=
    (v.checkout_flags P h width r banks src tab dst owners mid (dt a).1 (dt a).2 whole archive).1
  have words (a : Fin numDays) (i : Fin (count h D k*paths h v.sampler.degree v.depth)) :
      out (flagsDir.flagBase a+i.val)=if mode a=3 then (flagsDir.shelf a).result v.sampler k v.depth (froz a)
        ((flagsDir.shelf a).flagsBase v.sampler h D k v.depth+i.val) else 0 := by
    change out ((dir).flagBase a+i.val)=_
    rw [(literal a).2]
    exact (v.checkout_flags P h width r banks src tab dst owners mid (dt a).1 (dt a).2 whole archive).2 i
  have r₀:=receipt.base.observed.board
  have rom:=r₀.rom
  have tables:=v.purchased_table_room h sizes.strip
  have siteSmall : siteLast h D k+1≤2^w := by
    have step:=ProtocolRAMPurchaseSampler.lt_span (siteLast h D k+1)
    have startPage : ProtocolRAMPurchaseSampler.span (siteLast h D k+1)≤ColumnROM.words h D k:=Nat.le_add_right ..
    have stops:=(Public.borders v.sampler baseCol h v.W k v.wideJobs v.depth).1
    have floor : (Public.keyHead v.sampler baseCol h v.W k v.depth).stop≤(A).first:=keyLow
    have arena : (A).first<2^w:=(Nat.le_add_right ..).trans_lt limits
    omega
  let actual : Marks h v.W k numDays:=fun a=>Shelf.catalogueMarks (mode a) (flagsDir.shelf a)
    (mkt a).phase (mkt a).temperature (mkt a).kind (froz a)
  have history : days=actual := by
    first
    | rfl
  have marked : Exclusive actual:=history ▸ v.paid_days_exclusive h width r banks src tab dst owners mid
  have names (a : Fin numDays) (buy : mode a=3) : actual a=StripDirectory.actualMarks (flagsDir.shelf a)
      (mkt a).phase (mkt a).temperature (mkt a).kind (froz a) :=
    Shelf.catalogueMarks_buy _ _ _ _ _ _ buy
  intro j
  rw [history]
  constructor
  · intro flag
    obtain ⟨e,rfl⟩:=flagsDir.active_original v.sampler π v.depth actual out
      (fun a=>(mkt a).phase) (fun a=>(mkt a).temperature) (fun a=>(mkt a).kind) mode froz fixture
      names incoming prepared fits words rom.outer datesFit j flag
    have ports : ((dir).shelf e.1).PortData v.sampler π v.depth (BoughtLocation.keyOf e.2) out := by
      rw [(literal e.1).1]
      exact receipt.ports (dt e.1).1 (dt e.1).2 _
    exact ⟨e,rfl,(dir).located_original v.sampler π v.depth v.radius actual marked groups PurchaseCT.groupNumber
      packing out e ports (fun t=>(r₀.columns.geometry t).group) rom.names rom.outer rom.keys rom.sites rom.tables
      datesFit tables.1 tables.2.1 r₀.columns.groupFit r₀.columns.siteFit siteSmall⟩
  · rintro ⟨e,rfl,_⟩
    exact (flagsDir.original_active v.sampler π v.depth (WideMemory.K h v.W) (packing).groups
      (WideMemory.H h v.W k v.wideJobs) out (fun a=>(mkt a).phase) (fun a=>(mkt a).temperature)
      (fun a=>(mkt a).kind) mode froz fixture incoming prepared fits words rom.outer datesFit e).2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wide_bought_catalogue : ∀ᶠ h : ℕ in Filter.atTop,∀width : ℕ,width≤2^h → v.keepLimit*width+1≤2^h →
    ∀size : ℕ,(v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size →
    ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)), v.WideBoughtCatalogue h width size π raw := by
  filter_upwards [Filter.eventually_ge_atTop (max v.wideStockHeight v.wideJobs)] with h big
  intro wd small budget n extent perm tape
  apply v.wide_bought_catalogue_at h wd n perm tape extent ((Nat.le_max_left ..).trans big) _ small budget
  exact ((Nat.le_max_right ..).trans big).trans ((Nat.lt_two_pow_self (n:=h)).le.trans (v.date_prefix_fit h).le)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
