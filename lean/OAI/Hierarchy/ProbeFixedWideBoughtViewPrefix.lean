import OAI.Hierarchy.ProtocolRAMBoughtChosenFrame
import OAI.Hierarchy.ProbeFixedPriorPaidCore
import OAI.Hierarchy.ProbeFixedWideStockRun
import OAI.Hierarchy.ProbeFixedWideSignedHeader
import OAI.Hierarchy.ProbeFixedCatalystBirth

namespace OAI
/-! # Elapsed original bought edges have their checkout geometry throughout the remaining calendar -/
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
local notation "es" => events v.mesh
local notation "hh" => (dir).header h D k v.sampler.degree v.depth
local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs

set_option maxRecDepth 12000 in
/-- Even a padded raw candidate of an elapsed outer attempt reads the same
two original native endpoint words as checkout. -/
def WideBoughtViewPrefix (size : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (raw : Boot.Tape h (2^v.W)) : Prop :=
  ∀(a : Fin numDays) (t : Fin (es).length), (es).get t=.attempt (v.sourceAttempt a) →
    ∀j : ℕ, t.val<j → j≤(es).length → ∀rel : Fin (hh).ports,
    let row:=((hh).enum ⟨a,rel⟩).val
    let mid := v.wideSignedMidAt h width size stock v.radius π order raw
    let out := v.wideSignedCheckoutAt h width size stock v.radius π order raw
    let current : Memory w := StockBound.state chart mid j
    let now:=(P).catalogue.bought.view current (row:Word w)
    let final:=(P).catalogue.bought.view out (row:Word w)
    now.left=final.left ∧ now.right=final.right

set_option maxRecDepth 12000 in
/-- All native operands of one chosen date end before its slab retires.  Two
memories can therefore have unrelated values in all later date slices. -/
theorem wide_bought_view_low (a : Fin numDays) (rel : Fin (hh).ports) (left right : Memory w)
    (same : PrefixAgreement.Low ((A).base v.mesh (.attempt (v.sourceAttempt a))+(A).stride) left right)
    (word : (A).base v.mesh (.attempt (v.sourceAttempt a))+(A).stride<2^w)
    (header : (hh).Loaded right) (jobs : numDays≤2^w) :
    let row:=((hh).enum ⟨a,rel⟩).val
    let first:=(P).catalogue.bought.view left (row:Word w)
    let second:=(P).catalogue.bought.view right (row:Word w)
    first.left=second.left ∧ first.right=second.right := by
  let cut:=(A).base v.mesh (.attempt (v.sourceAttempt a))+(A).stride
  have surface : (A).first≤cut := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have stat:=(v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first P h width)
  have headLow : (hh).stop≤(A).first := (Nat.le_add_right ..).trans stat
  have headEnd := headLow.trans surface
  have keyEnd := (BoughtSockets.Public.borders v.sampler baseCol h v.W k numDays v.depth).2.trans headEnd
  have columns:=(CoreRoute.column_bounds v.sampler h v.W k numDays v.depth K (packing).groups H
    (P).catalogue.coreRows cut (stat.trans surface)).2
  have original:=v.sourcePair_uses h width K (packing).groups H (P).catalogue.coreRows (CoreCatalogue.pointBits h v.W)
    0 (v.wideJoint h width) r banks src tab dst owners (v.sourceOuter a).1 (v.sourceOuter a).2
  have name : finProdFinEquiv ((v.sourceOuter a).1,(v.sourceOuter a).2)=a := finProdFinEquiv.apply_symm_apply a
  rw [name] at original
  have dfs (i : Key h D k) : (((dir).shelf a).L v.sampler v.depth i).endAddress≤cut := by
    let sh:=((s).outer (v.sourceOuter a).1.val (v.sourceOuter a).2.val).market.shelf
    have shelfAt : (dir).shelf a = sh := original.1
    have early : (sh.L v.sampler v.depth i).endAddress≤(StripDirectory.flagBank sh v.sampler h D k v.depth).base :=
      (sh.end_le v.sampler v.depth i Nat.one_le_two_pow).trans ((sh.final_after v.sampler v.depth i).trans (Nat.le_add_right ..))
    have flags := (v.catalyst_birth_room P h width (v.sourceAttempt a)).2.2
    have endAt := congrArg (fun shelf : PurchaseFrozen.Shelf =>
      (shelf.L v.sampler v.depth i).endAddress) shelfAt
    exact endAt.le.trans (early.trans ((Nat.le_add_right ..).trans flags))
  exact (dir).chosen_view_frame v.sampler v.depth K (packing).groups H a rel left right same word
    columns headEnd keyEnd dfs header jobs

set_option maxRecDepth 12000 in
/-- The actual positive-or-zero acquisition flag is in the same elapsed slab. -/
theorem wide_bought_flag_low (a : Fin numDays) (rel : Fin (hh).ports) (left right : Memory w)
    (same : PrefixAgreement.Low ((A).base v.mesh (.attempt (v.sourceAttempt a))+(A).stride) left right)
    (word : (A).base v.mesh (.attempt (v.sourceAttempt a))+(A).stride<2^w)
    (header : (hh).Loaded right) (jobs : numDays≤2^w) :
    let row:=((hh).enum ⟨a,rel⟩).val
    (P).catalogue.bought.flag.eval left (row:Word w)=(P).catalogue.bought.flag.eval right (row:Word w) := by
  let ev:=v.sourceAttempt a
  let cut:=(A).base v.mesh (.attempt ev)+(A).stride
  let fmt:=v.nativeFormats P h width ev
  have first : (A).first≤cut := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have stat:=(v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first P h width)
  have headEnd : (hh).stop≤cut := ((Nat.le_add_right ..).trans stat).trans first
  have leftHeader:=(header.frame (fun x _ hx=>same x (hx.trans_le headEnd)))
  have count : fmt.market.rows=(hh).ports :=
    StripChart.candidate_count F v.mesh A (P).joint.initial s ev
  have original:=v.sourcePair_uses h width K (packing).groups H (P).catalogue.coreRows (CoreCatalogue.pointBits h v.W)
    0 (v.wideJoint h width) r banks src tab dst owners (v.sourceOuter a).1 (v.sourceOuter a).2
  have name : finProdFinEquiv ((v.sourceOuter a).1,(v.sourceOuter a).2)=a := finProdFinEquiv.apply_symm_apply a
  rw [name] at original
  have bound : (dir).flagBase a+(hh).ports≤cut := by
    have flagAt : (dir).flagBase a = (Calendar.repair chart ev).purchaseOut := original.2.1
    have placed := congrArg₂ Nat.add flagAt count.symm
    exact placed.le.trans (fmt.chargeColumns.2.2.1.trans (v.attempt_room P h width ev))
  have inside : (dir).flagBase a+rel.val<cut := (Nat.add_lt_add_left rel.isLt _).trans_le bound
  have room : (hh).ports≤2^w := ((Nat.le_add_left ..).trans bound).trans word.le
  have read (m : Memory w) (hload : (hh).Loaded m) :=
    (dir).archive_read h D k v.sampler.degree v.depth m hload jobs room (dir).flagBase a rel
  exact (read left leftHeader).trans ((same _ inside).trans (read right header).symm)

set_option maxRecDepth 12000 in
theorem wide_bought_view_prefix_at (size : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (raw : Boot.Tape h (2^v.W)) (extent : (A).endAddress v.mesh≤ size) (height : v.wideStockHeight≤h)
    (jobs : numDays≤2^w) (small : width≤2^h) (budget : v.keepLimit*width+1≤2^h) :
    v.WideBoughtViewPrefix h width size π raw := by
  let mid := v.wideSignedMidAt h width size stock v.radius π order raw
  let out := v.wideSignedCheckoutAt h width size stock v.radius π order raw
  intro a t birth j past last rel
  let ev:=Event.attempt (v.sourceAttempt a)
  let cut:=(A).base v.mesh ev+(A).stride
  let current : Memory w := StockBound.state chart mid j
  have live : ev∈es := by rw [show ev=(es).get t from birth.symm];exact (es).get_mem t
  have retained := (A).within v.mesh ev live
  have sizes:=v.wide_stock_sizes h width height budget small
  have word:=(sizes.words).addresses
  have smallCut : cut<2^w := retained.trans_lt word
  have whole:=(v.wide_stock_at h width size extent v.radius π raw height budget small).mounted_all
  have frozen:=v.prior_paid_low h width mid whole t j past last
  rw [birth] at frozen
  have same : PrefixAgreement.Low cut current out := fun x hx=>(frozen x hx).symm
  have stat:=(v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first P h width)
  have headLow : (hh).stop≤(A).first := (Nat.le_add_right ..).trans stat
  have boot:=v.wide_signed_boot_at h width size extent stock v.radius π order raw word
  have header : (hh).Loaded out := boot.2.2.1.board.rom.outer.frame (fun x _ hx=>
    v.wide_signed_checkout_below h width stock v.radius π order raw size x (hx.trans_le headLow) whole)
  exact v.wide_bought_view_low h width a rel current out same smallCut header jobs

set_option maxRecDepth 12000 in
theorem wide_bought_view_prefix : ∀ᶠ h : ℕ in Filter.atTop, ∀width : ℕ, width≤2^h → v.keepLimit*width+1≤2^h →
    ∀size : ℕ,(v.privateArena (v.widePlacement h width) h width).endAddress v.mesh≤ size →
    ∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)), v.WideBoughtViewPrefix h width size π raw := by
  filter_upwards [Filter.eventually_ge_atTop v.wideStockHeight,Filter.eventually_ge_atTop v.wideJobs] with h tall dates
  intro width small budget size extent π raw
  exact v.wide_bought_view_prefix_at h width size π raw extent tall
    (dates.trans ((Nat.lt_two_pow_self (n:=h)).le.trans (v.date_prefix_fit h).le)) small budget

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
