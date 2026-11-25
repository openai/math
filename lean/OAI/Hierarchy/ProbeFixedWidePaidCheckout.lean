import OAI.Hierarchy.ProtocolRAMPaidCheckoutEvent
import OAI.Hierarchy.ProbeFixedWidePaidRun
import OAI.Hierarchy.ProbeFixedWideSpillCases
import OAI.Hierarchy.ProbeFixedBroadcastCap

namespace OAI
/-! # The verdict write preserves every actual original paid-width load -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
local notation "f" => v.nativeFormats P h width
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A))
local notation "start" => v.catalystStaticStart P h width
local notation "page" => v.wideSignedPage h width stock
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "banks" => TerminalLayout.settlement page stock
local notation "order" => wideRouteOrder h D k
local notation "route" => source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "recipe" => routeBanks start cnt r
local notation "lay" => FeedLayout.atEvent («N»:=N) v.mesh A f (P).joint.initial width v.keepLimit

local notation "ownerBank" => sinkBank start cnt r (P).catalogue.rows
local notation "paidO" => v.catalystPairOwners P h width
local notation "paidP" => v.catalystPairParity P h width
local notation "floor" => (A).endAddress v.mesh
local notation "who" => v.nativeBoards P h width
local notation "tree" => v.nativeTrees P h width
local notation "sink" => (P).catalogue.sink r banks (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) ownerBank

private theorem paid_row_bound {W rows edges : ℕ} {t : Traversals} {m : Memory W}
    {walk : Fin rows → List (Fin edges)} (seen : t.Reads m walk) (i : Fin t.positions) :
    (t.sourceRow.eval m (i.val : Word W)).val < rows :=
  (seen.ownerAt i).trans_lt (seen.enum i).1.isLt

set_option cleanup.letToHave false in
set_option maxHeartbeats 1000000 in
private theorem paid_checkout_at (π : Equiv.Perm (Fin (2^h))) (m : Memory w) (word : floor<2^w)
    (data : v.WideSpillSource h width π (checkedOut C floor m))
    (menu : Fintype.card (Actions N k)≤2^w)
    (goods : Fintype.card (Commodity (Fin (2^h)) N k)≤2^w)
    (edges : (P).catalogue.rows≤2^w) (lanes : ∀ l : Fin (FeedLayout.lanes N k),laneWidth (decodeLane l)*2^h<2^w)
    (e : Fin (P).catalogue.rows) :
    PaidWidths.total (v.widePaidSlices h width v.maxBits) (checkedOut C floor m) e=
    PaidWidths.total (v.widePaidSlices h width v.maxBits) (run C (events v.mesh) m) e := by
  let left:=checkedOut C floor m
  let right:=run C (events v.mesh) m
  have low : PrefixAgreement.Low floor left right := by
    intro x hx
    exact ProtocolRAMGeneratedWrite.frame_image floor 1 _ _ x (Or.inl hx)
  have first : (A).first≤floor:=Nat.le_add_right ..
  have oldEnd : (ownerBank).base+(ownerBank).size≤(A).first := (v.catalyst_static_end P h width A).le
  have space:=allocated_space start cnt r (P).catalogue.rows w (⟨0,page+2⟩ : Bank) (8*2^page) (oldEnd.trans_lt (first.trans_lt word))
  have b₀:=space.kindEnd
  have b₁:=space.modeEnd
  have b₂:=space.operandEnd
  have safe:=CoreRoute.source_safe v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
    w floor ((v.wideGeometryPrefix h width).2.2.trans ((v.catalyst_initial_le_first P h width).trans first)) word
  have before (b : Bank) (endAt : b.base+b.size≤(ownerBank).base) : b.Fits w floor :=
    ⟨Nat.two_pow_pos _,by omega,by omega⟩
  have fit : (recipe).kind.Fits w floor ∧ (recipe).mode.Fits w floor ∧ (recipe).operand.Fits w floor:=
    ⟨before _ (by omega),before _ (by omega),before _ b₂⟩
  have path := earlyFits recipe route order paidO paidP safe fit
  obtain ⟨native,installed⟩:=data
  apply PaidWidths.total_congr
  intro s hs
  rw [← v.wideEventSlices_flat h width v.maxBits] at hs
  obtain ⟨ev,scheduled,entry⟩:=List.mem_flatMap.mp hs
  cases ev with
  | attempt a =>
    have arg:=v.wide_paid_operands h width banks (TerminalLayout.source page) (TerminalLayout.table page)
      (TerminalLayout.destination page) ownerBank a scheduled word
    have banksGood:=v.paid_attempt_banks P h width a scheduled word
    have archive:= (v.attempt_room P h width a).trans ((A).within v.mesh (.attempt a) scheduled)
    have read:=v.spill_read P h width π (v.wideOrder h width) left route native recipe
      (fun t : Columns h D×Fin k=>(pairKeys (Columns h D) k t).val) installed menu goods edges paidO paidP a
    exact PaidCheckout.attempt (W:=w) (f a) sink (P).catalogue.idBase (StripChart.header F who a).fieldTerm
      (StripChart.id F who (P).catalogue a) (tree a) (v.paidSpillPath P h width recipe route order a)
      v.maxBits floor left right low e arg path banksGood archive (paid_row_bound read) s entry
  | feed b =>
    change s ∈ (lay b).columns.map (fun c => c.paidSlice (v.paidFeedPath P h width route lay b c)) at entry
    obtain ⟨c,here,rfl⟩:=List.mem_map.mp entry
    have bound:=(v.paid_feed_archive P h width b scheduled c here).1
    obtain ⟨l,_,rfl⟩:=List.mem_map.mp here
    have read:=v.boundary_read P h π (v.wideOrder h width) left route native (lay b) paidO paidP l (lanes l) edges
    have fitLane:=lane_fits route (decodeLane (feedLane (lay b) ((lay b).column l))) paidO paidP safe
    exact PaidCheckout.feed (W:=w) ((lay b).column l) (v.paidFeedPath P h width route lay b ((lay b).column l))
      floor left right low e fitLane bound (paid_row_bound read)

/-- Equality holds at every row even when the array's final dyadic padding word
coincides with the verdict location. The two potentially padded input lookups are
indexed by the bounded commodity and lane positions recovered from the genuine ROM. -/
theorem wide_paid_checkout_eq :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width, width≤2^h → v.widthFloor≤width → v.keepLimit*width+1≤2^h →
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let paidStock:=v.fixedTerminalStock placed h width
      let paidOrder:=wideRouteOrder h (2^v.W) k
      ∀size,arena.endAddress v.mesh ≤ size→∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
        let mid:=v.wideSignedMidAt h width size paidStock v.radius π paidOrder raw
        let chk:=v.wideSignedCheckoutAt h width size paidStock v.radius π paidOrder raw
        let chart:=v.wideSignedChart h width paidStock
        ∀e : Fin placed.catalogue.rows, PaidWidths.total (v.widePaidSlices h width v.maxBits) chk e =
          PaidWidths.total (v.widePaidSlices h width v.maxBits) (run chart (events v.mesh) mid) e := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  filter_upwards [v.spill_word_room,v.wide_row_room,Filter.eventually_ge_atTop v.wideStockHeight] with h words rows age
  intro width small _ budget placed arena paidStock paidOrder size extent π raw mid chk chart e
  have word:=(v.wide_stock_sizes h width age budget small).words.addresses
  have real:=(v.wide_stock_at h width size extent v.radius π raw age budget small).mounted_all
  have native:=(v.wide_spill_source h width size extent π raw word real).2
  exact paid_checkout_at v h width π mid word native words.1 words.2.1 (rows width).1.le words.2.2 e

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
