import OAI.Hierarchy.ProbeFixedWideSpillSource
import OAI.Hierarchy.ProbeFixedPaidOverflowAtCheckout
import OAI.Hierarchy.ProbeFixedWideRetainedPrefix

namespace OAI
/-! # Every original paid spill and feed at the signed price check -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
theorem spill_word_room : ∀ᶠ h : ℕ in Filter.atTop,
    let n:=Stages h (2^v.W)
    let w:=Native.wordBits h (2^v.W) Native.copies
    Fintype.card (Actions n k) ≤ 2^w ∧
    Fintype.card (Commodity (Fin (2^h)) n k) ≤ 2^w ∧
    ∀ l : Fin (FeedLayout.lanes n k), laneWidth (decodeLane l)*2^h < 2^w := by
  filter_upwards [Filter.eventually_ge_atTop (Fintype.card (Actions (publicStages v.W) k)),
    Filter.eventually_ge_atTop (1+publicStages v.W*(2*k)),Filter.eventually_ge_atTop (2*publicStages v.W+2)]
    with h actions goods lanes
  intro n w
  have nEq : n=publicStages v.W := fixed_stage_count ..
  have exp := (Nat.lt_two_pow_self (n:=h)).le
  have prod : 2^h*2^h < 2^w := by
    rw [← pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by dsimp [w];rw [Native.wordBits_linear]; omega)
  refine ⟨?_,?_,?_⟩
  · rw [nEq]
    exact actions.trans (exp.trans (v.date_prefix_fit h).le)
  · rw [PurchaseInventory.card_commodity,PurchaseInventory.footprint,nEq]
    exact (Nat.mul_le_mul_right _ (goods.trans exp)).trans prod.le
  · intro l
    have cap : laneWidth (decodeLane l) ≤ 2*n+2 := by
      cases decodeLane l <;> simp [laneWidth]; omega
    rw [nEq] at cap
    exact (Nat.mul_le_mul_right _ (cap.trans (lanes.trans exp))).trans_lt prod

section
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

/-- Separate bounds for the two physically different source arrays, each at an
arbitrary real catalogue row, including an unlicensed purchased row. -/
def WideSpillCases (final : Memory w) : Prop :=
  (∀a,Event.attempt a∈events v.mesh → ∀ e : Fin (P).catalogue.rows,
    let t:=v.paidSpillPath P h width recipe route order a
    (PaidWidths.paidSpill (f a).pricedArea t.positions t.owner t.parity t.edge t.sourceRow).load final e ≤
      v.overflowFactor v.menu.maximum*width) ∧
  (∀b,Event.feed b∈events v.mesh → ∀ c∈(lay b).columns, ∀ e : Fin (P).catalogue.rows,
    (c.paidSlice (v.paidFeedPath P h width route lay b c)).load final e ≤ v.overflowFactor (v.keepLimit+1)*width)

end

theorem wide_paid_spill_cases :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width, width ≤ 2^h → v.widthFloor ≤ width → v.keepLimit*width+1 ≤ 2^h →
      let P:=v.widePlacement h width
      let A:=v.privateArena P h width
      let stock:=v.fixedTerminalStock P h width
      let order:=wideRouteOrder h (2^v.W) k
      ∀size,A.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
        let final:=v.wideSignedCheckoutAt h width size stock v.radius π order raw
        final (A.endAddress v.mesh)=0 → v.WideSpillCases h width final := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  filter_upwards [v.wide_paid_overflow_cells,v.spill_word_room,v.wide_row_room,
    Filter.eventually_ge_atTop v.wideStockHeight] with h cells words rows age
  intro width small floor budget P A stock order size extent π raw final accepted
  have filed := cells width small floor budget size extent π raw accepted
  have room := (v.wide_stock_sizes h width age budget small).words.addresses
  have run := v.wide_stock_at h width size extent v.radius π raw age budget small
  obtain ⟨source,rom⟩ := (v.wide_spill_source h width size extent π raw room run.mounted_all).2
  have edges := (rows width).1.le
  let owner := v.catalystPairOwners P h width
  let parity := v.catalystPairParity P h width
  constructor
  · intro a live e
    exact v.repair_spill_load P h width π (v.wideOrder h width) final _ _ source _ rom words.1 words.2.1 edges
      (fun _ => owner) (fun _ => parity) a v.menu.maximum e (filed.1 a live)
  · intro b live c member e
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp member
    exact v.boundary_spill_load P h width π (v.wideOrder h width) final _ source words.2.2 edges
      (fun _=>owner) (fun _=>parity) b l (v.keepLimit+1) e (filed.2 b live _ (List.mem_map.mpr ⟨l,List.mem_finRange l,rfl⟩))

/-- Every dated boundary invoice is paid by the same chronological cash tape,
including an individual signed-axis feed or a deferred reserve tranche. -/
theorem wide_feed_invoice :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width, width ≤ 2^h → v.keepLimit*width+1 ≤ 2^h →
      let P:=v.widePlacement h width
      let A:=v.privateArena P h width
      let stock:=v.fixedTerminalStock P h width
      let r:=Fintype.card (Slots h (2^v.W) k)
      let page:=v.wideSignedPage h width stock
      let count:=rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F A))
      let owners:=sinkBank (v.catalystStaticStart P h width) count r P.catalogue.rows
      let banks:=TerminalLayout.settlement page stock
      let src:=TerminalLayout.source page
      let tab:=TerminalLayout.table page
      let dst:=TerminalLayout.destination page
      ∀size,A.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
        let m:=v.wideSignedMidAt h width size stock v.radius π (wideRouteOrder h (2^v.W) k) raw
        let out:=run (v.wideSignedChart h width stock) (events v.mesh) m
        let days:=v.birthMarks P h width r banks src tab dst owners m
        let ord:=P.catalogue.ordinal v.sampler π v.depth days (v.wideOrder h width) rfl
        let len:=extendedLength ord (lenCode v.sampler π v.depth days v.radius)
        ∀ b maxBits,
          ((v.wideEventSlices h width maxBits (.feed b)).map (fun t=>t.toll out len width)).sum ≤
            (v.receipts P h width r banks src tab dst owners out (.feed b)).install := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  filter_upwards [v.spill_word_room,v.wide_row_room,Filter.eventually_ge_atTop v.wideStockHeight]
    with h words rows age
  intro width small budget P A stock r page count owners banks src tab dst size extent π raw m out days ord len b maxBits
  have room := (v.wide_stock_sizes h width age budget small).words.addresses
  have run := v.wide_stock_at h width size extent v.radius π raw age budget small
  have source := (v.wide_spill_source h width size extent π raw room run.mounted_all).1.1
  exact v.true_feed_invoice P h width r banks src tab dst owners π days (v.wideOrder h width) rfl
    out _ source (fun _ => v.catalystPairOwners P h width) (fun _ => v.catalystPairParity P h width)
    words.2.2 (rows width).1.le b

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
