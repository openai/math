import OAI.Hierarchy.ProbeFixedWirePaidChronology

namespace OAI
/-! # Cross-run agreement of paid snapshots with a shared chronological past -/
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

local notation "es" => events v.mesh
local notation "until" => fun e=>(A).base v.mesh e+(A).stride

local notation "rows" => (P).catalogue.rows
local notation "chk" => fun m=> checkedOut C floor m
local notation "memAt" => fun m j=> StockBound.state C m j
local notation "stamp" => fun a=>(f a).labelSource sink (P).catalogue.idBase (StripChart.header F who a).fieldTerm
  (StripChart.id F who (P).catalogue a)
local notation "regular" => fun a=> PaidWidths.paidDirect (f a).pricedArea (f a).stockSource (stamp a)
local notation "secondary" => fun a u v'=> PaidWidths.paidMate (f a).pricedArea (f a).stockSource u v'
local notation "broadcasting" => fun (bits : ℕ) a=> PaidWidths.paidBroadcast (f a).pricedArea
  (tree a).positions (tree a).owner (tree a).parity (tree a).edge (tree a).sourceRow (f a).board.batch.copies bits

/-- One real checkout determines the variable route indices. The other
memory may have independent choices throughout the remainder of the run. -/
theorem paid_event_low (π : Equiv.Perm (Fin (2^h))) (left right : Memory w) (bits : ℕ)
    (word : floor<2^w) (native : v.WideSpillSource h width π left)
    (menu : Fintype.card (Actions N k)≤2^w) (goods : Fintype.card (Commodity (Fin (2^h)) N k)≤2^w)
    (edges : rows<2^w) (lanes : ∀l : Fin (FeedLayout.lanes N k),laneWidth (decodeLane l)*2^h<2^w)
    (ev : Event) (occur : ev∈es) (low : PrefixAgreement.Low (until ev) left right)
    (s : PaidWidths.Slice) (found : s∈v.wideEventSlices h width bits ev) (e : Fin rows) :
    s.load left e=s.load right e := by
  cases ev with
  | feed b =>
    change s∈((lay b).columns).map _ at found
    obtain ⟨c,member,rfl⟩:=List.mem_map.mp found
    exact v.prior_feed_load h width π left right native b occur low word edges.le lanes c member e
  | attempt a =>
    change s∈(f a).paidSlices sink (P).catalogue.idBase (StripChart.header F who a).fieldTerm
      (StripChart.id F who (P).catalogue a) (tree a) (v.paidSpillPath P h width recipe route order a) bits at found
    have prices:=v.prior_paid_pair_low h width left right a low word edges occur e
    have forest:=v.wide_prior_forest_low h width left right word edges bits a occur low e
    have spilled:=v.prior_spill_load h width π left right native a occur low word menu goods edges.le e
    cases hm : (tree a).catalystMate with
    | none =>
      simp only [Format.paidSlices, Format.mateSlices, hm, Option.toList, List.map, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at found
      rcases found with rfl|rfl|rfl
      · exact prices.1
      · exact forest
      · exact spilled
    | some roles =>
      simp only [Format.paidSlices, Format.mateSlices, hm, Option.toList, List.map, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at found
      rcases found with rfl|rfl|rfl|rfl
      · exact prices.1
      · exact prices.2 roles.1 roles.2 hm
      · exact forest
      · exact spilled

/-- Sufficient memory for the first j events is exactly the original archive
through the jth boundary; future selector words may vary. -/
theorem wire_past_agreement (π : Equiv.Perm (Fin (2^h))) (left right : Memory w) (bits : ℕ)
    (word : floor<2^w) (native : v.WideSpillSource h width π left)
    (menu : Fintype.card (Actions N k)≤2^w) (goods : Fintype.card (Commodity (Fin (2^h)) N k)≤2^w)
    (edges : rows<2^w) (lanes : ∀l : Fin (FeedLayout.lanes N k),laneWidth (decodeLane l)*2^h<2^w)
    (j : ℕ) (same : PrefixAgreement.Low ((A).first+j*(A).stride) left right) (e : Fin rows) :
    v.wirePaidAt h width bits j left e=v.wirePaidAt h width bits j right e := by
  apply PaidWidths.total_rows_congr
  intro s mem target
  obtain ⟨ev,dated,found⟩:=List.mem_flatMap.mp mem
  obtain ⟨n,hn,eq⟩:=List.mem_take_iff_getElem.mp dated
  have past:=hn.trans_le (min_le_left ..)
  have existsAt:=hn.trans_le (min_le_right ..)
  have pos : position v.mesh ev=n:=by rw [←eq,position_at v.mesh existsAt]
  have bound:=Nat.mul_le_mul_right (A).stride (show n+1 ≤ j from past)
  rw [Nat.add_mul,one_mul] at bound
  have low : PrefixAgreement.Low (until ev) left right:=by
    intro x hx
    change x<(A).first+position v.mesh ev*(A).stride+(A).stride at hx
    rw [pos] at hx
    exact same x (by omega)
  exact v.paid_event_low h width π left right bits word native menu goods edges lanes ev
    (by rw [←eq];exact List.getElem_mem existsAt) low s found target

theorem wide_past_agreement :
    ∀ᶠ h : ℕ in Filter.atTop,∀width,width≤2^h→v.keepLimit*width+1≤2^h→
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let paidStock:=v.fixedTerminalStock placed h width
      let paidOrder:=wideRouteOrder h (2^v.W) k
      ∀size,(arena).endAddress v.mesh ≤ size→∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) bits j,
        let checked:=v.wideSignedCheckoutAt h width size paidStock v.radius π paidOrder raw
        ∀other : Memory (Native.wordBits h (2^v.W) Native.copies),
          PrefixAgreement.Low ((arena).first+j*(arena).stride) checked other→
          ∀e : Fin (placed).catalogue.rows,v.wirePaidAt h width bits j checked e=v.wirePaidAt h width bits j other e := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  filter_upwards [v.spill_word_room,v.wide_row_room,Filter.eventually_ge_atTop v.wideStockHeight] with h words bound age
  intro width small budget placed arena paidStock paidOrder size extent π raw bits j checked other same
  have W:=(v.wide_stock_sizes h width age budget small).words.addresses
  have full:=(v.wide_stock_at h width size extent v.radius π raw age budget small).mounted_all
  have read:=(v.wide_spill_source h width size extent π raw W full).2
  exact v.wire_past_agreement h width π checked other bits W read words.1 words.2.1 (bound width).1 words.2.2 j same

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
