import OAI.Hierarchy.ProbeFixedPriorPaidCore

namespace OAI
/-! # Native lane scatter readbacks from each real feed's own after-state -/
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

theorem prior_feed_reads (π : Equiv.Perm (Fin (2^h))) (initial : Memory w)
    (active : Calendar.mounted C es initial) (endWord : floor<2^w)
    (native : v.WideSpillSource h width π (checkedOut C floor initial)) (edges : (P).catalogue.rows≤2^w)
    (lanes : ∀l : Fin (FeedLayout.lanes N k),laneWidth (decodeLane l)*2^h<2^w)
    (t : Fin (es).length) (b : Boundary) (date : (es).get t=.feed b) (l : Fin (FeedLayout.lanes N k)) :
    let now:=StockBound.state C initial (t.val+1)
    let traversal:=v.paidFeedPath P h width route lay b ((lay b).column l)
    traversal.Reads now (fun i=> v.spillPath P h π (v.wideOrder h width)
      ((PurchaseInventory.slotEquiv h N k).symm (finProdFinEquiv (l,i)))) := by
  intro now traversal
  let chk:=checkedOut C floor initial
  obtain ⟨enum,edgesAt,ownerAt⟩:=v.boundary_read P h π (v.wideOrder h width) chk route native.1 (lay b)
    paidO paidP l (lanes l) edges
  have low:=v.prior_paid_low h width initial active t (t.val+1) (Nat.lt_succ_self _) t.isLt
  rw [date] at low
  have live : Event.feed b ∈ es := date ▸ (es).get_mem t
  have fits:=(v.prior_spill_operands h width (.feed b) live endWord).2 b l
  refine ⟨enum,fun i=>?_,fun i=>?_⟩
  · exact (congrArg Fin.val (PrefixAgreement.expr traversal.edge chk now _
      (PrefixAgreement.inputEnd_of_fits _ fits.1) low (i.val:Word w))).symm.trans (edgesAt i)
  · exact (congrArg Fin.val (PrefixAgreement.expr traversal.sourceRow chk now _
      (PrefixAgreement.inputEnd_of_fits _ fits.2) low (i.val:Word w))).symm.trans (ownerAt i)

theorem elapsed_boundary_reads :
    ∀ᶠ h : ℕ in Filter.atTop,∀width,width≤2^h→v.keepLimit*width+1≤2^h→
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let paidStock:=v.fixedTerminalStock placed h width
      let paidOrder:=wideRouteOrder h (2^v.W) k
      let layout:=FeedLayout.atEvent («N»:=Stages h (2^v.W)) v.mesh arena (v.nativeFormats placed h width)
        (placed).joint.initial width v.keepLimit
      let nativeRoute:=source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
        (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
      ∀size,(arena).endAddress v.mesh ≤ size→∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
        let mid:=v.wideSignedMidAt h width size paidStock v.radius π paidOrder raw
        let cal:=v.wideSignedChart h width paidStock
        ∀t : Fin (events v.mesh).length,∀b : Boundary,(events v.mesh).get t=.feed b→
        ∀l : Fin (FeedLayout.lanes (Stages h (2^v.W)) k),
          (v.paidFeedPath placed h width nativeRoute layout b ((layout b).column l)).Reads
            (StockBound.state cal mid (t.val+1)) (fun i=> v.spillPath placed h π (v.wideOrder h width)
              ((PurchaseInventory.slotEquiv h (Stages h (2^v.W)) k).symm (finProdFinEquiv (l,i)))) := by
  let : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
  filter_upwards [v.spill_word_room,v.wide_row_room,Filter.eventually_ge_atTop v.wideStockHeight] with h words arity age
  intro width small budget placed arena paidStock paidOrder layout nativeRoute size extent π raw mid cal
  have word:=(v.wide_stock_sizes h width age budget small).words.addresses
  have active:=(v.wide_stock_at h width size extent v.radius π raw age budget small).mounted_all
  have src:=(v.wide_spill_source h width size extent π raw word active).2
  exact v.prior_feed_reads h width π mid active word src (arity width).1.le words.2.2

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
