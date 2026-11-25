import OAI.Hierarchy.TaggedWireDatedLedger
import OAI.Hierarchy.ProbeFixedNativeStockRun
import OAI.Hierarchy.ProbeFixedPastWireLedger

namespace OAI
/-! # Every live goods word is in the elapsed part of the calendar -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
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



open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "order" => v.wideOrder h width
local notation "sheet" => v.wideSignedPage h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


local notation "es" => events v.mesh
local notation "bs" => v.stockBanks P h width
local notation "fmt" => v.nativeFormats P h width
local notation "empty" => v.emptyReserve P h width
local notation "H₀" => v.publicHeader P h width
local notation "gsize" => PurchaseInventory.footprint h N k
local notation "cutoff" j => (A).first+j*(A).stride

private theorem origin_cells : (P).joint.initial+gsize≤(A).first := by
  have scores:=JointHeader.order (P).joint h N k
  have base : (JointHeader.scores (P).joint h N k).base≤(H₀).ports.base:=Nat.le_add_right ..
  have tail:=v.stock_header_order P h width
  have area : (H₀).ports.base≤(H₀).ports.stop:=Nat.le_add_right ..
  have origin : (P).joint.initial≤(empty).base:=by omega
  have cells : gsize≤(empty).size:=(ProtocolRAMPurchaseSampler.lt_span gsize).le
  exact (Nat.add_le_add origin cells).trans (v.emptyReserve_end_le_first P h width)

private theorem old_cells (e : Event) : (bs).active e+gsize≤(A).base v.mesh e+(A).stride := by
  cases e with
  | attempt a=>
    change ((fmt) a).pricedArea.output+gsize≤_
    have bound:=v.stock_post_span P h width a
    omega
  | feed b=>
    change (A).base v.mesh (.feed b)+gsize≤_
    have bound:=v.feed_room P h width
    omega

theorem past_goods_agreement (j : ℕ) (upto : j≤(es).length) (left right : Memory w)
    (low : PrefixAgreement.Low (cutoff j) left right) :
    v.wireGoodsAt h width j left=v.wireGoodsAt h width j right := by
  funext i
  have site:=PurchaseInventory.slot_lt i
  have active : DatedGoods.previous v.mesh bs j+gsize≤cutoff j:=by
    unfold DatedGoods.previous
    split
    next hj=>
      have hr:=v.old_cells h width ((es)[j-1]'(by omega))
      have idx:=position_at v.mesh (show j-1<(es).length by omega)
      simp only [Arena.base,idx] at hr
      have step : (j-1).succ=j:=by omega
      rw [Nat.add_assoc,←Nat.succ_mul] at hr
      simpa only [step] using hr
    · exact (v.origin_cells h width).trans (Nat.le_add_right ..)
  have initialWord : PurchaseInventory.stock (DatedGoods.previous v.mesh bs j) left i=
      PurchaseInventory.stock (DatedGoods.previous v.mesh bs j) right i:=by
    apply congrArg Fin.val
    exact low _ ((Nat.add_lt_add_left site _).trans_le active)
  unfold wireGoodsAt
  dsimp only
  rw [initialWord]
  generalize eqn : (es)[j]?=ev
  cases par : DatedGoods.parent ev with
  | none=>simp [DatedGoods.bought,par]
  | some a=>
    have earlier : position v.mesh (.attempt a)<j:=by
      cases ev with
      | none=>simp [DatedGoods.parent] at par
      | some e=>
        obtain ⟨hi,hit⟩:=List.getElem?_eq_some_iff.mp eqn
        have idx:=position_at v.mesh hi
        rw [hit] at idx
        cases e with
        | attempt ballot=>
          cases ballot <;> simp [DatedGoods.parent,StockBound.parent] at par
          subst a
          simp only [position,sliceBase] at idx ⊢
          omega
        | feed boundary=>
          cases boundary <;> simp [DatedGoods.parent,StockBound.parent] at par
          subst a
          simp only [position,sliceBase] at idx ⊢
          omega
    have near : (A).base v.mesh (.attempt a)+(A).stride≤cutoff j:=by
      unfold Arena.base
      rw [Nat.add_assoc,←Nat.succ_mul]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ earlier) _
    have code : left ((C).modeAt a)=right ((C).modeAt a):=by
      apply low
      exact (v.stock_mode_room P h width a).trans near
    have saved : PurchaseInventory.stock ((bs).saved a) left i=PurchaseInventory.stock ((bs).saved a) right i:=by
      apply congrArg Fin.val
      exact low _ ((Nat.add_lt_add_left site _).trans_le ((v.stock_post_span P h width a).trans near))
    simp [DatedGoods.bought,DatedGoods.stash,par,code,saved]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
