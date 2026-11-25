import OAI.Hierarchy.ProbeFixedDatedRoleInput
import OAI.Hierarchy.ProbeFixedWideRetainedPrefix
import OAI.Hierarchy.TaggedWireMatchingEntry
import OAI.Hierarchy.TaggedWireStockOrdinals
import OAI.Hierarchy.ProbeFixedReleasedBits

namespace OAI
/-! # The physical wire inventory at each reachable original calendar date -/

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
  (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h



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


variable (bits : ℕ)
local notation "es" => events v.mesh
local notation "compile" => v.wideEventSlices h width bits
local notation "place" => siteNumber h D k
local notation "bs" => v.stockBanks P h width
local notation "pairs" => Columns h D×Fin k

/-- The original active, uninjected and undelivered portions of one good at the
entrance to date j. Each address is the actual retained earlier stock bank. -/
def wireGoodsAt (j : ℕ) (m : Memory w) (i : Commodity (Fin (2^h)) N k) :=
  let ev:=(es)[j]?
  let active:=PurchaseInventory.stock (DatedGoods.previous v.mesh bs j) m i
  let saved:=PurchaseInventory.stock (DatedGoods.stash bs ev) m i
  active+held v.mesh.inject width (DatedGoods.phase v.mesh ev)*payloadUnit i+
    (if DatedGoods.bought (C).modeAt ev m then held v.mesh.reserveSteps saved (DatedGoods.releases ev) else 0)

theorem wire_goods_run (j : ℕ) (initial : Memory w) (i : Commodity (Fin (2^h)) N k) :
    v.wireGoodsAt h width j (StockBound.state C initial j) i=
      DatedRoleInput.currentFlow v P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
        (TerminalLayout.destination page) (sinkBank start cnt r rows) j initial i := rfl

/-- Native owner word and native archived debit for one complete chronological
event. Boundary events record no catalyst transaction. -/
def wireWithdrawal (ev : Event) (m : Memory w) (a : pairs) :=
  match ev with
  | .feed _=>0
  | .attempt t=>
    let countPos : 0<num:=Nat.mul_pos Fintype.card_pos v.positive
    ∑i : Fin ((L).rows (.attempt t)),if CatalystArchive.key countPos
      (((L).term (.attempt t)).eval m (i.val:Word w))=pairKeys (Columns h D) k a then
        (m (v.releasedBase P h width (.attempt t)+i.val)).val else 0

def wireUsedAt (j : ℕ) (m : Memory w) (a : pairs) :=
  (((es).take j).map (fun ev=>v.wireWithdrawal h width ev m a)).sum

@[simp] theorem wire_used_start (m : Memory w) (a : pairs) : v.wireUsedAt h width 0 m a=0:=by
  simp [wireUsedAt]

theorem wire_used_next (j : Fin (es).length) (m : Memory w) (a : pairs) :
    v.wireUsedAt h width (j.val+1) m a=v.wireUsedAt h width j.val m a+
      v.wireWithdrawal h width ((es).get j) m a:=by
  unfold wireUsedAt
  rw [List.take_succ_eq_append_getElem j.isLt]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, List.get_eq_getElem]

def wirePaidAt (j : ℕ) (m : Memory w) :=
  PaidWidths.total (edges:=rows) (PrefixWidths.prefixRows es compile j) m

theorem wire_paid_next (j : Fin (es).length) (m : Memory w) (e : Fin rows) :
    v.wirePaidAt h width bits (j.val+1) m e=v.wirePaidAt h width bits j.val m e+
      PaidWidths.total (compile ((es).get j)) m e:=by
  exact PrefixWidths.prefix_step (events v.mesh) (v.wideEventSlices h width bits) m e j

/-- All coordinates refer to the original CT and purchased catalogue at this
date. In particular rows absent from an earlier paid prefix carry zero width. -/
def wireAt (π : Equiv.Perm (Tagged.Row h)) (j : ℕ) (m : Memory w) : LinearAlgebra.SpectralBooks.ChordGraph.Widths (siteLast h D k+1) :=
  let B:=(P).catalogue.coreMount π place (v.wideOrder h width) m
  B.actual.chordWidths (v.wirePaidAt h width bits j m)+
    (commodityGraph (k:=k) π place).chordWidths (v.wireGoodsAt h width j m)+
    (catalystGraph place).chordWidths (fun a=>fuel v.mesh*width-v.wireUsedAt h width j m a)

theorem wire_start (π : Equiv.Perm (Tagged.Row h)) (m : Memory w)
    (init : ∀i,v.wireGoodsAt h width 0 m i=initialGoods h D k width i) :
    v.wireAt h width bits π 0 m=exposedWidth π.symm D k width (fuel v.mesh*width) := by
  have empty : v.wirePaidAt h width bits 0 m=fun _=>0:=by
    funext e
    rfl
  simp only [wireAt,empty,chordWidths_empty,zero_add,funext init,wire_used_start,Nat.sub_zero,
    exposedWidth,Equiv.symm_symm]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
