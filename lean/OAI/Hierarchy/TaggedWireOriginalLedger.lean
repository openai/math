import OAI.Hierarchy.TaggedWireDatedLedger
import OAI.Hierarchy.TaggedWideHostAdmission

namespace OAI
/-! # Open matching stock at the genuine inverse-tag boot -/

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

private theorem first_date (c : Mesh) (started : 0<c.inject+c.cool) :
    (events c)[0]?=some (.attempt (.outer 0 0)) ∨ (events c)[0]?=some (.feed (.outer 0)) := by
  obtain ⟨p,hp⟩:=Nat.exists_eq_succ_of_ne_zero started.ne'
  cases budget : c.outerFuel with
  | zero =>
    right
    simp [events,hp,List.range_succ_eq_map,outerBlock,budget]
  | succ n =>
    left
    simp [events,hp,List.range_succ_eq_map,outerBlock,budget,trialBlock]

theorem wire_initial_goods (m : Memory w)
    (empty : ∀i : Commodity (Fin (2^h)) N k,PurchaseInventory.stock (P).joint.initial m i=0) (i) :
    v.wireGoodsAt h width 0 m i=initialGoods h D k width i := by
  have head:=first_date v.mesh (v.clock.inject_pos.trans_le (Nat.le_add_right ..))
  have first : DatedGoods.previous v.mesh (v.stockBanks P h width) 0=(P).joint.initial :=rfl
  rcases head with hh|hh <;> cases i <;>
    simp [wireGoodsAt,hh,first,empty,DatedGoods.phase,DatedGoods.bought,DatedGoods.parent,
      StockBound.parent,held_start,payloadUnit,initialGoods]

/-- Exact S₀ width on the booted funded input, for every tag and private
initial memory, using both real cleared stock fields and native date order. -/
theorem wire_origin (size : ℕ) (seed : Boot.Tape h D) (π : Equiv.Perm (Tagged.Row h))
    (extent : (A).endAddress v.mesh≤ size) (age : v.wideStockHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) :
    v.wireAt h width v.maxBits π.symm 0 (v.wideOrigin h width size seed π)=
      exposedWidth π D k width (fuel v.mesh*width) := by
  have lim:=v.wide_stock_sizes h width age budget small
  have initial:=v.wide_initial_stock h width size extent stock v.radius π.symm o
    (v.wideFundedRaw h width v.maxBits seed) lim.words.addresses lim.strip
  exact v.wire_start h width v.maxBits π.symm _ (v.wire_initial_goods h width _ initial.1)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
