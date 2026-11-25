import OAI.Hierarchy.ProbeFixedWideSpillMiddle
import OAI.Hierarchy.TaggedWideSpillDates
import OAI.Hierarchy.TaggedWideDatedSpillMiddle
import OAI.Hierarchy.ProtocolRAMDateSpillLoadRead
import OAI.Hierarchy.ProbeFixedWideSpillCases

namespace OAI
/-! # The real sparse spill components on the original role metadata -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires WireTelescope
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
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
local notation "sizes" => RoleRoom.shape (R:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
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
local notation "ss" => v.widePaidSlices h width bits
local notation "compile" => v.wideEventSlices h width bits
local notation "hi" => v.wideRoleStart h width stock ss
local notation "base" => (sizes).stop hi
local notation "lw" => v.wideWidthLayout h width ss
local notation "lr" => v.wideReserveLayout h width ss
local notation "source" => TerminalLayout.source page
local notation "table" => TerminalLayout.table page
local notation "target" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r rows
local notation "es" => events v.mesh
local notation "cells" => PurchaseInventory.footprint h N k
local notation "K" => Fintype.card (RoleProgram.Old h v.W k rows)

variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
include raw
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "mount" => (P).catalogue.coreMount π (siteNumber h D k) order chk
local notation "value" => v.wideDatedValue h width bits mid chk

set_option maxRecDepth 8192 in
/-- Incoming spill goods and their destination paid edges are read separately,
using the exact repeated-edge count on each original physical row. -/
theorem wide_spill_only_read (j : ℕ) (region : DateSpill.Page) (before final : Memory w)
    (issues : Attempt→CatalystArchive.Entry num width) (pages : v.WideDatedPages h width bits mid chk final issues)
    (sameEdges : region.edges=rows) (sameCore : region.core=ProtocolRAMDateSpillRank.coreCount o)
    (rank : ProtocolRAMDateSpillRank.RankRead mount o region.rankStart region.overflow before final)
    (low : region.overflow.base+region.overflow.size≤region.rankStart)
    (priceRoom : ∀e,routeLoad (mount).ordinary
      (fun x=>RouteSettlement.actual region.overflow before (PurchaseInventory.slot x)) e<2^w)
    (side : Bool) (i : Fin K) :
    let spill:=fun x : Goods h v.W k=>RouteSettlement.actual region.overflow before (PurchaseInventory.slot x)
    let qty : RoleProgram.Old h v.W k rows→ℕ:=Sum.elim (fun e=>if side then routeLoad (mount).ordinary spill e else 0)
      (Sum.elim (fun x=>if side then 0 else spill x) (fun _=>0))
    ((WideCPU.spillOnly (v.wideRoleInventory h width bits (j+1)) region side).eval final (i.val:Word w)).val=
      qty (SettledMatrix.Layout.numbered i) := by
  intro spill qty
  have key:=DatedRoleInput.decoded base final ((lw).bank (j+1)) ((lw).bank (j+1))
    (PrefixReserve.banks lr old (j+1)).reserved (PrefixReserve.banks lr old (j+1)).used pages.metadata pages.physical i
  have word : rows≤2^w:=by
    have card:=v.wide_old_rows h width
    have cap:=pages.physical
    omega
  have count:=ProtocolRAMDateSpillRank.read_load mount o region before final sameEdges sameCore rank word priceRoom
  have stored (x : Goods h v.W k) : (region.overflow.read final ((PurchaseInventory.slot x):Word w)).val=
      RouteSettlement.actual region.overflow before (PurchaseInventory.slot x):=by
    apply congrArg Fin.val
    unfold Bank.read
    apply rank.frame
    exact (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos region.overflow.bits)) _).trans_le low
  have wide : 2<2^w:=by
    apply lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) ?_)
    unfold Native.wordBits
    omega
  have ne:=DatedRoleInput.codes wide
  change (v.wideRoleInventory h width bits (j+1)).kind.eval final (i.val:Word w)=_ ∧
      (v.wideRoleInventory h width bits (j+1)).index.eval final (i.val:Word w)=_ at key
  rcases parts : SettledMatrix.Layout.numbered («r» := rows) (I := Goods h v.W k) («A» := Catalysts h v.W k) i with e|a|b <;>
    simp only [parts,DatedRoleInput.tag,DatedRoleInput.localIndex] at key <;>
    cases side <;> simp [WideCPU.spillOnly,Expr.eval,DescriptorExpr.Comparison.test,beq_iff_eq,
      key.1,key.2,qty,ne.1,Ne.symm ne.1,ne.2.1,ne.2.2,spill,stored,count]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
