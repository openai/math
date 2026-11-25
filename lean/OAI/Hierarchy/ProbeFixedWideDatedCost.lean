import OAI.Hierarchy.ProbeFixedWideDatedAmounts
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueCost

namespace OAI
/-! # Static resource bounds for the original dated role operands -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires WireTelescope StripDirectory
open ThreeFlat.RAM PhysicalProcedure
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
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
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

def wideRoleWorkBound : ℕ :=
  let flags:=BoughtSockets.wordWork (2^v.W) k v.wideJobs
  let goods:=3*7+29+v.mesh.reserveSteps*(7+13)
  let total:=2*7+3*7+goods+20
  max (2*7+3*7+8) (7+CatalogueRows.edgeWork 7 flags+2*7+total+4)

theorem wide_role_work_at : (v.wideRoleID h width bits).work≤v.wideRoleWorkBound ∧
    ∀j,(v.wideRoleWidth h width bits j).work≤v.wideRoleWorkBound := by
  let flags:=BoughtSockets.wordWork (2^v.W) k v.wideJobs
  let goods:=3*7+29+v.mesh.reserveSteps*(7+13)
  let total:=2*7+3*7+goods+20
  change (v.wideRoleID h width bits).work≤ max (2*7+3*7+8)
      (7+CatalogueRows.edgeWork 7 flags+2*7+total+4) ∧
    ∀j,(v.wideRoleWidth h width bits j).work≤ max (2*7+3*7+8) (7+CatalogueRows.edgeWork 7 flags+2*7+total+4)
  constructor
  · change (DatedRoleInput.id (v.wideRoleInventory h width bits 0) rows cells).work≤_
    rw [DatedRoleInput.id_work]
    exact le_max_left ..
  intro j
  let inv:=v.wideRoleInventory h width bits j
  let val:=DatedRoleInput.nativeAmount v P h width r old source table target owners base lw lr old j
  have lookup : inv.index.work=7:=rfl
  have kind : inv.kind.work=7:=rfl
  have field:=((P).routes.directory.source_work v.sampler h v.W k v.depth (P).routes.oldGroups (P).routes.bins (P).routes.height).2.2.2.1
  have f : (P).catalogue.bought.flag.work≤flags:=field
  have localWidth:=v.prefix_goods_work P h width r old source table target owners j inv.index
  have installed : val.work≤total:=by
    change (DatedRoleInput.amount inv (v.prefix_goods_expr P h width r old source table target owners j inv.index)).work≤total
    rw [DatedRoleInput.amount_work,lookup,kind]
    rw [lookup] at localWidth
    dsimp only [total,goods]
    omega
  have gate:=DatedRoleInput.mask_work (P).catalogue inv val
  have fixed : CatalogueRows.edgeWork 7 (P).catalogue.bought.flag.work≤CatalogueRows.edgeWork 7 flags:=by
    unfold CatalogueRows.edgeWork
    omega
  change (DatedRoleInput.mask (P).catalogue inv val).work≤_
  rw [lookup,kind] at gate
  apply le_trans gate
  apply le_trans _ (le_max_right ..)
  omega

theorem wide_role_work : ∃U:ℕ,∀ h width bits,
    (v.wideRoleID h width bits).work≤U ∧ ∀j,(v.wideRoleWidth h width bits j).work≤U :=
  ⟨v.wideRoleWorkBound,fun h width bits=>v.wide_role_work_at h width bits⟩

theorem wide_prefix_low_heap : (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span cells+1≤(lr).scratch := by
  have starts:=v.wide_prefix_starts h width ss
  have widthBefore : (lw).archive≤(lw).scratch:=Nat.le_add_right ..
  have reserveAfter : (lw).scratch≤(lr).scratch:=Nat.le_add_right ..
  have wide : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<2^page:=Nat.lt_log2_self
  unfold TerminalLayout.footprint at wide
  have initial:=v.wide_initial_room h width
  have low : (A).first≤(A).endAddress v.mesh:=Nat.le_add_right ..
  have span:=ProtocolRAMPurchaseSampler.span_le cells
  omega

theorem wide_role_fits (j : ℕ) (hj : j≤last) (dest : ℕ) (beyond : (lr).scratch≤dest)
    (word : dest<2^w) :
    (v.wideRoleID h width bits).Fits w dest ∧ (v.wideRoleWidth h width bits j).Fits w dest := by
  let inv:=v.wideRoleInventory h width bits j
  have widths : (lw).scratch≤(lr).scratch:=Nat.le_add_right ..
  have archiveStart : (lw).archive≤(lw).scratch:=Nat.le_add_right ..
  have archiveBound : (lw).archive≤dest:=archiveStart.trans (widths.trans beyond)
  have metadata := RoleRoom.stock_room (R:=WideMemory.R v.sampler h v.W k) v.sampler directory rows hi
  change base+K+(RoleROM.bank (base+K) K).size≤(lw).archive at metadata
  have small (b : Bank) (endAt : b.base+b.size≤dest) : b.Fits w dest :=
    ⟨Nat.two_pow_pos _,by omega,endAt⟩
  have idx : inv.index.Fits w dest:=
    ⟨small _ (metadata.trans archiveBound),trivial⟩
  have kind : inv.kind.Fits w dest:=
    ⟨small _ (show base+(RoleROM.bank base K).size≤dest by
      change base+ProtocolRAMPurchaseSampler.span K≤dest
      change base+K+ProtocolRAMPurchaseSampler.span K≤(lw).archive at metadata
      omega),trivial⟩
  have seed:=v.wide_initial_room h width
  have heap : (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span cells+1≤dest:=
    (v.wide_prefix_low_heap h width bits).trans beyond
  have geographic : (A).endAddress v.mesh<2^w:=by omega
  have flag:=(v.wide_catalogue_sources h width old source table target owners geographic).2.2.2.2.1
  have good:=v.prefix_goods_fits P h width r old source table target owners j hj inv.index dest idx seed heap word
  have endBefore (a n t : ℕ) (h : t<n) (bits : ℕ) :
      (a+t*(2^bits+1))+2^bits≤a+n*(2^bits+1) := by
    have step:=Nat.mul_le_mul_right (2^bits+1) (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at step
    omega
  have paid : ((lw).bank j).Fits w dest:=small _
    ((endBefore (lw).archive (last+1) j (Nat.lt_succ_of_le hj) (lw).bits).trans (widths.trans beyond))
  have saved : (PrefixReserve.banks lr old j).reserved.Fits w dest:=small _
    ((endBefore (lr).archive (2*last+2) (2*j) (by omega) (lr).bits).trans beyond)
  have debit : (PrefixReserve.banks lr old j).used.Fits w dest:=small _
    ((endBefore (lr).archive (2*last+2) (2*j+1) (by omega) (lr).bits).trans beyond)
  exact ⟨DatedRoleInput.id_fits _ _ _ _ kind idx,DatedRoleInput.mask_fits (P).catalogue inv _ (ProtocolRAMGeneratedWrite.fits_mono _ (by omega) flag)
    kind idx (DatedRoleInput.amount_fits inv _ _ kind idx paid good saved debit)⟩

namespace WideDatedPages
variable {v h width bits}

/-- Appending the higher rank, role, and endpoint sheets preserves all the
original dated observations. The pre-mask quantity has its own operand bound,
so the statement includes unpurchased original rows as well. -/
theorem frame {init archive m later : Memory w} {issues : Attempt→Entry num width}
    (pages : v.WideDatedPages h width bits init archive m issues) (first : ℕ)
    (heap : (lr).scratch≤first) (word : first<2^w) (keep : ∀a<first,later a=m a) :
    v.WideDatedPages h width bits init archive later issues := by
  have lowHeap:=v.wide_prefix_low_heap h width bits
  have raw : (A).endAddress v.mesh≤first := by omega
  have labels := RoleRoom.stock_room (R:=WideMemory.R v.sampler h v.W k) v.sampler directory rows hi
  change base+K+ProtocolRAMPurchaseSampler.span K≤(lw).archive at labels
  have widthStart : (lw).archive≤(lw).scratch := Nat.le_add_right ..
  have reserveStart : (lw).scratch≤(lr).scratch := Nat.le_add_right ..
  have n:=ProtocolRAMPurchaseSampler.lt_span K
  have flags:=(v.wide_catalogue_sources h width old source table target owners (raw.trans_lt word)).2.2.2.2.1
  refine ⟨pages.metadata.frame (fun a lo inStock => keep a (by omega)),pages.physical,
    (fun a bound=>(keep a (bound.trans_le raw)).trans (pages.low a bound)),?_,?_⟩
  · intro j
    exact (eval_below _ _ m later flags (fun a h =>keep a (h.trans_le raw))).trans (pages.flags j)
  · intro j date i
    have field : (DatedRoleInput.nativeAmount v P h width r old source table target owners base lw lr old j).Fits w first :=
      (v.wide_role_fits h width bits j date first heap word).2.2.2.1
    rw [eval_below _ _ m later field keep]
    exact pages.amount j date i

end WideDatedPages

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
