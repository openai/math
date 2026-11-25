import OAI.Hierarchy.TaggedWideDatedSocketFits
import OAI.Hierarchy.ProbeFixedWideDated
import OAI.Hierarchy.ProbeFixedWideDatedCost
import OAI.Hierarchy.ProbeFixedWideFunded
import OAI.Hierarchy.ProbeFixedWideGeometry
import OAI.Hierarchy.TaggedWirePaidFits

namespace OAI
/-! # The real roles, both charted neighbors and original account ordinals fit every chronological sheet -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets
open HistoryRoles RoleProgram CatalystArchive StripChart CatalogueRows ColumnWires
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width : ℕ)
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "dir" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "z" => RoleRoom.shape («R»:=R) v.sampler dir rows
local notation "stock" => v.fixedTerminalStock P h width
local notation "ss" => v.widePaidSlices h width v.maxBits
local notation "start" => v.wideRoleStart h width stock ss
local notation "floor" => v.wideFundedSize h width v.maxBits
local notation "paid" => v.widePaidPorts h width start
local notation "nativeBoard" => v.wideTerminalBoard h width v.maxBits 0
local notation "page" => v.wideSignedPage h width stock

theorem wide_dated_operand_fits (out : ℕ) (prior : floor≤out) (room : out<2^w) :
    (∀b,((nativeBoard).before b).Fits w out) ∧ (v.wideRoleID h width v.maxBits).Fits w out := by
  let owners:=CatalystArchive.sinkBank (v.catalystStaticStart P h width)
    (rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A)))
    (Fintype.card (CoreRoute.Slots h D k)) rows
  obtain ⟨core,bought⟩:=v.wide_catalogue_sources h width (TerminalLayout.settlement page stock)
    (TerminalLayout.source page) (TerminalLayout.table page) (TerminalLayout.destination page) owners
    (((v.wide_funded_extent h width v.maxBits).trans prior).trans_lt room)
  have ext (e : Expr):=ProtocolRAMGeneratedWrite.fits_mono («w»:=w) e ((v.wide_funded_extent h width v.maxBits).trans prior)
  obtain ⟨c₁,c₂,c₃,c₄,c₅⟩:=core
  obtain ⟨b₁,b₂,b₃,b₄,b₅⟩:=bought
  have source : (P).catalogue.core.All (Expr.Fits w out):=⟨ext _ c₁,ext _ c₂,ext _ c₃,ext _ c₄,ext _ c₅⟩
  have quoted : (P).catalogue.bought.All (Expr.Fits w out):=⟨ext _ b₁,ext _ b₂,ext _ b₃,ext _ b₄,ext _ b₅⟩
  let pub:=BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (dir).groups H R
  have raw (b : Bool) : (paid b).Fits w out :=
    RoleRoom.catalogue_fits z (P).catalogue pub v.sampler h v.W k v.depth K (dir).groups H
      (CoreCatalogue.headBase h v.W K (dir).groups H) R (CoreCatalogue.pointBits h v.W)
      (CoreCatalogue.siteBase h v.W K) (CoreCatalogue.superStart h v.W) start
      source quoted rfl prior (prior.trans_lt room) b
  have orig:=RoleRoom.original_fits z start h v.W k (P).catalogue.core paid raw source rfl rfl prior (prior.trans_lt room)
  let g:=v.wideRoleInventory h width v.maxBits 0
  let n:=(z).old
  let base:=(z).stop start
  have endAt : base+n+(RoleROM.bank (base+n) n).size≤out:=
    (RoleRoom.stock_room («R»:=R) v.sampler dir rows start).trans prior
  have bank (b : Bank) (endBound : b.base+b.size≤out) : b.Fits w out :=
    ⟨Nat.two_pow_pos _,by omega,endBound⟩
  have idx : g.index.Fits w out:=⟨bank _ endAt,trivial⟩
  have tag : g.kind.Fits w out:=by
    refine ⟨bank _ ?_,trivial⟩
    change base+ProtocolRAMPurchaseSampler.span n≤out
    change base+n+ProtocolRAMPurchaseSampler.span n≤out at endAt
    omega
  exact ⟨orig,DatedRoleInput.id_fits g _ _ out tag idx⟩

theorem wide_dated_role_fits (ell unitCost rom out : ℕ) (amount : Expr) (prior : floor≤out) (room : out<2^w)
    (size : amount.Fits w out) (stride : rom+ProtocolRAMPurchaseSampler.span (siteLast h D k+1)≤out) :
    let real:=v.wideDated h width ell unitCost
    DatedRoleSheets.Fits real.physical real.chart real.sockets (real.siteStride rom) amount real.ordinal w out := by
  intro real
  obtain ⟨raw,ordinal⟩:=v.wide_dated_operand_fits h width out prior room
  have site : (real.siteStride rom).Fits w out := by
    change 0<2^_ ∧ ProtocolRAMPurchaseSampler.span (siteLast h D k+1)<2^w ∧
      rom+ProtocolRAMPurchaseSampler.span (siteLast h D k+1)≤out
    exact ⟨Nat.two_pow_pos _,by omega,stride⟩
  exact DatedRows.role_fits real.physical z start real.sockets amount real.ordinal _ raw prior
    (prior.trans_lt room) size ordinal site

theorem wide_ordinary_role_fits (ell unitCost rom out : ℕ) (j : Fin ((events v.mesh).length+1))
    (prior : floor≤out) (archive : (v.wideReserveLayout h width ss).scratch≤out) (room : out<2^w)
    (stride : rom+ProtocolRAMPurchaseSampler.span (siteLast h D k+1)≤out) :
    let real:=v.wideDated h width ell unitCost
    DatedRoleSheets.Fits real.physical real.chart real.sockets (real.siteStride rom) (real.amount j) real.ordinal w out :=
  v.wide_dated_role_fits h width ell unitCost rom out _ prior room
    (v.wide_role_fits h width v.maxBits j.val (by omega) out archive room).2 stride

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
