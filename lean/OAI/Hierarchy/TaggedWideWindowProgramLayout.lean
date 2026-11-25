import OAI.Hierarchy.ProtocolRAMBoughtMaxMetric
import OAI.Hierarchy.TaggedWideWindowLayout
import OAI.Hierarchy.ProbeFixedWideTerminal
import OAI.Hierarchy.TaggedWideTransportMask
import OAI.Hierarchy.TaggedWideFundedAnchors
import OAI.Hierarchy.ProtocolRAMPruneFlag

namespace OAI
/-! # Original held advice and output banks of both purchased-window programs -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard HistoryRoles Tagged ProtocolRAMFrozenWindow
open ProtocolRAMPackedRanked ProtocolRAMSupergroupDirectory Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A : ℝ} (x : WideParent κ A) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
local notation "d" => 2^v.W
local notation "P" => v.widePlacement x.h x.w
local notation "T" => (events v.mesh).length
local notation "g" => (WideMemory.dir x.h v.W k v.wideJobs).groups
local notation "r" => (P).catalogue.rows

/-- A dated lookup may read the full dyadic padding of its physical bank.
Reserve that padding before any supergroup or shorter-format table. -/
def wideGroupROM (dated : WideCPU.Dated T) (bits romStart : ℕ) :=
  v.wideTerminalROMEnd x.h x.w bits (dated.romEnd romStart) 0+2*dated.romEnd romStart+2

def wideLayersROM (dated : WideCPU.Dated T) (bits romStart : ℕ) :=
  v.wideGroupROM x dated bits romStart+2*span g

def wideFormatROM (dated : WideCPU.Dated T) (bits romStart : ℕ) :=
  v.wideLayersROM x dated bits romStart+2^groupBits (siteLast x.h d k+1)

/-- The final immutable end depends only on public capacities and earlier public
ROM lengths. The original signed pass occupies the region below romStart. -/
def wideFormatEnd (cap : ℕ) (dated : WideCPU.Dated T) (bits romStart : ℕ) :=
  v.wideFormatROM x dated bits romStart+(m+1)*v.wideWindowStride x ell cap

theorem wide_terminal_before_groups (dated : WideCPU.Dated T) (bits romStart workStart : ℕ) :
    v.wideTerminalROMEnd x.h x.w bits (dated.romEnd romStart) workStart≤v.wideGroupROM x dated bits romStart := by
  rw [v.wide_terminal_rom_irrel x.h x.w bits (dated.romEnd romStart) workStart 0]
  unfold wideGroupROM
  omega

theorem wide_dated_ballot_guard (cap : ℕ) (dated : WideCPU.Dated T) (bits romStart : ℕ) :
    3*dated.romEnd romStart+2≤v.wideFormatEnd x m ell cap dated bits romStart := by
  have later : dated.romEnd romStart≤v.wideTerminalROMEnd x.h x.w bits (dated.romEnd romStart) 0 := by
    unfold wideTerminalROMEnd ProtocolRAMTurnWindow.Layout.readOnlyEnd ProtocolRAMTurnWindow.Layout.halfBase
      ProtocolRAMTurnWindow.Layout.directoryBase
    exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have guard : 3*dated.romEnd romStart+2 ≤ v.wideGroupROM x dated bits romStart := by
    unfold wideGroupROM
    omega
  unfold wideFormatEnd wideFormatROM wideLayersROM
  exact ((guard.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)

def widePruneBank (dated : WideCPU.Dated T) (bits romStart : ℕ) : Bank :=
  ⟨v.wideLayersROM x dated bits romStart,groupBits (siteLast x.h d k+1)⟩

def widePruneLayout := boardLayout x.h d k x.w (CatalystArchive.fuel v.mesh*x.w)

def widePruneBound :=
  2*v.radius*(∑ _ : Fin k,Fintype.card (Columns x.h d)*(CatalystArchive.fuel v.mesh*x.w))-2^x.h*x.w

/-- Actual printed endpoints, metrics and group word are carried by the retained
original terminal tape. The per-type selectors address one shared packed group
and two already-packed, lane-scaled row slots. -/
def wideWindowProgramLayout (cap : ℕ) (dated : WideCPU.Dated T) (bits romStart : ℕ)
    : WideCPU.Layout m :=
  let first:=v.wideFormatROM x dated bits romStart
  let start:=v.wideFormatEnd x m ell cap dated bits romStart
  let base:=v.wideTerminalWorkEnd x.h x.w bits (dated.workEnd start)
  let fmt:=v.wideWindow x m ell short u δ ξ cap first
  let need:=fun i=>(fmt i).window.stop 0
  let groups:=v.wideGroupROM x dated bits romStart
  let dst:=CatalystArchive.TerminalLayout.destination (v.wideSignedPage x.h x.w (v.fixedTerminalStock P x.h x.w))
  let ends:=RoleROM.bank dst (3*r)
  let metrics:=RoleROM.bank (dst+3*r) (3*r)
  let gates:=RoleROM.bank (dst+6*r) (3*r)
  let args : ProtocolRAMFrozenWindow.Inputs :=
    { owner:=PruneFlag.field gates 0, directory:=groupBank groups g,offset:=offsetBank groups g,
      left:=dated.slotBank start false,right:=dated.slotBank start true,width:=dated.stageWidth start,bias:=ends,classes:=ends,weights:=ends,origins:=ends }
  { tagScratch:=start, scatterLast:=WideCPU.Dated.last T,scatter:=dated.sheets romStart start,
    terminal:=v.wideTerminal x.h x.w bits (dated.romEnd romStart) (dated.workEnd start),
    windows:=fmt,inputs:=fun i=>(fmt i).publicInputs args,floor:=base,
    pruneScratch:=WindowSeries.finish base need,pruneRows:=r,
    lengthCode:=BoughtSockets.Public.maxMetric v.radius,threshold:=v.widePruneBound x,
    ends:=ends,metrics:=metrics,layers:=v.widePruneBank x dated bits romStart }

theorem wideWindowProgramLayout_windows (cap : ℕ) (dated : WideCPU.Dated T) (bits romStart : ℕ) :
    (v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).windows=
    v.wideWindow x m ell short u δ ξ cap (v.wideFormatROM x dated bits romStart) := rfl

theorem wideWindowProgramLayout_stop (cap : ℕ) (dated : WideCPU.Dated T) (bits romStart : ℕ) :
    let l:=v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart
    WindowSeries.finish l.floor l.need=l.pruneScratch := rfl


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
