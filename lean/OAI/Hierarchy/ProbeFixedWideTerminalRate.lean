import OAI.Hierarchy.ProbeFixedWideTerminal
import OAI.Hierarchy.TaggedWireFixedTurnClock
import OAI.Hierarchy.ProbeSiteAddress

namespace OAI
/-! # A uniform native clock and address bounds for the physical turn shelf -/
set_option quotPrecheck false

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope ProbeStage CoreBoard ReportSockets
open CoreRoute HistoryRoles RoleProgram
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits : ℕ)
local notation "P" => v.widePlacement h width
local notation "D" => 2^v.W
local notation "edges" => (P).catalogue.rows
local notation "n" => Fintype.card (Old h v.W k edges)
local notation "entries" => Fintype.card (Slots h D k)
local notation "slots" => WordSeats.room (k:=k) (attempts:=v.wideJobs) v.sampler

open CatalystArchive

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem wide_terminal_board_clock :
    ∃ cost : ℕ,∀ h width bits work,
      (v.wideTerminalBoard h width bits work).extendedTime (v.wideTerminalStock h width bits)≤cost*2^h := by
  obtain ⟨cost,charge⟩:=RoleRoom.fixed_clock v.sampler v.W k v.wideJobs v.depth
  refine ⟨cost,?_⟩
  intro h width bits work
  let directory := WideMemory.dir h v.W k v.wideJobs
  let rank := WideMemory.R v.sampler h v.W k
  let hosts := WideMemory.H h v.W k v.wideJobs
  let keys := WideMemory.K h v.W
  let placement := v.widePlacement h width
  let stockBank := v.fixedTerminalStock placement h width
  let slices := v.widePaidSlices h width bits
  let start := v.wideRoleStart h width stockBank slices
  let payment := (v.wideWidthLayout h width slices).bank (events v.mesh).length
  let settlement := TerminalLayout.settlement (v.wideSignedPage h width stockBank) stockBank
  exact charge h rank hosts (v.wideOrder h width) directory
    (BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth
      keys directory.groups hosts rank)
    placement.catalogue start work (CoreCatalogue.headBase h v.W keys directory.groups hosts)
    (CoreCatalogue.pointBits h v.W) (CoreCatalogue.siteBase h v.W keys) (CoreCatalogue.superStart h v.W)
    keys directory.groups hosts payment stockBank settlement.reserved settlement.used

def wideTerminalVolume := 1+v.rowFactor+CatalystArchive.slotFactor D k+RoleRoom.oldFactor D k v.rowFactor+
  siteFactor D k*WordSeats.room (k:=k) (attempts:=v.wideJobs) v.sampler+
  siteFactor D k+WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler

theorem wide_terminal_volume (work : ℕ) :
    let L:=v.wideTurnWindow h width bits work
    let fixed:=WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler
    1+edges+entries+n+L.sites*L.seats+L.sites+fixed≤v.wideTerminalVolume*2^h := by
  intro L fixed
  have edge:=v.wideCatalogueRows h width
  have route:=slot_count h D k (Nat.two_pow_pos _)
  have original:=RoleRoom.old_bound (W:=v.W) (k:=k) edge
  have sites:=site_count h D k (Nat.two_pow_pos _)
  have grid : L.sites*L.seats≤(siteFactor D k*slots)*2^h := by
    change (siteLast h D k+1)*slots ≤ (siteFactor D k*slots)*2^h
    simpa only [Nat.mul_right_comm (siteFactor D k) (2^h) slots] using Nat.mul_le_mul_right slots sites
  have seats:=Nat.le_mul_of_pos_right fixed (Nat.two_pow_pos h)
  unfold wideTerminalVolume
  simp only [Nat.add_mul,Nat.one_mul]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.two_pow_pos h) edge) route) original) grid) sites) seats

/-- The same fixed coefficient bounds both native locations and the actual instruction
count, for arbitrary ROM and work offsets and every width and bits parameter. -/
theorem wide_terminal_native_rate :
    ∃ rate : ℕ,∀ h width bits rom work,
      let T:=v.wideTerminal h width bits rom work
      let paid:=(v.wideWidthLayout h width (v.widePaidSlices h width bits)).bank (events v.mesh).length
      T.ticks paid≤rate*2^h ∧ v.wideTerminalWorkEnd h width bits work≤work+rate*2^h ∧
        v.wideTerminalROMEnd h width bits rom work≤rom+rate*2^h := by
  obtain ⟨c,charged⟩:=v.wide_terminal_board_clock
  refine ⟨c+7000*v.wideTerminalVolume,?_⟩
  intro h width bits rom work T paid
  let L:=v.wideTurnWindow h width bits work
  let fixed:=WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler
  let rows := (v.widePlacement h width).catalogue.rows
  let slotCount := Fintype.card (Slots h (2^v.W) k)
  let accounts := Fintype.card (Old h v.W k rows)
  have activity:=v.wide_terminal_volume h width bits work
  have bill:=v.wide_terminal_timing h width bits rom work
  have part:=charged h width bits work
  have rr:=(v.wide_terminal_areas h width bits rom work).1
  have ww:=v.wide_terminal_work h width bits work
  have total := Nat.mul_le_mul_left 7000 activity
  have extra : c*2^h+7000*(v.wideTerminalVolume*2^h)=(c+7000*v.wideTerminalVolume)*2^h:=by ring
  rw [← extra]
  constructor
  · change T.ticks paid=T.board.extendedTime T.stock+138+539*(rows+slotCount)+6*rows+
      6096*((rows+slotCount)+accounts)+30*(L.sites*L.seats) at bill
    change T.board.extendedTime T.stock≤c*2^h at part
    change 7000*(1+rows+slotCount+accounts+L.sites*L.seats+L.sites+fixed)≤_ at total
    omega
  · change v.wideTerminalWorkEnd h width bits work≤work+39*accounts+58*rows+51*slotCount+5*(L.sites*L.seats)+20 at ww
    change v.wideTerminalROMEnd h width bits rom work≤rom+52*((rows+slotCount)+accounts)+8*L.sites+4*fixed+22 at rr
    change 7000*(1+rows+slotCount+accounts+L.sites*L.seats+L.sites+fixed)≤_ at total
    constructor <;> omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
