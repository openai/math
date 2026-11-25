import OAI.Hierarchy.ProbeFixedWideTerminalBoard
import OAI.Hierarchy.TaggedWidePrograms
import OAI.Hierarchy.ProbeFixedWideReplayedTurn
import OAI.Hierarchy.ProtocolRAMTurnStaticWords
import OAI.Hierarchy.ProtocolRAMTurnWindowRun
import OAI.Hierarchy.ProtocolRAMTurnSpace
import OAI.Hierarchy.TaggedWirePublicTurnSeats

namespace OAI
/-! # The fixed calendar's literal terminal code and two forward allocation bounds -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope ProbeStage CoreBoard ReportSockets
open CoreRoute HistoryRoles RoleProgram CatalystArchive
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits : ℕ)
local notation "P" => v.widePlacement h width
local notation "D" => 2^v.W
local notation "K" => WideMemory.K h v.W
local notation "dir" => WideMemory.dir h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "edges" => (P).catalogue.rows
local notation "n" => Fintype.card (Old h v.W k edges)
local notation "entries" => Fintype.card (Slots h D k)
local notation "stock" => v.fixedTerminalStock P h width
local notation "ss" => v.widePaidSlices h width bits
local notation "paid" => (v.wideWidthLayout h width ss).bank (events v.mesh).length
local notation "old" => TerminalLayout.settlement (v.wideSignedPage h width stock) stock
local notation "ownerBase" => v.wideRoleStart h width stock ss
local notation "shape" => RoleRoom.shape («R»:=R) v.sampler dir edges
local notation "names" => (ProtocolRAMTurnGeometry.sourceOrder edges h D k).symm
local notation "geo" => ProtocolRAMTurnGeometry.header (wideRouteOrder h D k)
  (WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler) names
local notation "slots" => WordSeats.room (k:=k) (attempts:=v.wideJobs) v.sampler

def wideTerminalStock := Inventory.ofOriginal ((shape).stop ownerBase) n paid stock (old).reserved (old).used

/-- Reserve sufficient room for the padded last role banks before the weighted counters.
This also covers the raw forward endpoint and width, on different old and paid domains. -/
def wideTerminalRankStart (workStart : ℕ) :=
  let b := v.wideTerminalBoard h width bits workStart
  b.endAt+3*b.old+b.widthBank.size+(b.newRole true).size

def wideTurnWindow (workStart : ℕ) : ProtocolRAMTurnWindow.Layout where
  floor := ProtocolRAMTurnReplayed.endAt (v.wideTerminalRankStart h width bits workStart) (edges+entries) edges
  rows := ProtocolRAMTurnOrder.turns (ProtocolRAMTurnGeometry.length ∘ names)
  sites := siteLast h D k+1
  seats := slots

def wideTerminal (fixedROMStart workStart : ℕ) : WideCPU.Terminal :=
  let T := v.wideTerminalBoard h width bits workStart
  let L := v.wideTurnWindow h width bits workStart
  let lo := v.wideTerminalRankStart h width bits workStart
  let modes := WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler
  let key := ProtocolRAMTurnReplayed.key lo (edges+entries)
  let rank := ProtocolRAMTurnReplayed.rank lo (edges+entries) edges
  { board:=T,«stock»:=v.wideTerminalStock h width bits,rankStart:=lo,«edges»:=edges,routeEntries:=entries,accounts:=old,
    turns:=L.rows,sites:=L.sites,seats:=L.seats,header:=fixedROMStart,headerBits:=ProtocolRAMPackedRanked.groupBits L.rows,
    startColumn:=L.zero,source:=L.src,sourceBits:=L.srcBits,rom:=L.directoryBase fixedROMStart,romBits:=L.romBits,
    base:=L.base,scratch:=L.scratch,sink:=L.sink,
    columns:=⟨T.forwardSite false,T.forwardSite true,T.widthBank,L.site,T.oldRole false,T.oldRole true,
      ProtocolRAMSupergroupDirectory.groupBank (L.halfBase fixedROMStart) (2*modes)⟩,
    heads:=T.newSite true,walk:=T.itinerary key rank }

def wideTerminalROMEnd (fixedROMStart workStart : ℕ) :=
  let L := v.wideTurnWindow h width bits workStart
  L.readOnlyEnd fixedROMStart (WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler)

private theorem readOnlyEnd_of_rows_sites (L M : ProtocolRAMTurnWindow.Layout) (rom roles : ℕ)
    (rows : L.rows = M.rows) (sites : L.sites = M.sites) :
    L.readOnlyEnd rom roles = M.readOnlyEnd rom roles := by
  unfold ProtocolRAMTurnWindow.Layout.readOnlyEnd ProtocolRAMTurnWindow.Layout.halfBase
    ProtocolRAMTurnWindow.Layout.directoryBase ProtocolRAMTurnWindow.Layout.romBits
  rw [rows, sites]

theorem wide_terminal_rom_irrel (rom a b : ℕ) :
    v.wideTerminalROMEnd h width bits rom a=v.wideTerminalROMEnd h width bits rom b :=
  readOnlyEnd_of_rows_sites (v.wideTurnWindow h width bits a) (v.wideTurnWindow h width bits b)
    rom (WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler)
    (Eq.refl (ProtocolRAMTurnOrder.turns (ProtocolRAMTurnGeometry.length ∘ names)))
    (Eq.refl (siteLast h D k+1))

def wideTerminalWorkEnd (workStart : ℕ) := (v.wideTurnWindow h width bits workStart).stop

/-- These three public tables depend on the original source enumeration and charged network
shape. Neither output placements, actual visit sites, the permutation, nor widths appear. -/
def wideTerminalWords {w : ℕ} (fixedROMStart workStart : ℕ) (mem : Memory w) :=
  (v.wideTurnWindow h width bits workStart).install fixedROMStart
    (WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler) geo mem

theorem wide_terminal_count (workStart : ℕ) :
    (v.wideTurnWindow h width bits workStart).rows=(edges+entries)+n :=
  ProtocolRAMTurnSpace.count names

theorem wide_terminal_areas (rom work : ℕ) :
    let L:=v.wideTurnWindow h width bits work
    let lo:=v.wideTerminalRankStart h width bits work
    let roles:=WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler
    v.wideTerminalROMEnd h width bits rom work ≤ rom+52*((edges+entries)+n)+8*L.sites+4*roles+22 ∧
      v.wideTerminalWorkEnd h width bits work ≤ lo+21*(edges+entries)+edges+9+
        30*((edges+entries)+n)+5*(L.sites*L.seats)+7 := by
  intro L lo roles
  have count : L.rows=(edges+entries)+n := v.wide_terminal_count h width bits work
  have readonly := L.readOnly_le rom roles
  have vol := L.stop_le
  have rank := ProtocolRAMTurnReplayed.extent lo (edges+entries) edges
  change L.readOnlyEnd rom roles≤_ ∧ L.stop≤_
  have bound : L.floor=ProtocolRAMTurnReplayed.endAt lo (edges+entries) edges := rfl
  omega

/-- All eleven role columns, their padded last reads, the original-order rank, and
the physical shelf are linear in the two actual catalogues and the installed seats. -/
theorem wide_terminal_work (work : ℕ) :
    let L:=v.wideTurnWindow h width bits work
    v.wideTerminalWorkEnd h width bits work ≤ work+39*n+58*edges+51*entries+5*(L.sites*L.seats)+20 := by
  intro L
  let lo:=v.wideTerminalRankStart h width bits work
  have spanO := ProtocolRAMPurchaseSampler.span_le n
  have spanE := ProtocolRAMPurchaseSampler.span_le edges
  have address : lo=work+4*n+4*edges+3*n+
      ProtocolRAMPurchaseSampler.span n+ProtocolRAMPurchaseSampler.span edges := rfl
  have tail := (v.wide_terminal_areas h width bits 0 work).2
  change v.wideTerminalWorkEnd h width bits work≤lo+21*(edges+entries)+edges+9+
    30*((edges+entries)+n)+5*(L.sites*L.seats)+7 at tail
  omega

theorem wide_terminal_timing (rom work : ℕ) :
    let T:=v.wideTerminal h width bits rom work
    T.ticks paid=T.board.extendedTime T.stock+138+539*(edges+entries)+6*edges+
      6096*((edges+entries)+n)+30*(T.sites*T.seats) := by
  intro T
  have count : T.turns=(edges+entries)+n := v.wide_terminal_count h width bits work
  have time : ProtocolRAMTurnReplayed.time T.rankStart edges entries T.accounts paid=
      66+539*(edges+entries)+6*edges := ProtocolRAMTurnPaidCost.rank_clock ..
  change (T.board.extendedTime T.stock+ProtocolRAMTurnReplayed.time T.rankStart edges entries T.accounts paid)+
    (72+6096*T.turns+30*(T.sites*T.seats))=_
  rw [time,count]
  omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
