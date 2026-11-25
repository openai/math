import OAI.Hierarchy.DescentDatedDonorOutputs
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Execution and two-sided frame of the public donor publisher on arbitrary registers -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentRawCablePanel DescentPacking.PackedMatch.Local DescentHostDegree DescentSIMDLookup
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
set_option quotPrecheck false
namespace DonorDate
variable (d : DonorDate)
variable (payload base : ℕ)
local notation "f" => d.format
local notation "s" => d.matcher
local notation "r" => 2^d.exponent
local notation "K₀" => 2^(d.exponent+1)
local notation "H" => d.hosts
local notation "J" => d.groups
local notation "M" => lanes payload d.amount
local notation "rows" => H*chunks J M
local notation "size" => DepotRAM.Setup.words f s K₀ H J M d.amount
local notation "rootAt" => DonorSpace.dynamicStart base size
local notation "span₀" => DepotRAM.Resident.Dynamic.Placement.endAddress H J M d.degree (DepotRAM.rawBits f) 0
local notation "src" => DonorSpace.source base size span₀ rows
local notation "end₀" => DonorSpace.meterBase base size span₀ rows
local notation "second" => base+DescentSIMDLookup.Book.words (DepotRAM.totalBits f) H J M
local notation "leaf" => second+DepotRAM.Binary.count f*(2*2^(d.amount*M))

variable (w : ℕ) (old : OrdinaryLink.PriorBanks (2^d.exponent) d.degree d.cap (2^(d.exponent+1)))
local notation "addr" => OrdinaryLink.publicAddressed f s K₀ H J M d.amount rootAt second leaf old
local notation "common" => DepotRAM.Resident.addressed f addr H
local notation "tabs" => DepotRAM.Binary.joints f M d.amount second
local notation "inputs" => DepotRAM.Resident.fields f s common H J M
local notation "rom" => DescentSIMDLookup.Book.banks base (DepotRAM.totalBits f) H J M src
local notation "L" => DepotRAM.Resident.Dynamic.Placement.layout H J M d.degree (DepotRAM.rawBits f)
  rootAt old.peers.roster old.hub

/-- Only numeric bounds on addresses and static expression operands are required. -/
structure PhaseRoom : Prop where
  setup : base+size<2^w
  middle : DepotRAM.Resident.Dynamic.Room L r d.degree (2*d.cap) (f).short H J M w (common).terrain
  inputsFit : DepotRAM.FitsInputs f tabs inputs M (src).base w
  finish : DescentSIMDLookup.Fits rom (DepotRAM.totalBits f) (DepotRAM.outputBits f) M H J w (end₀+1)

theorem phase_any_frame (safe : d.PhaseRoom payload base w old) (m : Memory w) :
    (d.phase payload base w old).Runs m ∧
    ∀x, x<base ∨ end₀+1+rows≤x → (d.phase payload base w old).image m x=m x := by
  let profile:=DescentTerminalEpochBits.width d.colors
  let seats:=2^(packExponent 20 d.rankDegree)+2
  let setup:=DepotRAM.Setup.phase f s K₀ H J M d.amount base d.cap profile d.colors d.padding
    d.grain d.branch seats w
  let venue:=DepotRAM.Resident.Dynamic.Placement.issuedPhase H J M d.degree r (2*d.cap) (f).short
    d.cap profile w rootAt old.peers.roster old.hub (common).terrain
  let gather:=DepotRAM.phase tabs inputs rom (end₀+1) H J M w
  let warm:=setup.image m
  let mid:=venue.image warm
  have large : 2*DepotRAM.totalBits f+1≤d.amount :=
    (le_max_right ..).trans (le_max_right ..)
  have put:=DepotRAM.Setup.mount f s K₀ H J M d.amount base d.cap profile d.colors d.padding
    d.grain d.branch seats src old.hub old.born m large safe.setup
  have walk:=DepotRAM.Resident.Dynamic.Placement.any_frame H J M d.degree r (2*d.cap)
    (f).short d.cap profile w rootAt old.peers.roster old.hub (common).terrain safe.middle warm
  have last : gather.Runs mid := DepotRAM.phase_any f tabs inputs rom (end₀+1) H J M w safe.inputsFit safe.finish mid
  constructor
  · intro pcs regs pubs cpu
    exact (setup.seq venue).seq_runs gather m (setup.seq_runs venue m put.1 walk.1) last cpu
  · intro x away
    have base₁ : base+size≤rootAt := by unfold DonorSpace.dynamicStart; omega
    have base₂ : rootAt≤ (src).base := Nat.le_add_right ..
    have base₃ : (src).base+(src).size=end₀ := rfl
    have rowsFit : rows≤ (src).size := safe.finish.srcSize
    have dynEnd : DepotRAM.Resident.Dynamic.Placement.endAddress H J M d.degree (DepotRAM.rawBits f)
        rootAt=(src).base := DepotRAM.Resident.Dynamic.Placement.translate ..
    change ProtocolRAM.image (end₀+1) rows (DescentSIMDLookup.lookup rom)
      (ProtocolRAM.image (src).base rows (DepotRAM.gather tabs inputs) mid) x=m x
    rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by rcases away with h|h <;> omega),
      ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by rcases away with h|h <;> omega)]
    exact (walk.2 x (by
      change x < rootAt ∨ DepotRAM.Resident.Dynamic.Placement.endAddress H J M d.degree (DepotRAM.rawBits f) rootAt ≤ x
      rw [dynEnd]
      rcases away with h|h <;> omega)).trans
      (put.2.2.2.2 x (by rcases away with h|h <;> omega))

/-- The concrete middle phase used after the actual public matcher, for every RAM input. -/
theorem afterMatcher_any (d : DonorDate) (payload seats : ℕ) (input : Stage.Dated.Operands)
    (board floor w : ℕ) (m : Memory w) :
    let a:=d.schedule payload seats board
    let origin:=a.rotationEnd input.roster floor
    let old:=d.matcherOutput payload seats input (a.prepareAt input.roster floor)
    d.PhaseRoom payload origin w old →
      (d.afterMatcher payload seats input board floor w).Runs m ∧
      ∀x,x<origin ∨ d.meterBase payload origin+1+d.hosts*chunks d.groups (lanes payload d.amount)≤x →
        (d.afterMatcher payload seats input board floor w).image m x=m x := by
  intro a origin old safe
  exact d.phase_any_frame payload origin w old safe m

end DonorDate
end
end Hierarchy.DescentSixParty.Chronology

end OAI
