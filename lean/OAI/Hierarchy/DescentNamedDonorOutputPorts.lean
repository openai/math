import OAI.Hierarchy.DescentNamedMatchedDonor

namespace OAI
/-! # All mounted predecessor banks have the same addresses on every accepted history -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentRawCablePanel DescentPackedColony DescentSIMDLookup ProtocolRAM
open DescentPacking.PackedMatch
open DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable (date : DonorDate) (payload seats : ℕ) (old : Dated.Operands) (floor board : ℕ)
local notation "a" => date.schedule payload seats board
local notation "M" => lanes payload date.amount
local notation "H" => date.hosts
local notation "J" => date.groups
local notation "D" => date.degree
local notation "fmt" => date.format
local notation "start" => (a).prepareAt old.roster floor
local notation "base" => (a).rotationEnd old.roster floor
local notation "K" => 2^(date.exponent+1)
local notation "size" => DepotRAM.Setup.words fmt date.matcher K H J M date.amount
local notation "geom" => DonorSpace.dynamicStart base size
local notation "span" => DepotRAM.Resident.Dynamic.Placement.endAddress H J M D (DepotRAM.rawBits fmt) 0
local notation "previous" => date.matcherOutput payload seats old start

/-- Addresses of the five actual resident source fields after the donor scan.
Ranks and hub flags each have one common chart rather than per-outcome metadata. -/
def issuedShelves : DepotRAM.Resident.Addressed fmt K :=
  let second:=base+DescentSIMDLookup.Book.words (DepotRAM.totalBits fmt) H J M
  let leaf:=second+DepotRAM.Binary.count fmt*(2*2^(date.amount*M))
  OrdinaryLink.publicAddressed fmt date.matcher K H J M date.amount geom second leaf previous

structure OutputPorts where
  selected : Bank
  rotation : ℕ
  multiplier : ℕ
  paint : ℕ
  topology : Bank
  births : Bank
  priorHub : Bank
  roster : Bank
  ownerVenue : Bank
  rankChart : Bank
  hubChart : Bank
  packedDonors : Bank
  meter : ℕ
  firstFree : ℕ

/-- Scalar address book derived from the same actual matcher and the same bump
allocation. The array of winners, marks and signed cables is given by matcherOutput. -/
def outputPorts : OutputPorts where
  selected:=(previous).gate
  rotation:=(a).flagEnd old.roster floor+2^date.exponent
  multiplier:=(((a).chooser old.roster floor).shelves D date.exponent board M).mu
  paint:=(((a).chooser old.roster floor).shelves D date.exponent board M).paint
  topology:=(previous).topology
  births:=(previous).born
  priorHub:=(previous).hub
  roster:=(previous).peers.roster
  ownerVenue:=(date.issuedShelves payload seats old floor board).source.owner
  rankChart:=(date.issuedShelves payload seats old floor board).source.ranks.chart
  hubChart:=(date.issuedShelves payload seats old floor board).source.hubs.chart
  packedDonors:=DonorSpace.source base size span (H*chunks J M)
  meter:=date.meterBase payload base
  firstFree:=date.endAddress payload base

local notation "out" => date.outputPorts payload seats old floor board

theorem output_room :
    (out).topology.base+(out).topology.size≤(out).selected.base ∧
    (out).births.base+(out).births.size≤(out).selected.base ∧
    (out).selected.base+(out).selected.size≤(out).rotation ∧
    (out).rotation+1≤(out).packedDonors.base ∧ (out).packedDonors.base+(out).packedDonors.size=(out).meter ∧
    (out).meter+1+H*chunks J M<(out).firstFree := by
  let n:=((a).batch)
  let P:=(a).matcher old.roster floor
  let first:=LayoutSum.Finish.first P.layout.topology P.layout.out n
  let births:=LayoutSum.Finish.births date.matcher M P.layout.topology P.layout.out n
  have lo : (out).topology.base+(out).topology.size≤first :=
    le_max_left (P.layout.topology.base+P.layout.topology.size) _
  have printed : first≤births:=Nat.le_add_right ..
  have window : births+2^(Nat.clog 2 n)≤(out).selected.base:=by
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have begin_ : (out).selected.base+(out).selected.size=(a).flagEnd old.roster floor:=rfl
  have floor_ : (out).rotation+1=base:=rfl
  have abs : base≤(out).packedDonors.base:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have last:=DonorSpace.leaves base size span (H*chunks J M) payload
  exact ⟨lo.trans (printed.trans ((Nat.le_add_right ..).trans window)),window,by rw [begin_];exact Nat.le_add_right ..,
    by rw [floor_];exact abs,rfl,last.2.2.2⟩

end
end Hierarchy.DescentSixParty.Chronology.DonorDate

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
      (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=GroupStage.depthBound (atRound S.rounds) n f g)
      (t:=S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice}
    (br : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ}
variable {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
local notation "A" => prior.placement
variable {nonneg : 0≤(((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (prior.placement.stage.result nonneg).Choice}
    {norm : Normalize ((prior.placement.stage.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg prior.placement.stage choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "H" => DescentCompiler.TerminalScale.hostRows (S.hostSize i)
local notation "short" => max (k+3) (Nat.clog 2 ((A).degree+1))
local notation "prof" => DescentTerminalEpochBits.width G.C
local notation "amount" => ticket.installedDonorWidth short prof

attribute [local irreducible] OrdinaryLink.matchedBanks DonorDate.matcherOutput
set_option maxHeartbeats 750000
include ticket before tail cut in
theorem reached_ports (payload seats board floor : ℕ) (input : Operands) :
    let date:=DonorDate.atDate G S g k i p
    let actual:=ticket.donorDate
    let pub:=date.schedule payload seats board
    let romBase:=pub.prepareAt input.roster floor
    let base:=pub.rotationEnd input.roster floor
    let prev:=ticket.matchedBanks payload seats romBase (input.ports (A).degree)
      (fun x j=>input.wire x.val j.val) input.hubs
    let shelves:=ticket.issuedAddressed payload base prev
    let location:=date.outputPorts payload seats input floor board
    let M:=DescentSIMDLookup.lanes payload amount
    let span:=DescentRawCablePanel.DepotRAM.Resident.Dynamic.Placement.endAddress H (S.groupCount i) M (A).degree
       (DescentRawCablePanel.DepotRAM.rawBits (ticket.depotShape short)) 0
    HEq prev (date.matcherOutput payload seats input romBase) ∧
    actual.outputPorts payload seats input floor board=location ∧
    prev.gate=location.selected ∧ prev.hub=location.priorHub ∧ prev.born=location.births ∧
    prev.topology=location.topology ∧ prev.peers.roster=location.roster ∧
    shelves.source.owner=location.ownerVenue ∧ shelves.source.ranks.chart=location.rankChart ∧ shelves.source.hubs.chart=location.hubChart ∧
    ticket.donorSource short prof H payload base span=location.packedDonors ∧
    ticket.donorMeter short prof H payload base span=location.meter ∧
    ticket.wholeDonorEnd short prof H payload base=location.firstFree ∧
    pub.rotationEnd input.roster floor=location.rotation+1 := by
  dsimp only
  rw [←donor_date_eq X G S br ticket before tail cut]
  rw [ticket.matchedBanks_eq]
  exact ⟨HEq.rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
