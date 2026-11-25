import OAI.Hierarchy.DescentSelectedMatchedBanks
import OAI.Hierarchy.DescentNamedMeterCode

namespace OAI
/-! # Branch-independent code of the complete private update after the real matcher -/
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

include ticket before tail cut in
theorem matched_code (payload seats romBase base : ℕ) (input : Operands) {header w factor : ℕ}
    (past : header≤base) (live : 0<amount) (wide : 2*amount≤payload) (size : payload≤w)
    (ratio : w≤factor*payload) (room : ticket.wholeDonorEnd short prof H payload base≤2^w) :
    let real:=ticket.matchedBanks payload seats romBase (input.ports (A).degree) (fun x j=>input.wire x.val j.val) input.hubs
    let grain:=ticket.grain_on_cut before tail cut br.issuedGrains
    let visit:=ticket.issuedVisit payload base real past live wide size ratio room grain
    let date:=DonorDate.atDate G S g k i p
    let phase:=date.matchedPhase payload seats input romBase base w
    let meter:=date.counter payload base header
    (visit.install.seq visit.venue).seq visit.gather=phase ∧
      MeterPort.program ticket visit.port header w=meter.program w ∧
      MeterPort.ticks ticket visit.port header=meter.ticks ∧ MeterPort.hardware ticket visit.port=meter.hardware := by
  dsimp only
  constructor
  · exact (ticket.matched_phase_eq payload seats romBase base input past live wide size ratio room
      (ticket.grain_on_cut before tail cut br.issuedGrains)).trans
      (congrArg (fun d : DonorDate=>d.matchedPhase payload seats input romBase base w)
        (donor_date_eq X G S br ticket before tail cut))
  · exact ordinary_meter X G S br ticket before tail cut payload base _ past live wide size ratio room

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
