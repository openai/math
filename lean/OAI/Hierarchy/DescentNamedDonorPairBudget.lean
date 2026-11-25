import OAI.Hierarchy.DescentNamedMatchedDonor
import OAI.Hierarchy.DescentDonorVisitWordBill
import OAI.Hierarchy.DescentOrdinaryDateBillExact

namespace OAI
/-! # Both real private subprograms of the registered public ordinary date -/
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
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (prior.placement.stage.result nonneg).Choice} {norm : Normalize ((prior.placement.stage.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg prior.placement.stage choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "H" => DescentCompiler.TerminalScale.hostRows (S.hostSize i)
local notation "short" => max (k+3) (Nat.clog 2 ((A).degree+1))
local notation "prof" => DescentTerminalEpochBits.width G.C
local notation "amount" => ticket.installedDonorWidth short prof


open DescentCompiler DescentCompiler.TerminalScale DescentPacking.PackedMatch.Local.Stage
include before tail cut in
theorem private_pair_paid {t J reset M frozen : ℕ}
    (schedule : S=stageNumbers G t J f g reset M frozen)
    (depth : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (payload seats board floor header w ratio : ℕ) (input : Operands) :
    let date:=DonorDate.atDate G S g k i p
    let a:=date.schedule payload seats board
    let base:=a.rotationEnd input.roster floor
    let r:=donorRates G t f g reset
    header ≤ base → 0 < amount → 2*amount ≤ payload → payload ≤ w → w ≤ ratio*payload →
      ticket.wholeDonorEnd short prof H payload base ≤ 2^w →
      0 < S.hostSize i → 2^(payload/2) ≤ S.hostSize i →
      ProtocolRAMPortScale.bitWidth (S.grainAt G.b p i) ≤ S.hostSize i →
      (date.afterMatcher payload seats input board floor w).wordInvoice+
        DateBill.bitTariff ((date.counter payload base header).program w) (date.counter payload base header).ticks ≤ S.hostSize i*payload*(7*(2*ratio)*(1274+6*scale J r.work))+
            S.hostSize i*(S.groupCount i*S.radix)*(7*(2*ratio)*(4*scale J r.amount*(342+2*scale J r.work))) :=by
  intro date a base rates above positive purchase hw wh finish hosts tables grain
  let rom:=a.prepareAt input.roster floor
  let banks:=ticket.matchedBanks payload seats rom (input.ports (A).degree) (fun x j=>input.wire x.val j.val) input.hubs
  let scale_:=ticket.grain_on_cut before tail cut br.issuedGrains
  let r:=ticket.issuedVisit payload base banks above positive purchase hw wh finish scale_
  have code:=matched_code X G S br ticket before tail cut payload seats rom base input above positive purchase hw wh finish
  change ((r.install.seq r.venue).seq r.gather=date.afterMatcher payload seats input board floor w) ∧
    MeterPort.program ticket r.port header w=(date.counter payload base header).program w ∧
    MeterPort.ticks ticket r.port header=(date.counter payload base header).ticks ∧
    MeterPort.hardware ticket r.port=(date.counter payload base header).hardware at code
  have rows:=r.actual_date schedule depth (by rw [radix];positivity) hosts tables grain
  rw [code.1,code.2.1,code.2.2.1] at rows
  exact rows

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
