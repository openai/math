import OAI.Hierarchy.DescentIssuedPublicDonor
import OAI.Hierarchy.DescentNamedOrdinaryCode

namespace OAI
/-! # A single static donor program across the different honest choices of a date -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentCompiler DescentCompiler.TerminalScale DescentPacking.PackedMatch.Local.Stage.Dated

/-- Only fixed original parameters and the calendar date enter this constructor. -/
def atDate {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (gain k i p : ℕ) : DonorDate :=
  let a:=forAge S G.b gain k i (Nat.clog 2 (S.hostSize i)) 1 0 0 0 0
  ⟨k,a.D,a.cap,k,a.D,S.grainAt G.b p i,hostRows (S.hostSize i),S.groupCount i,G.b,G.C,G.k⟩

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
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height


include ticket before tail cut in
theorem donor_date_eq : ticket.donorDate=DonorDate.atDate G S g k i p := by
  let ℓ:=Nat.clog 2 (S.hostSize i)
  let a:=forAge S G.b g k i ℓ 1 0 0 0 0
  have metrics:=ordinary_geometry X G S br ticket before tail cut ℓ 1 0 0 0 0
  have deg : (A).degree=a.D:=congrArg Ordinary.D metrics
  have cap : (A).cap=a.cap:=congrArg Ordinary.cap metrics
  have grain : (A).z=S.grainAt G.b p i:=ticket.quantum.symm.trans
    (ticket.grain_on_cut before tail cut br.issuedGrains)
  have typed : T.k=k ∧ T.Δ=(A).degree :=by
    have rateEq:=ticket.sourceRate
    subst rate
    cases eq_of_heq ticket.placement
    exact ⟨rfl,rfl⟩
  change DonorDate.mk k (A).degree (A).cap T.k T.Δ (A).z _ _ _ _ _=
    DonorDate.mk k a.D a.cap k a.D (S.grainAt G.b p i) _ _ _ _ _
  rw [typed.1,typed.2,deg,cap,grain]

include ticket before tail cut in
theorem same_donor_phase (priorBanks : OrdinaryLink.PriorSource) (payload base w : ℕ) :
    ticket.donorDate.fromPrior payload base w priorBanks =
      (DonorDate.atDate G S g k i p).fromPrior payload base w priorBanks :=
  congrArg (fun date : DonorDate=>date.fromPrior payload base w priorBanks)
    (donor_date_eq X G S br ticket before tail cut)

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
