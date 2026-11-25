import OAI.Hierarchy.DescentNamedRegisteredWidth
import OAI.Hierarchy.DescentFundedBaseRoom

namespace OAI
/-! On a named trajectory the original actor and preorder registers already fit before the argument purchase. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
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
local notation "feeMultiplier" => price*(wire:ℝ)
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


open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
variable (op : RotorSpec) (frozen drift degree payload seats hostLanes : ℕ) (ports : DatePorts)
variable (old : ProtocolRAM.Bank) (ordinary : ℕ→Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports
local notation "v" => (books).onTicket ticket g frozen p f payload seats hostLanes old ordinary

include before tail cut in
theorem registered_base_width {t reset τ β copies driftR degreeMax:ℕ}
    (grant:ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (schedule:S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth:k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (pRoom:p≤payload) :
    (v).fundedMaxUnit 0≤ scale (Nat.log 2 payload/(2*β)) (NativePitch.FundedBase.public_rate G t f g reset).choose :=by
  let J:=Nat.log 2 payload/(2*β)
  have stamp:=donor_date_eq X G S br ticket before tail cut
  have flags:=issued_return_fields X G S br ticket before tail cut (books) frozen payload seats hostLanes old ordinary
  have pay:=grant.census copies frozen p i g pRoom
  dsimp only at pay
  rw [←schedule,←depth] at pay
  have paid:(v).venue.paidBits≤ticket.donorDate.amount:=by
    change S.censusBits p≤ticket.donorDate.amount
    rw [stamp]
    exact pay
  have h:=(v).initial_unit flags.1 rfl paid flags.2.1.le
  change (v).fundedMaxUnit 0≤NativePitch.FundedBase.upper ticket.donorDate.degree (2^k) ticket.donorDate.cap ticket.donorDate.amount at h
  rw [stamp] at h
  have bound:=(NativePitch.FundedBase.public_rate G t f g reset).choose_spec J copies frozen p i
  dsimp only at bound
  have grouped:k=groupBits t J S.hostGain S.capGain (cutRate t f g):=by rw [schedule];exact depth
  rw [←schedule,←grouped] at bound
  exact h.trans bound

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
