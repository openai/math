import OAI.Hierarchy.DescentNamedSignedReturn
import OAI.Hierarchy.DescentSignedReturnLedger

namespace OAI
/-! # The first four native successor phases are bought on every authentic named cut -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
set_option hygiene false
set_option quotPrecheck false
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ fee} {hu : 0 ≤ u} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=Ht) (t:=S.rounds) S.height
      (initial X S.copies s (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 P bits} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G price fee S k i z D wire s} {T : StageInput W G rate fee}
    {nonneg : 0 ≤ fee} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' wire s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height




open Filter
/-- The cofinal prerequisite depends only on the gadget, public round layout and saving. -/
def Funding (G : PoweredGadget F) (t f g reset ratio payload : ℕ) : Prop :=
  ∀J M tailSize i invoice : ℕ,J≤Nat.log 2 payload → 2^payload≤2*M →
    let S:=stageNumbers G t J f g reset M tailSize
    let R:=ratio*scale J (Chronology.returnRate G t f g reset)
    invoice≤R*MaterialProgram.purchased (S.hostSize i) (S.groupCount i) payload →
    invoice≤S.hostSize i*payload*(R+1)+S.hostSize i*(S.groupCount i*S.radix)*R

theorem eventual_return_funding (G : PoweredGadget F) (t f g reset ratio saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,Funding G t f g reset ratio h :=
  signed_date_funded G t f g reset ratio saving

include before tail cut in
theorem named_return_funded (books : OrdinaryBooks) (frozen payload seats hostLanes : ℕ) (old : ProtocolRAM.Bank)
    (ordinary : ℕ→Ordinary) {t reset J M tailSize : ℕ}
    (cal : S=stageNumbers G t J f g reset M tailSize)
    (kfit : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (floor w ratio : ℕ) (parts adj : ProtocolRAM.Bank) (oldSources : DescentOrdinaryVenueReturn.Sources)
    (input : Operands) (oldRoom : 2*scale J (donorRates G t f g reset).amount≤payload)
    (newRoom : 2*scale J (signedRates G t f g reset).amount≤payload)
    (bus : w≤ratio*payload) (calibrated : Funding G t f g reset ratio payload)
    (age : J≤Nat.log 2 payload) (size : 2^payload≤2*M) :
    let v:=books.onTicket ticket g frozen p f payload seats hostLanes old ordinary
    let R:=ratio*scale J (Chronology.returnRate G t f g reset)
    v.MarkRoom floor input w →
      (v.signedReturnPrefix floor w parts adj oldSources input).wordInvoice≤
        S.hostSize i*payload*(R+1)+S.hostSize i*(S.groupCount i*S.radix)*R := by
  intro v R addresses
  have init : 0<M:=by have positive:=Nat.two_pow_pos payload;omega
  have live : 0<S.hostSize i:=by
    rw [cal]
    exact Nat.mul_pos init (pow_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) _)
  have receipt:=named_return_bill X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary
    cal kfit live floor w ratio parts adj oldSources input addresses oldRoom newRoom bus
  have result:=calibrated J M tailSize i (v.signedReturnPrefix floor w parts adj oldSources input).wordInvoice age size
  rw [←cal] at result
  exact result receipt

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
