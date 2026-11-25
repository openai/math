import OAI.Hierarchy.DescentNamedOrdinaryTicketAdmission
import OAI.Hierarchy.DescentNamedSignedDate

namespace OAI
/-! The actual ordinary ticket's resource certificate on a cut of the named epoch. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
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


set_option quotPrecheck false
variable (ports : DatePorts) (op : RotorSpec) (tailBits drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books₀" => OrdinaryBooks.atDate G S op g k i p tailBits drift degree payload seats ports
local notation "base₀" => (books₀).onTicket ticket g tailBits p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "floor₀" => (base₀).stageStart root
local notation "v₀" => DatePorts.ordinaryModel ports ticket op g tailBits p f drift degree payload seats root ordinary
local notation "entry₀" => (base₀).registeredEntry ports floor₀
local notation "mat₀" => (base₀).registered_match ports floor₀ (Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift))

include before tail cut in
theorem cut_ticket_admission {w : ℕ} (chart : (v₀).SignedChart) (pg : Fin (7*(v₀).vector.operands))
    (inlet : (entry₀).Room (v₀) floor₀ w) (previous : ports.venue.groups=S.groupCount i)
    (age : i<S.length) (lanes : 0<(v₀).vector.lanes) (room : (v₀).routedStart floor₀<2^w)
    (wide : ∀key,((v₀).wideHead floor₀ chart key).Fits w ((v₀).operandHeaderEnd floor₀))
    (narrow : ∀key,((v₀).narrowHead floor₀ key).Fits w ((v₀).operandHeaderEnd floor₀)) :
    (v₀).TicketAdmission floor₀ w chart (entry₀) (mat₀) pg :=by
  have observed:=signed_stage_eq X G S br ticket before tail cut (NativePitch.incomingHosts S (i+1))
  have field : (v₀).material.fieldBits=(v₀).signedLayout.fieldBits:=congrArg SignedStage.fieldBits observed.symm
  exact DatePorts.ordinary_ticket_admission_fields ports ticket op g tailBits p f drift degree payload seats root ordinary
    chart pg inlet previous age radix lanes field (signed_source_capacity X G S br ticket before tail cut) room wide narrow

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
