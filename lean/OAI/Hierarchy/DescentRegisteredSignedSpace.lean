import OAI.Hierarchy.DescentNamedSignedReturn
import OAI.Hierarchy.DescentRegisteredOrdinaryStep
import OAI.Hierarchy.DescentDatedSignedSpace

namespace OAI
/-! # Space for the registered ordinary signed return and its earlier geometry tables -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSIMDLookup DescentHaloWalkRAM DescentPacking.PackedMatch.Local.Stage ProtocolRAM
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

variable (op:RotorSpec) (frozen drift degree payload seats root:ℕ) (ports:DatePorts)
    (ordinary:ℕ→Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports
local notation "base" => (books).onTicket ticket g frozen p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "v" => DatePorts.ordinaryModel ports ticket op g frozen p f drift degree payload seats root ordinary

local notation "floor₀" => (v).stageStart root
local notation "sq" => SignedStage.atDate G S g k i (NativePitch.incomingHosts S (i+1))
local notation "rankRoom" w => PriorHeader.Room ports.io.roster (v).area.H (v).signed.groups
  (v).signed.lanes (v).signed.degree ((v).donorEnd floor₀) w

include before tail cut in
theorem registered_signed_room (w:ℕ) (kpos:0<k) (live:0<S.hostSize i)
    (fieldWidth:2*(sq).unit≤payload)
    (matcher:(v).area.Space ports.io w floor₀)
    (envelope:(v).signedGuard floor₀<2^w) :
    (v).SignedRoom floor₀ w ∧ rankRoom w :=by
  have chart:=(issued_return_fields X G S br ticket before tail cut books frozen payload seats
    ports.venue.lanes ports.io.roster ordinary).2.2.2
  have shape : (v).signedLayout.format (v).payload=(v).signed:=
    congrArg (fun a:PhysicalOrdinary F P=>a.signed) chart
  have oldH : (v).signed.priorHosts=(v).area.H:=by rw [←shape];rfl
  have newH : (v).signed.hosts=(v).venue.hosts:=by rw [←shape];rfl
  have deg : (v).signed.degree=(v).area.D:=by rw [←shape];rfl
  have totalG : (v).material.oldGroups=(v).signed.groups*(ticket.depotShape (v).short).blocks:=by
    change S.groupCount i=(v).signed.groups*2^k
    rw [←shape]
    change S.groupCount i = S.groupCount (i+1) * 2^k
    have axes:=Fintype.card_congr (S.groupDigits ticket.hubRows.choose radix)
    simpa only [Fintype.card_fin,Fintype.card_prod] using axes
  have lanes₀ : 0<(v).signed.lanes:=
    (occupancy payload (sq).unit (sq).positive fieldWidth).1
  have oldLe : (v).area.H≤(v).signed.hosts:=by
    rw [newH]
    change hostRows (S.hostSize i)≤NativePitch.incomingHosts S (i+1)
    have grew : 2≤S.radix:=by rw [radix];exact Nat.le_self_pow (by omega) 2
    have hostFactor : 1≤2^S.hostGain:=Nat.two_pow_pos _
    have factor : 2≤2^S.hostGain*S.radix := grew.trans (Nat.le_mul_of_pos_left _ hostFactor)
    calc
      _ ≤ 2*S.hostSize i := hostRows_double live
      _ ≤ (2^S.hostGain*S.radix)*S.hostSize i := Nat.mul_le_mul_right _ factor
      _ = S.hostSize (i+1) := by unfold AtomSchedule.hostSize; rw [pow_succ]; ring
      _ ≤ _ := (NativePitch.hosts_bounds S (i+1) ticket.hubRows.choose).1
  have paid:=(v).signed_room floor₀ w oldH newH lanes₀ (Nat.two_pow_pos _) totalG oldLe envelope
  have grow : floor₀≤(v).donorEnd floor₀ :=by rw [(v).donor_shift];exact Nat.le_add_right ..
  have ppos : 0<(v).signed.reach:=by change 0 < ((v).signed.degree+1)^4;positivity
  have pathWord : (v).signed.reach<2^w:=
    (Nat.le_mul_of_pos_right _ ppos).trans_lt paid.paths
  have degPath : (v).signed.degree≤(v).signed.reach:=by
    change (v).signed.degree≤((v).signed.degree+1)^4
    exact (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  exact ⟨paid,⟨⟨matcher.accessible.roster.1,matcher.accessible.roster.2.1,
      matcher.accessible.roster.2.2.trans grow⟩,by rw [deg];exact matcher.accessible.rosterRoom,
      oldH ▸ paid.old,degPath.trans_lt pathWord,pathWord,paid.header⟩⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
