import OAI.Hierarchy.DescentNamedSignedDate
import OAI.Hierarchy.DescentNextStagePitch
import OAI.Hierarchy.DescentStageVenueChange
import OAI.Hierarchy.DescentCensusPrecision

namespace OAI
/-! # Numeric successor venues at a fixed original ordinary date -/
namespace Hierarchy.DescentSixParty.StageVenueTail.Date
open DescentCompiler DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage.Dated
open DescentMixedRouter
noncomputable section
set_option quotPrecheck false

def ofSigned (q:SignedStage)(countBits sourceLanes payload nextM:ℕ):Date:=
  ⟨q.k,q.newHosts,q.groups,q.newDegree,q.newCap,countBits,sourceLanes,(q.format payload).lanes,sourceLanes,nextM⟩

def atOrdinary {F:Type} [Field F](gadget:PoweredGadget F)(S:AtomSchedule)
    (gain k tail p f payload:ℕ)(ordinary:ℕ→Ordinary)(i sourceLanes:ℕ):Date:=
  ofSigned (SignedStage.atDate gadget S gain k i (NativePitch.incomingHosts S (i+1)))
    (S.censusBits p) sourceLanes payload (NativePitch.incoming S k tail p f payload ordinary (i+1))

theorem atOrdinary_fields {F:Type} [Field F](G:PoweredGadget F)(S:AtomSchedule)
    (gain k tail p f payload:ℕ)(ordinary:ℕ→Ordinary)(i sourceLanes:ℕ):
    let d:=atOrdinary G S gain k tail p f payload ordinary i sourceLanes
    d.hosts=NativePitch.incomingHosts S (i+1) ∧ d.groups=S.groupCount (i+1) ∧ d.paidBits=S.censusBits p ∧
    d.aliveLanes=sourceLanes ∧ d.signedLanes=(SignedStage.signedAt G S gain k i payload).lanes ∧
    d.paidLanes=sourceLanes ∧ d.lanes=NativePitch.incoming S k tail p f payload ordinary (i+1):=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end Hierarchy.DescentSixParty.StageVenueTail.Date

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
theorem venue_date_eq (frozen payload sourceLanes:ℕ)(ordinary:ℕ→Ordinary):
    let H:=NativePitch.incomingHosts S (i+1)
    let q:SignedStage:=⟨k,prior.placement.degree,prior.placement.cap,next.placement.degree,next.placement.cap,
      hostRows (S.hostSize i),H,S.groupCount (i+1),G.b,G.C,G.k⟩
    StageVenueTail.Date.ofSigned q (S.censusBits p) sourceLanes payload
        (NativePitch.incoming S k frozen p f payload ordinary (i+1))=
      StageVenueTail.Date.atOrdinary G S g k frozen p f payload ordinary i sourceLanes:=
  congrArg (fun q=>StageVenueTail.Date.ofSigned q (S.censusBits p) sourceLanes payload
    (NativePitch.incoming S k frozen p f payload ordinary (i+1)))
    (signed_stage_eq X G S br ticket before tail cut (NativePitch.incomingHosts S (i+1)))

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
