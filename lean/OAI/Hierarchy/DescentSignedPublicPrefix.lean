import OAI.Hierarchy.DescentNamedSignedReturn

namespace OAI
/-! # The four signed-return phases are one common executable even before a ticket is chosen -/
namespace Hierarchy.DescentDatedAddressBook.SignedProgram
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section

theorem atAge_chart {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)
    (gain k i p b payload unit seats floor : ℕ) (old : Bank) :
    (atAge G S gain k i p b payload unit seats floor old).Chart where
  degree:=rfl
  blocks:=rfl
  seats:=by
    let cap:=(DonorDate.atDate G S gain k i p).cap
    change 2^k*cap*11=2^k*(cap*11)
    exact Nat.mul_assoc ..
  markSlots:=rfl

def four (x : SignedProgram) (c : x.Chart) (w : ℕ) (parts adj : Bank)
    (roster : DescentOrdinaryVenueReturn.Sources) (input : Dated.Operands) : NativePhase w :=
  let peers:=DescentOrdinaryVenueReturn.phase roster x.afterMaterial x.material.setup.oldBits
    x.priorHosts x.priorDegree x.nextHosts x.nextDegree w
  (((x.prepared parts adj w).seq peers).seq (x.markedPhase input w)).seq (x.signedPhase c w)

theorem four_congr {x y : SignedProgram} (same : x=y) (cx : x.Chart) (cy : y.Chart)
    (w : ℕ) (parts adj : Bank) (roster : DescentOrdinaryVenueReturn.Sources) (input : Dated.Operands) :
    x.four cx w parts adj roster input=y.four cy w parts adj roster input :=by cases same;rfl

def fourAt {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)
    (gain k i p b payload unit seats floor w : ℕ) (old parts adj : Bank)
    (roster : DescentOrdinaryVenueReturn.Sources) (input : Dated.Operands) : NativePhase w :=
  (atAge G S gain k i p b payload unit seats floor old).four
    (atAge_chart G S gain k i p b payload unit seats floor old) w parts adj roster input

end
end Hierarchy.DescentDatedAddressBook.SignedProgram

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
theorem four_eq (floor w : ℕ) (parts adj : Bank) (roster : DescentOrdinaryVenueReturn.Sources) (input : Dated.Operands) :
    let x:=v.withIssuedSigned
    v.signedReturnPrefix floor w parts adj roster input=
      (x.signedProgram floor).four (x.publicSignedChart floor v.issuedSignedChart) w parts adj roster input :=rfl

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

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



variable (books : OrdinaryBooks) (frozen payload seats hostLanes : ℕ) (old : ProtocolRAM.Bank)
    (ordinary : ℕ→Ordinary)
local notation "v" => books.onTicket ticket g frozen p f payload seats hostLanes old ordinary
local notation "pub" => DonorDate.atDate G S g k i p
local notation "short₀" => max (k+3) (Nat.clog 2 (prior.placement.degree+1))

include before tail cut in
theorem named_public_return (floor w : ℕ) (parts adj : ProtocolRAM.Bank) (roster : DescentOrdinaryVenueReturn.Sources)
    (input : Operands) :
    (v).signedReturnPrefix floor w parts adj roster input=
      SignedProgram.fourAt G S g k i p (S.censusBits p) payload (pub).amount seats floor w old parts adj roster input :=by
  have issuedFields:=issued_return_fields X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary
  have named:=issued_return_program X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary floor
  have issued : (v).withIssuedSigned.signedProgram floor=SignedProgram.atAge G S g k i p (S.censusBits p)
      payload (pub).amount seats floor old:=(congrArg (fun physical : PhysicalOrdinary F P => physical.signedProgram floor) issuedFields.2.2.2).trans named
  exact ((v).four_eq floor w parts adj roster input).trans (SignedProgram.four_congr issued _ _ w parts adj roster input)

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
