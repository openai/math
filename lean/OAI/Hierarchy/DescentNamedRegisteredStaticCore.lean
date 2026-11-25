import OAI.Hierarchy.DescentOrdinaryStaticCore
import OAI.Hierarchy.DescentNamedSignedReturn

namespace OAI
/-! The controls and addresses of a registered ordinary step on a cut of the named history. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.StaticCore
open DescentCompiler DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
noncomputable section

def fromPrefix (d:DonorDate) (a:Dated.Ordinary) (p:SignedProgram) (m:Dated.Measures) : StaticCore :=
  ⟨d,p.material.depot,a,p.signed,p.material.extent,p.entry,p,m⟩

/-- The initial profile repacking moves the true start of the matcher by an amount
determined by its public seat, lane and local pair counts. -/
def profileStart {F:Type} [Field F] (G:PoweredGadget F) (S:AtomSchedule)
    (gain k i p payload seats root:ℕ) :=
  let d:=DonorDate.atDate G S gain k i p
  let a:=d.schedule payload seats (S.censusBits p)
  let packed:ProfileRepack:=⟨seats,DescentPackedEpochShelves.grain (payload/2) G.C,
      a.lanesAt*a.shapeAt.pairs,DescentTerminalEpochBits.width G.C⟩
  packed.endAddress root

def atAge {F:Type} [Field F] (G:PoweredGadget F) (S:AtomSchedule) (gain k i p payload seats root:ℕ)
    (old:ProtocolRAM.Bank) : StaticCore :=
  let d:=DonorDate.atDate G S gain k i p
  let a:=Dated.forAge S G.b gain k i (Nat.clog 2 (S.hostSize i)) (S.censusBits p) payload d.amount
      (DescentTerminalEpochBits.width G.C) seats
  let start:=profileStart G S gain k i p payload seats root
  fromPrefix d a (SignedProgram.atAge G S gain k i p (S.censusBits p) payload d.amount seats start old)
      (Dated.measuresAt S G.b p i)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.StaticCore

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



variable (op:RotorSpec) (frozen drift degree payload seats root:ℕ) (ports:DatePorts)
    (ordinary:ℕ→Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports
local notation "base" => (books).onTicket ticket g frozen p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "v" => DatePorts.ordinaryModel ports ticket op g frozen p f drift degree payload seats root ordinary
local notation "d₀" => DonorDate.atDate G S g k i p
local notation "start" => PhysicalOrdinary.StaticCore.profileStart G S g k i p payload seats root

theorem registered_profile_start : (v).stageStart root=start :=rfl

include before tail cut in
theorem registered_static_core :
    (v).staticCore ((v).stageStart root)=
      PhysicalOrdinary.StaticCore.atAge G S g k i p payload seats root ports.io.roster :=by
  let a:=forAge S G.b g k i (Nat.clog 2 (S.hostSize i)) (S.censusBits p) payload (d₀).amount
      (DescentTerminalEpochBits.width G.C) seats
  have roster:=donor_date_eq X G S br ticket before tail cut
  have census:(base).area=a:=
    ordinary_geometry X G S br ticket before tail cut _ _ _ _ _ _
  have program:=issued_return_program X G S br ticket before tail cut (books) frozen payload seats
      ports.venue.lanes ports.io.roster ordinary start
  have quantities:(⟨(A).wire,(A).z,(A).hist⟩:Measures)=measuresAt S G.b p i:=by
    unfold measuresAt
    rw [prior.edges,prior.atoms,←ticket.quantum,ticket.grain_on_cut before tail cut br.issuedGrains]
  change PhysicalOrdinary.StaticCore.fromPrefix ticket.donorDate (base).area ((base).signedProgram start)
      ⟨(A).wire,(A).z,(A).hist⟩=
    PhysicalOrdinary.StaticCore.fromPrefix d₀ a
      (SignedProgram.atAge G S g k i p (S.censusBits p) payload (d₀).amount seats start ports.io.roster)
      (measuresAt S G.b p i)
  rw [roster,census,program,quantities]

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
