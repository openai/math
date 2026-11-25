import OAI.Hierarchy.DescentNamedOrdinaryMachine
import OAI.Hierarchy.DescentOrdinaryMountedInlet
import OAI.Hierarchy.DescentIssuedSignedChart

namespace OAI
/-! # Typed admission for the ordinary CPU on the original dated input banks -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 500000

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))} {hu : 0 ≤ (((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ))*((S.epochPower^S.priceExponent):ℝ))} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=(GroupStage.depthBound (atRound S.rounds) n f g)) (t:=S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 ((Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))) ((fun _ : ((Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))))=>(S.firstWidth G.b p)*1))} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G ((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)) ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))}
    {nonneg : 0 ≤ ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G ((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)) ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
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

local notation "core" => PhysicalOrdinary.StaticCore.atAge G S g k i p payload seats root ports.io.roster
local notation "paid" => (StageVenueTail.Date.atOrdinary G S g k frozen p f payload ordinary i ports.venue.lanes).paidBits


local notation "clip" => OrdinaryBooks.purchaseClip G books core ports paid
local notation "purchased" => OrdinaryBooks.purchased G books core ports paid
local notation "entry" => (base).registeredEntry ports ((base).stageStart root)

local notation "argData" => PhysicalOrdinary.bareData G S i payload seats start (S.censusBits p)
  ports core purchased clip
local notation "cap₀" => Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift)
local notation "m₀" => (base).registered_match ports ((base).stageStart root) cap₀
local notation "actual" => (v).bareArguments ((base).stageStart root) entry m₀

local notation "stage" => (v).stageStart root
local notation "rawA" => (base).datedEntry ports stage
local notation "other" => DescentDatedOperandReadPipeline.purchase (((base).withFundedArguments 0 rawA).ticketReadGeometry)

include before tail cut in
theorem ordinary_admission (w : ℕ) (short : payload≤w) (inlet : (entry).Room (v) stage w)
    (endFit : (v).endAddress stage<2^w)
    (fund : (v).FundedRoom stage ((v).fundedFromEntry stage entry
      (m₀).paths) ports.io w)
    (result : (v).ResultRoom stage ((v).reachedSources stage) w) :
    DatePorts.OrdinaryCodeRoom ports ticket op g frozen p f drift degree payload seats root ordinary w :=by
  have fixed:=(issued_return_fields X G S br ticket before tail cut books frozen payload seats
    ports.venue.lanes ports.io.roster ordinary).2.2.2
  have signed : (base).SignedChart:=fixed ▸ (base).issuedSignedChart
  have width : DescentPackedOperand.unit (v).resolver.size*(v).resolver.lanes≤payload/4:=
    ((base).funded_argument_widths rawA other 10).2.2
  have positiveSlots : 0<S.retainedArgumentsAt G drift:=by
    unfold DescentSixParty.AtomSchedule.retainedArgumentsAt DescentSixParty.AtomSchedule.retainedArguments
      DescentCompiler.AtomSchedule.epochPower
    positivity
  exact { signed:=⟨signed.degree, signed.blocks, signed.seats, signed.markSlots⟩,blocks:=rfl,paths:=(m₀).paths,slots:=positiveSlots.trans_le (Nat.le_max_right ..),
          chip:=(entry).chip_fits (v) stage inlet m₀,endFit:=endFit,
          packed:=by rw [Nat.mul_comm];omega
          radix:=rfl,funded:=fund,result:=result }

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
