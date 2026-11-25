import OAI.Hierarchy.DescentChosenRegisteredDate
import OAI.Hierarchy.DescentRegisteredPrimitiveFunding

namespace OAI
/-! # Independently paid physical role and operand return buses on a selected ordinary date -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentOrdinaryPalette Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

def registeredRoleRate (t f g reset : ℕ) := 2+(3+(stageNumbers G t 0 f g reset 0 0).localTokenExponent)

theorem role_unit_at (t J f g reset sites last bits : ℕ) (short : bits ≤ scale J 3) :
    let S:=stageNumbers G t J f g reset sites last
    4*Configuration.returnUnit bits S.retainedNodes ≤ scale J (registeredRoleRate G t f g reset) :=by
  intro S
  let a:=(stageNumbers G t 0 f g reset 0 0).localTokenExponent
  have nodes : S.retainedNodes ≤ scale J a:=(S.capacities_scale G).1
  have L : bits*S.retainedNodes ≤ scale J (3+a):=(Nat.mul_le_mul short nodes).trans_eq (scale_mul ..)
  have one : 1 ≤ scale J (3+a):=Nat.two_pow_pos _
  have fit : Configuration.returnUnit bits S.retainedNodes ≤ scale J (3+a):=max_le one L
  have four : 4 ≤ scale J 2:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.mul_le_mul_left 2 (Nat.succ_pos J))
  exact (Nat.mul_le_mul four fit).trans_eq (scale_mul ..)

theorem eventually_role_payload (t f g reset B : ℕ) (bought : registeredRoleRate G t f g reset<B) :
    ∀ᶠ h : ℕ in atTop,2*scale (Nat.log 2 h/(2*B)) (registeredRoleRate G t f g reset)≤h :=
  AgeBound.payload_room _ B bought

end
end Hierarchy.DescentSixParty

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

open DescentDatedOperandReadPipeline
variable (stageFloor : ℕ)
local notation "entry" => (v).datedEntry ports stageFloor
local notation "other" => purchase ((v).withFundedArguments 0 entry).ticketReadGeometry
local notation "ext" => (v).argumentUnitFrom ports stageFloor
local notation "Y" => (v).registeredFrom ports stageFloor
local notation "Q" => SignedStage.atDate G S g k i (NativePitch.incomingHosts S (i+1))
local notation "growth" => 2*(2^S.hostGain*S.radix)
local notation "Z" => NativePitch.incoming S k frozen p f payload ordinary (i+1)





variable {t reset τ β copies driftR degreeMax ratio : ℕ}
local notation "J₀" => Nat.log 2 payload/(2*β)
local notation "startRate" => (NativePitch.FundedBase.public_rate G t f g reset).choose
local notation "funds₀" => 44*argumentDigitRate G t f g reset driftR startRate
local notation "laneR" => returnLaneRate G t f g reset funds₀
local notation "inputs" => (v).registeredEntry ports stageFloor
variable (actual : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (resources : ReturnCalendar G t f g reset driftR (44*argumentDigitRate G t f g reset driftR (NativePitch.FundedBase.public_rate G t f g reset).choose) τ β ratio payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β))) (dr : drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR)
    (degreeRoom : degree≤degreeMax) (bin sockets : ℕ) (openSocket : 0<sockets)
    (split : p=bin*(payload/(16*((sockets*(G.b^(S.rounds*S.height)*G.b))*bin))))
    (archive : DatePorts.ArchiveWidths G S op ports k frozen p drift degree payload i)
    (slots : DatePorts.ArgumentSlots G S ports drift) (pPos : 0<p)


include before tail cut actual resources schedule depth tailBits dr degreeRoom openSocket split archive slots pPos in
theorem chosen_output_pitches (roleWidth : scale J₀ (registeredRoleRate G t f g reset)≤payload) :
    payload≤(Y).resolver.lanes*scale J₀ laneR ∧
      payload≤(Y).palette.nextLanes*scale J₀ (registeredRoleRate G t f g reset) :=by
  have prior:=chosen_registered_resources X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary stageFloor actual resources schedule depth tailBits dr degreeRoom bin sockets openSocket split archive slots pPos
  have first : S.firstWidth G.b p≤payload:=by rw [split];exact S.split_first_width G.b payload bin sockets openSocket
  let b₀:=DescentPrimitivePalette.printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
  have short : b₀ ≤ scale J₀ 3:=actual.printed _ _ (Nat.le_mul_of_pos_right _ G.base_pos) first
  have enough:=(role_unit_at G t J₀ f g reset copies frozen b₀ short)
  dsimp only at enough
  rw [←schedule] at enough
  let u₀:=DescentOrdinaryPalette.Configuration.returnUnit b₀ S.retainedNodes
  have wide : 2*u₀≤payload:=(Nat.mul_le_mul_right u₀ (by decide : 2≤4)).trans (enough.trans roleWidth)
  have density : payload≤(Y).palette.nextLanes*(4*u₀):=by
    change payload ≤ DescentOrdinaryPalette.Configuration.returned payload b₀ S.retainedNodes*(4*u₀)
    simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
      (DescentOrdinaryPalette.Configuration.returned_occupancy payload b₀ S.retainedNodes wide).2
  exact ⟨prior.2.1.2.2,density.trans (Nat.mul_le_mul_left _ enough)⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
