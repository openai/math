import OAI.Hierarchy.DescentNamedCutPublishedHeaders
import OAI.Hierarchy.DescentOrdinaryRegisteredRows

namespace OAI
/-! Actual W-page geometry of the two four-hop orderings at a named ordinary cut. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
set_option cleanup.letToHave false
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

open DescentDatedPriorOperand DescentOperandStateBanks DescentHaloWalkRAM DescentSharedCableNames
open PhysicalOrdinary.ArgumentEntry
open DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentRawCablePanel ProtocolRAM
open scoped Classical Fin.CommRing
local notation "sh₀" => (base₀).registered_geometry ports floor₀
local notation "rc₀" => (v₀).resolver
local notation "vx₀" => (v₀).vector
local notation "bn₀" => (v₀).bornBook
local notation "g₀" => (v₀).ticketReadGeometry
local notation "M₀" => (rc₀).lanes
local notation "W₀" => (vx₀).lanes*(vx₀).radix
local notation "vecAt" => (v₀).vectorStart floor₀
local notation "mouthEnd₀" => (v₀).originMouthEnd floor₀
local notation "headerEnd" => (v₀).operandHeaderEnd floor₀
local notation "e₀" => (v₀).material
local notation "fmt₀" => (v₀).ticket.depotShape (v₀).short
local notation "ps₀" => (v₀).operandPathStart floor₀
local notation "refs₀" => ((entry₀).directory (v₀) floor₀ (mat₀)).refs
local notation "Val₀" => References.Rows (v₀).vector (v₀).reference.degree (v₀).reference.k (v₀).reference.oldNodes
  (v₀).reference.capacity ((rc₀).size+2)
local notation "dims₀" => DatePorts.ordinary_header_dimensions ports ticket op g tailBits p f drift degree payload seats root ordinary
local notation "H₀" => (entry₀).clip.venue.hosts
local notation "G₀" => (entry₀).clip.venue.groups
local notation "pop₀" => (entry₀).population (v₀) floor₀
local notation "Active" => Fin H₀→Fin G₀→Cell (1*(entry₀).clip.venue.socket.blocks)
local notation "RealPeers" => Fin H₀→Fin (entry₀).clip.venue.socket.degree→Option (Fin H₀)

theorem registered_walk_adjacency : (entry₀).venue.adjacency=ports.io.roster:=rfl

include before tail cut in
theorem registered_walk_dimensions :
    (vx₀).hosts=(e₀).oldHosts ∧ H₀=(e₀).oldHosts ∧
    breadth (v₀).reference.degree=breadth (fmt₀).degree ∧ 0<(vx₀).lows :=by
  let date:=DonorDate.atDate G S g k i p
  have chosen : ticket.donorDate=date:=donor_date_eq X G S br ticket before tail cut
  have deg : prior.placement.degree=date.degree:=congrArg DonorDate.degree chosen
  refine ⟨rfl,rfl,?_,?_⟩
  · rfl
  · change 0<(2^(k+1)-1)*DescentOrdinaryVenueReturn.shapeSlots date.degree
    apply Nat.mul_pos
    · have positive : 0<2^k:=by positivity
      rw [pow_succ];omega
    · exact Nat.zero_lt_succ _

theorem registered_walk_identity {w} (age : i<S.length) (pg : Fin (vx₀).pageCount) (m : Memory w)
    (form : (entry₀).InputShape (v₀))
    (old : Pages (entry₀).previous.operands→Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin (entry₀).previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits (entry₀).previous))
    (parts : Fin H₀→Fin G₀→DepotRAM.Parts (entry₀).clip.venue.socket)
    (roles : Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin G₀→Cell ((pop₀).roleBits*(pop₀).nodes))
    (active : Active) (hubs : Fin H₀→Cell 1) (peer : RealPeers)
    (oldR : Fin (e₀).oldHosts→Fin (fmt₀).degree→Option (Fin (e₀).oldHosts))
    (inside : (e₀).oldHosts<2^w) (adj : Bank) (atInput : (entry₀).venue.adjacency=adj)
    (owned : ∀h j,m ((entry₀).venue.adjacency.base+h.val*(entry₀).clip.venue.socket.degree+j.val)=(number (peer h j):Word w))
    (priorRead : ∀h j,m (adj.base+h.val*(fmt₀).degree+j.val)=(number (oldR h j):Word w))
    (width : Packed.bits (entry₀).clip.venue.names*(entry₀).clip.actorCount=(v₀).reference.nameBits*(v₀).reference.actors)
    (names : (pop₀).nameBits=(v₀).reference.nameBits) (ranks : (pop₀).donors=(v₀).reference.donors) :
    let groups : G₀=(vx₀).groups*(vx₀).radix:=(dims₀ age radix).2.2.2
    let field:=(entry₀).venueWord (v₀) parts active hubs peer width
    let books : Val₀ (v₀).reference.nameBits (v₀).reference.countBits:=fun col low=>
      groupValues groups ((entry₀).registeredValues (v₀) form floor₀ (mat₀) old parts roles (Gather.reaching peer)
        field names ranks col low)
    ∀q,HEq (books pg q).walks (Gather.reaching oldR) :=by
  intro groups field books q
  exact (entry₀).registered_walks_from_reads (v₀) form floor₀ (mat₀) old parts roles peer oldR
    rfl rfl adj m inside (by simpa only [atInput] using owned) priorRead field names ranks groups pg q

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
