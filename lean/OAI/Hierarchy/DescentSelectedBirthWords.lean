import OAI.Hierarchy.DescentCutAcquiredNumerals
import OAI.Hierarchy.DescentSelectedBoardOperandSpan

namespace OAI
/-! The three measured range digits for every real newborn on a selected ordinary date. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open DescentKernelHistory
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 9000
set_option maxHeartbeats 1200000

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
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

variable (ports : DatePorts) (op : RotorSpec) (tailBits drift degree payload seats root : ℕ)
    (ordinary : ℕ → Dated.Ordinary)
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

variable (w shelfHeader headerBase : ℕ) (pos : 0<k)
    (code : DatePorts.OrdinaryCodeRoom ports ticket op g tailBits p f drift degree payload seats root ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom ports ticket op g tailBits p f drift degree payload seats root ordinary
      w shelfHeader headerBase code)

local notation "steps₀" => (v₀).issuedSteps root ports (entry₀) code.signed w (mat₀) (sh₀) code.blocks code.paths
  code.slots code.chip code.endFit code.packed code.radix code.funded
local notation "donors" m:arg => DatePorts.ordinaryDonorMemory ports ticket op g tailBits p f drift degree
  payload seats root ordinary w shelfHeader headerBase pos code exec m
local notation "phys₀" => (v₀).withIssuedSigned
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentPacking.PackedMatch.Local

open DescentLocalArchiveOrder.PaddedOrigin DescentScalarVenueMask DescentPacking.PackedMatch.Local.Stage
open DescentGroupPeerOrder DescentOrdinaryAtomFieldRAM
local notation "trueCap" => prior.placement.cap
local notation "OG" => S.groupCount i

variable {original:Memory w} (stores:CutStores X G S (f:=f) (g:=g) (p:=p) (radix:=radix) ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec original)
local notation "clipSocket" => (entry₀).clip.venue.socket
local notation "dateRows" => BitDescription.scannedRows nonneg T
local notation "seedSite" pair:arg => W.graph.src ((dateRows).pick (pair,0))
local notation "firstSlot" pair:arg => DescentOrdinaryLocalBirth.outgoingSlot A (prior.order.trans Fin.valEmbedding)
  S prior.valid (dateRows).pick (fun other=>(dateRows).picked (other,0)) pair

include before tail cut in
theorem selected_birth_shapes :
    (entry₀).clip.venue.slots=(phys₀).materialFormat.slots ∧
    (bn₀).blocks=(clipSocket).blocks ∧ (bn₀).cap=(clipSocket).cap ∧
    (bn₀).names=(clipSocket).names ∧ (bn₀).widths=(clipSocket).widths ∧
    0<(bn₀).bits ∧ (bn₀).scale=T.z :=by
  let date:=DonorDate.atDate G S g k i p
  have chosen:ticket.donorDate=date:=donor_date_eq X G S br ticket before tail cut
  have degreeAt:prior.placement.degree=date.degree:=congrArg DonorDate.degree chosen
  have short:(v₀).short=max (k+3) (Nat.clog 2 (prior.placement.degree+1)):=by
    change max (k+3) (Nat.clog 2 (date.degree+1))=_
    rw [degreeAt]
  have socketDate:clipSocket=date.format:=by
    change ticket.depotShape (v₀).short=date.format
    rw [short,←chosen]
    rfl
  have sampled:T.Δ=date.degree:=congrArg DonorDate.rankDegree chosen
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change DescentOrdinaryVenueReturn.shapeSlots prior.placement.degree = DescentOrdinaryVenueReturn.shapeSlots T.Δ
    exact congrArg DescentOrdinaryVenueReturn.shapeSlots (degreeAt.trans sampled.symm)
  · rw [socketDate]
    rfl
  · rw [socketDate]
    rfl
  · rw [socketDate]
    rfl
  · rw [socketDate]
    rfl
  · change 0<(DescentOperandWidth.recordBits G S k tailBits drift degree p-2)+2
    omega
  · exact (ticket.grain_on_cut before tail cut br.issuedGrains).symm

section Source
variable {X G S ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec}

/-- The source function used by the acquired seven-page book, restricted to the preceding
original hosts and groups and to the three interval digits. -/
def selectedBirthSource (capacity:(v₀).reference.capacity=trueCap)
    (width:(rc₀).size+2=ports.operandBits)
    (j:Fin (rc₀).operands) (f₀:Fin 3) (block:Block k) (seat:Fin trueCap) (party:Fin 6)
    (host:Fin (Fintype.card prior.V)) (oldGroup:Fin OG) : Cell ports.operandBits :=
  let page:=DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f₀) j
  ((entry₀).bornInput (v₀) stores.inputs floor₀ (mat₀) stores.parts page block
    (seat.cast capacity.symm) party (host.castLE stores.oldFit) oldGroup).cast (congrArg (2^·) width)

/-- Pulling a physical input row back through the group permutation gives exactly the
same source on each of the predecessor's occupied and padded argument columns. -/
theorem selected_birth_source_at (age:i < S.length) (capacity:(v₀).reference.capacity=trueCap)
    (width:(rc₀).size+2=ports.operandBits) :
    let pull:=fun y:Fin (S.groupCount (i+1)*2^k)=>(S.groupDigits age radix).symm (finProdFinEquiv.symm y)
    let fresh:=fun pg x (s₀:Fin trueCap) party h₀ y=>
      ((entry₀).bornInput (v₀) stores.inputs floor₀ (mat₀) stores.parts pg x (s₀.cast capacity.symm)
        party h₀ (pull y)).cast (congrArg (2^·) width)
    ∀(j:Fin (rc₀).operands)(f₀:Fin 3)(block:Block k)(seat:Fin trueCap)(party:Fin 6)
      (host:Fin (Fintype.card prior.V)) y,
      fresh (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f₀) j) block seat party
        (host.castLE stores.oldFit) y=selectedBirthSource stores capacity width j f₀ block seat party host (pull y) :=by
  intros
  rfl

end Source

variable {w shelfHeader headerBase pos code exec}

include before tail cut in
theorem selected_birth_words (_age:i < S.length) (width:(rc₀).size+2=ports.operandBits) :
    let axes:=selected_w_axes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
    ∀(j:Fin (rc₀).operands)(f₀:Fin 3)(pair:(dateRows).pairs)(party:Fin 6),
      let site:=seedSite pair
      (selectedBirthSource stores axes.1 width j f₀ ((A).block site) (firstSlot pair) party
        (prior.vertex ((A).pos site).2) ((A).pos site).1).val =
      if j.val < DescentFreshRoleFields.arity G p T.z ((dateRows).profile choice pair) party then
        DescentRetainedRangeDigits.value DescentTerminalSliceRuns.whole f₀ else 0 :=by
  intro axes j f₀ pair party site
  obtain ⟨slotsAt,blocksAt,capAt,namesAt,widthsAt,live,scaleAt⟩:=
    selected_birth_shapes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
  let host:=(prior.vertex ((A).pos site).2).castLE stores.oldFit
  let group:=((A).pos site).1
  have word:=(PhysicalOrdinary.SelectedBoard.native_operand_span (v₀) stores.oldFit stores.rotor stores.pick
    (donors original) (steps₀).parts stores.board stores.selected (entry₀) stores.inputs floor₀ (mat₀)
    stores.parts rfl rfl slotsAt blocksAt capAt namesAt widthsAt live rfl scaleAt pair party host group
    (by rw [stores.material]; rfl) j f₀)
  dsimp only at word
  simp only [selectedBirthSource,DescentRetainedRangeDigits.value,
    DescentTerminalSliceRuns.whole,ite_self]
  with_unfolding_all exact word

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
