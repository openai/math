import OAI.Hierarchy.DescentCutRegisteredHeaderPrefix
import OAI.Hierarchy.DescentSelectedBirthWords
import OAI.Hierarchy.DescentRegisteredBirthChip

namespace OAI
/-! The selected ordinary board's first donor supplies all native newborn header fields. -/
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

open DescentOrdinaryBorn DescentPriorOperandColumns
local notation "axes" => selected_w_axes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
local notation "realChip" => (entry₀).nativeChips (v₀) stores.inputs.toBirthShape stores.parts
local notation "birth_" => header_birth_at (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase)
  (pos:=pos) (code:=code) (exec:=exec) X G S br ticket before tail cut ports op tailBits drift degree
  payload seats root ordinary stores

/-- The packed last group digit is the low radix digit of the same original group. -/
theorem cut_birth_group {sched:AtomSchedule} {age k₀ n₀:ℕ} (live:age<sched.length) (base:sched.radix=2^k₀)
    (same:n₀=sched.groupCount (age+1)*2^k₀) (old:n₀=sched.groupCount age) (i:Fin (sched.groupCount age)) :
    (finProdFinEquiv ((sched.groupDigits live base) i)).cast same.symm=i.cast old.symm :=by
  apply Fin.ext
  exact DatePorts.ordinary_source_number live base i

include before tail cut in
theorem cut_birth_digits (width:(rc₀).size+2=ports.operandBits)
    (j:Fin (vx₀).operands) (pair:(dateRows).pairs) (party:Fin 6) :
    let birthSite:=seedSite pair
    let h:=(prior.vertex ((A).pos birthSite).2).castLE stores.oldFit
    let g₀:=((A).pos birthSite).1
    let h₀:=h.cast stores.inputs.hosts.symm
    let g₁:=g₀.cast stores.inputs.groups.symm
    let donor:=chipDonor (bn₀).format (realChip h₀ g₁)
      (finProdFinEquiv (((A).block birthSite).cast (mat₀).newBlocks.symm,
        (firstSlot pair).cast ((mat₀).newCap.trans (axes).1).symm))
    donor.first=true ∧ (∀s₀,(donor.supplyUnits s₀).val=(((dateRows).profile choice pair).val s₀).val+G.k) ∧
      ∀f₀:Fin 4,(birth_ width j.val f₀ ((A).block birthSite) (firstSlot pair) party (prior.vertex ((A).pos birthSite).2) g₀).val=
        (component (bn₀).bits (pointerAt (bn₀).demand (bn₀).grain (bn₀).scale donor party j.val)
          (f₀.castLE (by decide:4≤7))).val :=by
  intro birthSite h g₀ h₀ g₁ donor
  obtain ⟨slotsAt,blocksAt,capAt,namesAt,widthsAt,_,_⟩:=
    selected_birth_shapes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
  have trueChip:=PhysicalOrdinary.SelectedBoard.dated_donor_span (v₀) stores.oldFit stores.rotor stores.pick
    (donors original) (steps₀).parts stores.board stores.selected pair
  have observed:=(entry₀).native_chip_fields (v₀) stores.inputs.toBirthShape blocksAt capAt namesAt widthsAt stores.parts
    h₀ g₁ (((A).block birthSite).cast (mat₀).newBlocks.symm) ((firstSlot pair).cast ((mat₀).newCap.trans (axes).1).symm)
  dsimp only at trueChip observed
  have first:donor.first=true:=observed.1.trans (by rw [slotsAt,stores.material]; exact trueChip.1)
  have supply (a:Fin 8):(donor.supplyUnits a).val=(((dateRows).profile choice pair).val a).val+G.k:=
    (observed.2 a).trans (by rw [slotsAt,stores.material]; exact trueChip.2 a)
  refine ⟨first,supply,fun f₀=>?_⟩
  have head:=header_birth_read (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase)
    (pos:=pos) (code:=code) (exec:=exec) X G S br ticket before tail cut ports op tailBits drift degree payload seats root
    ordinary stores width j f₀ ((A).block birthSite) (firstSlot pair) party (prior.vertex ((A).pos birthSite).2) g₀
  have byte:=(entry₀).native_chip_byte (v₀) stores.inputs floor₀ (mat₀) stores.parts j
    ((A).block birthSite) ((firstSlot pair).cast (axes).1.symm) party h g₀ f₀
  exact head.trans byte

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
