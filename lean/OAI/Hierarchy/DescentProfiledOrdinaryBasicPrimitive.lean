import OAI.Hierarchy.DescentCutPrimitiveArchive
import OAI.Hierarchy.DescentProfiledOrdinaryArgumentTables
import OAI.Hierarchy.DescentProfiledOrdinaryArchiveEntry
import OAI.Hierarchy.DescentBoughtRoleRegister
import OAI.Hierarchy.DescentProfiledOrdinaryArchivePlaces
import OAI.Hierarchy.DescentProfiledAcquireTags

namespace OAI
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 3500
set_option maxHeartbeats 650000

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

variable (w shelfHeader headerBase : ℕ) (pos : 0<k)
    (code : DatePorts.OrdinaryCodeRoom ports ticket op g tailBits p f drift degree payload seats root ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom ports ticket op g tailBits p f drift degree payload seats root ordinary
      w shelfHeader headerBase code)
local notation "wired" m:arg => DatePorts.ordinarySignedMemory ports ticket op g tailBits p f drift degree
  payload seats root ordinary w shelfHeader headerBase pos code exec m


local notation "steps₀" => (v₀).issuedSteps root ports (entry₀) code.signed w (mat₀) (sh₀) code.blocks code.paths
  code.slots code.chip code.endFit code.packed code.radix code.funded
local notation "donors" m:arg => DatePorts.ordinaryDonorMemory ports ticket op g tailBits p f drift degree
  payload seats root ordinary w shelfHeader headerBase pos code exec m
local notation "phys₀" => (v₀).withIssuedSigned
local notation "room₀" => (v₀).signedReturn floor₀ ports.io ports.archive.count (steps₀).parts (steps₀).adjacency w
local notation "page₀" => (⟨0,Nat.mul_pos (by decide : 0<7) code.slots⟩:Fin (7*(vx₀).operands))
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentPacking.PackedMatch.Local

open DescentLocalArchiveOrder.PaddedOrigin DescentScalarVenueMask DescentPacking.PackedMatch.Local.Stage
open DescentGroupPeerOrder DescentOrdinaryAtomFieldRAM
local notation "deg₀" => prior.placement.degree
local notation "shelf" => DescentOrdinaryVenueReturn.shapeSlots deg₀
local notation "pitch₀" => (2^(k+1)-1)*shelf
local notation "trueCap" => prior.placement.cap
local notation "GS" => S.groupCount (i+1)*2^k
local notation "OG" => S.groupCount i
local notation "roleWidth" => (pop₀).roleBits
local notation "nb" => (v₀).reference.nameBits
local notation "mb" => (v₀).reference.countBits


variable {original:Memory w} (stores:CutStores X G S (radix:=radix) (f:=f) (g:=g) (p:=p) ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec original)
local notation "peer_" => hostRotor (prior.vertex.trans (Fin.castLEEmb stores.oldFit))
  (hostRoster prior.placement (prior.vertex.trans Fin.valEmbedding))

open DescentLocalArchiveOrder DescentOrdinaryOriginMask DescentOrdinaryRasterReturn DescentPaidResidentCount
local notation "Hreal" => Fintype.card prior.V
local notation "actualRows" => (entry₀).clip.core.values stores.parts stores.active
local notation "realTokens" => fun x j (v:Fin Hreal) groupIndex=>actualRows x j (v.castLE stores.oldFit) groupIndex
local notation "countSource" => (entry₀).roleValues (v₀) stores.roles
local notation "realCounts" => fun x (v:Fin Hreal) groupIndex=>
  DescentOrdinaryAtomFieldRAM.RoleCounts.count (K:=ports.nodes) mb (countSource x (v.castLE stores.oldFit) groupIndex)
local notation "oldHosts" => prior.vertex.trans (Fin.castLEEmb stores.oldFit)
local notation "rrows" => DescentKernelHistory.BitDescription.scannedRows nonneg T
local notation "newSite" => GadgetNetwork.newSite _ (rrows).pick
  (bestLayout (branchWidth G (fun _:(rrows).pairs=>T.z) ((rrows).profile choice))) (rrows).pack
local notation "origMoves" => rotor A (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding))

open DescentLocalArchiveOrder.PaddedOrigin DescentOrdinaryPrimitiveCheckpoint DescentPrimitivePalette
open DescentKernelHistory DescentGL DescentSharedCableNames DescentRetainedRangeDigits DescentBundleHistory
local notation "Z₀" => S.grainAt G.b p 0
local notation "width_" => printedBits G s Z₀ op
local notation "L_" => (v₀).paletteShape
local notation "stock_" => cut_primitive_stock stores
local notation "chart_" => registered_node_chart X G S br ticket before tail cut op tailBits drift degree payload seats
    ports.venue.lanes ports ports.io.roster ordinary floor₀
local notation "tmp_" => (chart_ ▸ stock_)
local notation "out_" => DatePorts.ordinary (v₀) floor₀
local notation "limit_" => cut_palette_limit X G S br ticket before tail cut
local notation "saxis" => registered_role_axes X G S br ticket before tail cut op tailBits drift degree payload seats
    ports.venue.lanes ports ports.io.roster ordinary floor₀
local notation "final" => DatePorts.ordinaryOutput ports ticket op g tailBits p f drift degree payload seats root ordinary
  w shelfHeader headerBase pos code exec original
set_option maxHeartbeats 800000

open private Origin.archiveOrder from OAI.Hierarchy.DescentNamedPrivateArchive
open private Palette.encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
set_option maxRecDepth 8000
set_option cleanup.letToHave false
variable (menu : Runnable F op)
local notation "extended" => before.ordinary ticket
local notation "startArch" => br.origin.archive
local notation "startOrd" => Origin.archiveOrder br.origin
local notation "startLabels" => Palette.encodedOrigin (p:=p) br.origin op menu
local notation "priorArch" sourceIn:arg wholeIn:arg => (sourceIn:Path br.origin.source _).archive p hp startArch wholeIn
local notation "priorRank" sourceIn:arg wholeIn:arg => trajectory p hp startArch startOrd sourceIn wholeIn
local notation "pathLabels" sourceIn:arg wholeIn:arg fixedIn:arg => encodePath op menu sourceIn hp wholeIn fixedIn startArch startLabels
include tail cut in
private theorem funded_role_at_returned_register {t reset τ β copies driftR degreeMax : ℕ}
    (grant : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (cost : OrdinaryBooks.PrimitiveCalendar G op t f g reset τ β drift degreeMax driftR payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies tailBits)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (frozen : tailBits=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (dr : drift+1≤ scale (Nat.log 2 payload/(2*β)) driftR) (degreeRoom : degree≤degreeMax)
    (grain : p≤payload) (seed : S.firstWidth G.b p≤payload) (hp : 0<p)
    (archive : DatePorts.ArchiveWidths G S op ports k tailBits p drift degree payload i)
    (slots : DatePorts.ArgumentSlots G S ports drift) (low : headerBase<root)

    (whole : (extended).whole p) (fixed : (extended).OnlyRotor op)
    (places : DatePorts.RangeRoom ports prior (priorArch before whole).bit)
    (resident : ∀ x hostIndex groupIndex, (stores.roles x hostIndex groupIndex).val=
      (encode width_ ports.nodes (fun j=>(DatePorts.slotAt ports prior (priorArch before whole).bit (priorRank before whole) places
        (x.cast (congrArg (2^·) places.radix)) j hostIndex (groupIndex.cast places.groups)).elim 0 (fun z=>token G s Z₀ op ((pathLabels before whole fixed).atNode z)))).val)
    (canonical:stores.Canonical) (registered:DatePorts) (memory:Memory w)
    (portsEq:registered=out_) (memoryEq:memory=final) (nextRoom:DatePorts.RangeRoom registered next (priorArch extended whole).bit) :
    ∀x:Fin (2^registered.venue.k), DescentPackedColony.Reads (registered.archive.roles.bank x.val)
      (fun hostIndex groupIndex=>encode width_ registered.nodes (fun j=>(DatePorts.slotAt registered next (priorArch extended whole).bit (priorRank extended whole)
        nextRoom x j hostIndex groupIndex).elim 0 (fun z=>token G s Z₀ op ((pathLabels extended whole fixed).atNode z)))) registered.roleLanes memory := by
  subst registered
  subst memory
  have purchased := cut_primitive_purchased (before:=before) (tail:=tail) (cut:=cut) stores grant cost schedule depth frozen dr degreeRoom grain seed hp archive slots low
  exact cut_primitive_archive X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec stores ticket.hubRows.choose (priorArch before whole) (priorRank before whole) places menu (pathLabels before whole fixed) resident canonical nextRoom _ purchased
end
end Hierarchy.DescentSixParty.SeedNamed.Branch

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Fin.CommRing
noncomputable section
open ProtocolRAM DescentOperandStateBanks DescentPrimitivePalette DescentLocalArchiveOrder DescentBundleHistory DescentKernelHistory
open private claimOnPath branchTrace branchClaim from OAI.Hierarchy.DescentNamedArchivePrefix
open private Origin.archiveOrder from OAI.Hierarchy.DescentNamedPrivateArchive
open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
open private Palette.encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P → ℕ} {d k wire hist i z D w : ℕ} {q ε : ℝ} {U : MarkedWorld F d P bits}
variable {final : ℕ}
private def fieldReturnOnPath
    {U V : MarkedWorld F d P bits} {z D z' D' : ℕ}
    (first : Reached U G q ε S k 0 z D wire hist)
    (last : Reached V G q ε S k final z' D' wire hist) (path : Path first last)
    {p R : ℕ} (hp : 0 < p) (hR : 1 ≤ R) (widths : ∀ y, p ∣ bits y)
    (op : RotorSpec) (menu : Runnable F op) (a : Archive U) (o : Local a.bit)
    (seedShape : WorldShape p R a.bit)
    (names : Encoding (Label G hist z op) (dictionary G op menu p) a.bit) (pin : P → ℕ)
    (claim : PrefixClaim (RunTrace.mk U V z D z' D' first last path) w) : Prop := ∀
    {W : MarkedWorld F d P bits} {j Z D₁ : ℕ} {r : Reached W G q ε S k j Z D₁ wire hist}
    (before : Path first r) (pos : RegisterTimeline.Position) (mem : Memory w)
    (whole : before.whole p) (aligned : before.aligned p R) (rotated : before.OnlyRotor op)
    , claim before pos mem ↔ ∃room : DatePorts.RangeRoom pos.ports r (before.archive p hp a whole).bit,
      DatePorts.ArchiveRead pos.ports r (before.archive p hp a whole).bit
      (trajectory p hp a o before whole) room (archiveShape hp hR widths a seedShape before whole aligned) op
      (encodePath op menu before hp whole rotated a names).atNode
      (Reached.argumentPointer r _ (trajectory p hp a o before whole)
        (archiveShape hp hR widths a seedShape before whole aligned) hp pin pos.ports.argumentsPerNode)
      (archiveFlag r _ (trajectory p hp a o before whole) pos.ports room) mem
omit [Fintype P] in
private theorem fieldReturnOnRealPath
    {U V : MarkedWorld F d P bits} {z D z' D' : ℕ}
    (first : Reached U G q ε S k 0 z D wire hist)
    (last : Reached V G q ε S k final z' D' wire hist) (path : Path first last)
    {p R : ℕ} (hp : 0 < p) (hR : 1 ≤ R) (widths : ∀ y, p ∣ bits y)
    (op : RotorSpec) (menu : Runnable F op) (a : Archive U) (o : Local a.bit)
    (seedShape : WorldShape p R a.bit)
    (names : Encoding (Label G hist z op) (dictionary G op menu p) a.bit) (pin : P → ℕ)
    : fieldReturnOnPath (w:=w) first last path hp hR widths op menu a o seedShape names pin
        (claimOnPath first last path hp hR widths op menu a o seedShape names pin) := by
  intro W j Z D₁ reached before pos mem whole aligned rotated
  dsimp only [claimOnPath, archiveClaim]
  constructor
  · intro saved
    exact saved whole aligned rotated
  · rintro ⟨room, evidence⟩ _ _ _
    exact ⟨room, evidence⟩
end
variable {F : Type} [Field F]
section
variable {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
local notation "wire₀" => S.epochPower^S.priceExponent
local notation "s₀" => S.firstWidth G.b p
local notation "q₀" => (1/((s₀:ℝ)*(wire₀:ℝ)):ℝ)
local notation "ε₀" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "units₀" => q₀*(wire₀:ℝ)
local notation "depthBound_" => GroupStage.depthBound (atRound S.rounds) n f g
local notation "pinSizes_" => (fun _ => dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b) 1)
local notation "widthDiv_" => dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
private theorem fieldReturnOnBranch {he : 0≤ε₀} {hu : 0≤units₀} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (w : ℕ) : fieldReturnOnPath (w:=w) b.origin.source b.target b.path hp stride pinSizes_ op menu
        b.origin.archive (Origin.archiveOrder b.origin) (Origin.archiveShape b.origin p R hp stride widthDiv_)
        (Palette.encodedOrigin (p:=p) b.origin op menu) (fun y=>y.1.val)
        (branchClaim X G S (r:=r) (c:=c) b hp stride op menu w) := by
  exact fieldReturnOnRealPath b.origin.source b.target b.path hp stride pinSizes_ op menu
    b.origin.archive (Origin.archiveOrder b.origin) (Origin.archiveShape b.origin p R hp stride widthDiv_)
    (Palette.encodedOrigin (p:=p) b.origin op menu) (fun y=>y.1.val)
end

end
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Fin.CommRing
noncomputable section
section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
  {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {A : Type*}
  (traces : A → RunTrace G q ε S k wire hist final bits d) {n δ : ℕ} (b : RegisterTimeline.Menu n δ)
  (initial : RegisterTimeline.Position) (c : A)
private def roleOnTrace : Prop :=
  ∀ {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (before : Path (traces c).first r) (after_ : Path r (traces c).last),
    before.append after_ = (traces c).path →
    (RegisterTimeline.calendar (w:=w) traces b initial i).ports.RoleRows ∧
    0 < (RegisterTimeline.calendar (w:=w) traces b initial i).ports.roleLanes
end
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F)
variable {n h C f g p cut tail : ℕ}
variable (t rate τ β siteCount payload : ℕ)
local notation "J₀" => Nat.log 2 payload/(2*β)
set_option quotPrecheck false
local notation "frozen" => DescentCompiler.TerminalScale.tail τ J₀
local notation "S" => stageNumbers G t J₀ f g rate siteCount frozen
local notation "k" => groupBits t J₀ (hostRate t rate) (capRate G t g) (cutRate t f g)
variable (ordinary : OrdinaryRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) cut) (reset : ResetRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) (atRound (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds) n h C f g cut (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))
variable (branch : G.b ≤ 2^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => (S).firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*((S).epochPower^(S).priceExponent:ℝ)):ℝ)
local notation "fee" => ((((S).initialSites*(S).copies:ℕ):ℝ)/(S).epochPower)
local notation "pins" => (Σ _ : Fin (S).copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler.TerminalScale
local notation "board" => reset.board
local notation "op" => RotorSpec.ofRates reset
variable
    (drift degree degreeMax lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial


set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
set_option cleanup.letToHave false





local notation "geom" i => Geometry G S menu k w i (cursor i)

local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g rate).choose
variable {driftR ratio : ℕ}
local notation "funds" => 44*argumentDigitRate G t f g rate driftR baseRate


open DescentPackedEpochShelves
local notation "storage" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "family" => fun i H=>SignedStage.atDate G S g k i H

open DescentPackedProfileTape DescentPackedProfileInstall
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial
local notation "walk₀" votes => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes

open DescentLocalArchiveOrder DescentPrimitivePalette DescentKernelHistory DescentBundleHistory
open private chosenClaim from OAI.Hierarchy.DescentNamedArchivePrefix
attribute [local irreducible] Origin.source Origin.archivePackage issued
local notation "claim" vote:arg => chosenClaim X G S ordinary reset branch positive room shorten w (walk₀ vote)
open private Origin.archiveOrder from OAI.Hierarchy.DescentNamedPrivateArchive
open private Palette.encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
open DescentSIMDLookup DescentPackedColony
local notation "org" vote:arg => (trace (walk₀ vote)).origin
open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
open private register_cap_calendar from OAI.Hierarchy.DescentNamedPrefixState
open private traceAt_kinds from OAI.Hierarchy.DescentNamedBranchMachine
local notation "stride₁" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "fullBranch" vote:arg => trace (walk₀ vote)
local notation "pinDiv" => dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
local notation "pinFactors" => (fun _ : pins=>dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b) 1)
private theorem selectedFieldReturn (votes : (ch).Pin → Bool) :
    fieldReturnOnPath (w:=w) (fullBranch votes).origin.source (fullBranch votes).target (fullBranch votes).path
      positive (le_max_left 1 _) pinFactors op reset.menu (fullBranch votes).origin.archive
      (Origin.archiveOrder (fullBranch votes).origin)
      (Origin.archiveShape (fullBranch votes).origin p stride₁ positive (le_max_left 1 _) pinDiv)
      (Palette.encodedOrigin (p:=p) (fullBranch votes).origin op reset.menu)
      (fun y:pins=>y.1.val) (claim votes) := by
  exact fieldReturnOnBranch X G S (r:=(cert).choose) (c:=walk₀ votes) (trace (walk₀ votes))
    positive (le_max_left 1 _) op reset.menu w
attribute [local irreducible] chosenClaim
private theorem profiledRoleOnTrace
    (votes : (ch).Pin → Bool)
    (placed : ∀ i (e : RunTrace.Events traces i), RegisterTimeline.fitsAt traces menu initial (w:=w) i e)
    (seed : Geometry G S menu k w 0 initial)
    (prior : initial.ports.RoleRows ∧ 0 < initial.ports.roleLanes)
    (palette : OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (input : p ≤ payload) (original : (S).firstWidth G.b p ≤ payload) :
    roleOnTrace (w:=w) traces menu initial (walk₀ votes) := by
  have ample := OrdinaryBooks.PrimitiveCalendar.role_unit G op t f g rate τ β drift degreeMax driftR payload siteCount p
    palette initial.ports (DatePorts.ArchiveWidths.node_bound G S op seed.room.archive) input original
  have moves := all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl
  intro U i z D r before after_ joined
  exact RegisterTimeline.bought_role_registers traces menu initial
    (fun j a b x y => moves j (cursor j) a b x y) placed
    (register_cap_calendar X G S ordinary reset branch positive room shorten menu rfl)
    (traceAt_kinds X G S ordinary reset branch positive room shorten)
    seed (walk₀ votes) prior ample before after_ joined
private abbrev profiledPrimitiveStatement : Prop := ∀ (K headRate : ℕ)
    (_grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (_purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (_returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (_receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (_growth : drift+1 ≤ scale J₀ driftR) (_sites : siteCount≤(2^payload)^2)
    (_input : p≤ payload) (_coeff : degree≤ degreeMax) (_original : (S).firstWidth G.b p≤ payload)
    (_pre : Geometry G S menu k w 0 initial) (_positiveK : 0< k)
    (_headerFits : initial.floor≤2^(headRate*payload)) (_machine : (t+1+max K headRate+2)*payload≤ w)
    (_matcher:MatcherRoom G S k p payload)
    (_signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤ payload)
    (_palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (_nonempty:0< sockets)
    (_split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (_beforeHeader:lo+extent storage (ch).layout≤ header) (_oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (_oldVotes:∀a∈shelves storage lo 0 (ch).layout,∀j:Fin (slots a.src.seats storage),
      m (a.base+j.val)=((packed a.src.pin votes storage j.val).val:Computability.VPVNP.BurstRAM.Word w))
    (_observed:ObservationRoom G S payload w)
    (_seedRoles:initial.ports.RoleRows ∧ 0< initial.ports.roleLanes)
    {W:MarkedWorld F 0 pins widths} {i z D z' D':ℕ} {q:ℝ} {nonneg:0≤fee}
    {prior:Reached W G price fee S k i z D ((S).epochPower^(S).priceExponent) s}
    {T:StageInput W G q fee} {choice:(T.result nonneg).Choice} {norm:Normalize ((T.result nonneg).state choice)}
    {next:Reached norm.result G price fee S k (i+1) z' D' ((S).epochPower^(S).priceExponent) s}
    (ticket:OrdinaryLink prior nonneg T choice norm next)
    (before:Path (traces (walk₀ votes)).first prior) (after:Path next (traces (walk₀ votes)).last)
    (_located:(before.ordinary ticket).append after=(traces (walk₀ votes)).path)
    (_cells:geom i)
    (_old:(cursor i).ports.held prior (cursor i).floor (DateCode.history cpu m i))
    (_accepted:before.selections.length+1<((ch).rows votes).length ∨ (ch).read votes=some (walk₀ votes))
    (_previous:(claim votes) before (cursor i) (DateCode.history cpu m i))
    (_tags:(cursor i).ports.ArchiveTags (DateCode.history cpu m i))
    (whole:(before.ordinary ticket).whole p) (fixed:(before.ordinary ticket).OnlyRotor op)
    (dest:DatePorts.RangeRoom (cursor (i+1)).ports next ((before.ordinary ticket).archive p positive (org votes).archive whole).bit),
    ∀x:Fin (2^(cursor (i+1)).ports.venue.k),Reads ((cursor (i+1)).ports.archive.roles.bank x.val)
      (fun actor group=>DescentSIMDLookup.encode (printedBits G s ((S).grainAt G.b p 0) op) (cursor (i+1)).ports.nodes (fun j=>
        (DatePorts.slotAt (cursor (i+1)).ports next ((before.ordinary ticket).archive p positive (org votes).archive whole).bit (trajectory p positive (org votes).archive (Origin.archiveOrder (org votes)) (before.ordinary ticket) whole) dest x j actor group).elim 0
          (fun y=>token G s ((S).grainAt G.b p 0) op ((encodePath op reset.menu (before.ordinary ticket) positive whole fixed (org votes).archive (Palette.encodedOrigin (p:=p) (org votes) op reset.menu)).atNode y))))
      (cursor (i+1)).ports.roleLanes (DateCode.history cpu m (i+1))

open Lean Elab Term in
local elab "previousFields% " relationship:term:arg inputProof:term:arg : term => do
  let witness ← elabTerm relationship none
  let kind ← Lean.Meta.whnf (← Lean.Meta.inferType witness)
  let both := kind.getAppArgs
  unless kind.getAppFn.isConstOf ``Iff && both.size == 2 do throwError "expected the archive field equivalence"
  let proof ← elabTerm inputProof none
  return mkApp4 (mkConst ``Iff.mp) both[0]! both[1]! witness proof
theorem profiled_ordinary_basic_primitive :
    profiledPrimitiveStatement (driftR:=driftR) (ratio:=ratio) X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial := by
  intro K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes observed seedRoles W i z D z₁ D₁ q nonneg prior T choice norm next ticket before afterBranch located cells old accepted previous tags whole fixed dest
  let suffix := (Path.here.ordinary ticket).append afterBranch
  have together : before.append suffix=(traces (walk₀ votes)).path := (Path.append_cut_assoc before (Path.here.ordinary ticket) afterBranch).symm.trans located
  have structural := prefix_archive_witnesses X G S ordinary reset branch positive room shorten (walk₀ votes) before suffix together
  have field := selectedFieldReturn X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit votes before (cursor i) (DateCode.history cpu m i) structural.1 structural.2.1 structural.2.2
  let available := previousFields% field previous
  let places := Classical.choose available
  have read := Classical.choose_spec available
  have placed (j:ℕ) (e:RunTrace.Events traces j) : RegisterTimeline.fitsAt traces menu initial (w:=w) j e :=
    (profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
      input coeff original pre positiveK headerFits machine j e).1
  have role :=profiledRoleOnTrace X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit
    drift degree degreeMax lo header initial votes placed pre seedRoles palette input original before suffix together
  have entered := profiled_ordinary_archive_entry (driftR:=driftR) (ratio:=ratio)
    X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit board op drift degree degreeMax lo header initial
    K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine
    matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m ticket before afterBranch located cells
    _ _ places _ _ _ _ read role.1
  let layout := Classical.choose entered
  have executable := Classical.choose_spec entered
  let exec := Classical.choose executable
  have output := Classical.choose_spec executable
  let argument := profiled_ordinary_argument_evidence (driftR:=driftR) (ratio:=ratio)
    X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit board op drift degree degreeMax lo header initial
    K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes ticket before afterBranch located cells observed old accepted
    _ _ places _ _ _ _ read role.1 role.2 tags
  let pose := profiled_ordinary_argument_pose (driftR:=driftR) (ratio:=ratio)
    X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit board op drift degree degreeMax lo header initial
    K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes ticket before afterBranch located cells observed old accepted
    _ _ places _ _ _ _ read role.1 role.2 tags
  have low : header < (cursor i).floor := oldHeader.trans_le (RegisterTimeline.initial_below_cursor (RegisterTimeline.issued (w:=w) traces menu) initial i)
  exact Branch.funded_role_at_returned_register X G S (trace (walk₀ votes)) ticket before afterBranch located (cursor i).ports op frozen drift degree payload ((menu).seats i) (cursor i).floor (menu).ordinary w ((menu).profile i) header positiveK layout exec argument.1.1 reset.menu purchase palette rfl rfl rfl growth coeff input original positive cells.room.archive cells.room.args low whole fixed places argument.2.2 pose (cursor (i+1)).ports (DateCode.history cpu m (i+1)) output.2.1 output.2.2.1 dest
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
