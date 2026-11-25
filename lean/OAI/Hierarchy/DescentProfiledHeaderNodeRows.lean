import OAI.Hierarchy.DescentProfiledOrdinaryArgumentTables
import OAI.Hierarchy.DescentHeaderArityFromSpan
import OAI.Hierarchy.DescentDatedRegisteredPointerRows
import OAI.Hierarchy.DescentRegisteredCountFrames
import OAI.Hierarchy.DescentOrdinaryArchivedCounts
import OAI.Hierarchy.DescentProfiledPrefixCensus
import OAI.Hierarchy.DescentOrdinaryRegisteredHeaderRoom
import OAI.Hierarchy.DescentPrefixArgumentCapacity

namespace OAI
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
open scoped Fin.CommRing
set_option cleanup.letToHave false
set_option maxRecDepth 12000
attribute [local irreducible] Origin.source Origin.archivePackage issued
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F)
variable {n h C f g p cut tail : ℕ}
variable (t rate τ β siteCount payload : ℕ)
set_option hygiene false in
local notation "J₀" => Nat.log 2 payload/(2*β)
set_option quotPrecheck false
set_option hygiene false in
local notation "frozen" => DescentCompiler.TerminalScale.tail τ J₀
set_option hygiene false in
local notation "S" => stageNumbers G t J₀ f g rate siteCount frozen
set_option hygiene false in
local notation "k" => groupBits t J₀ (hostRate t rate) (capRate G t g) (cutRate t f g)
variable (ordinary : OrdinaryRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) cut)
    (reset : ResetRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g))
      (atRound (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).capGain) (positive : 0 < p)
    (room : 10*(X.size+1) ≤ (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false in
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
set_option hygiene false in
local notation "run" => (cert).choose
set_option hygiene false in
local notation "last" => Epochs.finish G _ _ run
set_option hygiene false in
local notation "s" => (S).firstWidth G.b p
set_option hygiene false in
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
set_option hygiene false in
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).firstWidth G.b p < 2^w)
set_option hygiene false in
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

set_option hygiene false in
local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
set_option hygiene false in
local notation "price" => (1/((s:ℝ)*((S).epochPower^(S).priceExponent:ℝ)):ℝ)
set_option hygiene false in
local notation "fee" => ((((S).initialSites*(S).copies:ℕ):ℝ)/(S).epochPower)
set_option hygiene false in
local notation "pins" => (Σ _ : Fin (S).copies,Fin (Fintype.card (Port nP X.width)))
set_option hygiene false in
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler.TerminalScale
variable {n₀ δ : ℕ} (board : NonlinearExpanders.Graph n₀ δ) (op : RotorSpec)
    (drift degree degreeMax lo header : ℕ) (initial : RegisterTimeline.Position)
set_option hygiene false in
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
set_option hygiene false in
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial
set_option hygiene false in
local notation "model" i:arg a:arg tick:arg =>
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) (a:RegisterTimeline.Position).floor (menu).ordinary
set_option hygiene false in
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    ((S).firstWidth G.b p) ((S).grainAt G.b p 0) a.ports a.floor
set_option maxHeartbeats 6000000

set_option hygiene false in
local notation "roof" => profiledEnd X G S ordinary reset branch positive room shorten w fit board op frozen drift degree payload lo header initial
set_option hygiene false in
local notation "offer" => ProfiledOrdinaryOffer G f g board op t rate τ drift degreeMax β payload
set_option hygiene false in
local notation "slot" => ProfiledPosition G board op t f g rate τ drift degreeMax β payload

set_option hygiene false in
local notation "guardAt" => profiledGuard X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit board op drift degree lo header initial
set_option hygiene false in
local notation "geom" i => Geometry G S menu k w i (cursor i)
set_option hygiene false in
local notation "numbers" => profiledNumbers X G S ordinary reset branch positive room shorten w fit board op frozen drift degree payload lo header initial
set_option hygiene false in
local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g rate).choose
variable {driftR ratio : ℕ}
set_option hygiene false in
local notation "funds" => 44*argumentDigitRate G t f g rate driftR baseRate

set_option hygiene false in
local notation "execute" => profiledExecution X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
open DescentPackedEpochShelves
set_option hygiene false in
local notation "storage" => DescentPackedEpochShelves.grain (payload/2) G.C
set_option hygiene false in
local notation "family" => fun i H=>SignedStage.atDate G S g k i H

open DescentPackedProfileTape DescentPackedProfileInstall
set_option hygiene false in
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial
set_option hygiene false in
local notation "walk₀" votes => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes

open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentPrimitivePalette DescentOperandStateBanks
set_option hygiene false in
local notation "register" i => (cursor i).ports
set_option hygiene false in
local notation "time" i => (cursor i).floor
set_option hygiene false in
local notation "program" => RegisterTimeline.instruction (w:=w) traces menu initial
set_option hygiene false in
local notation "atDate" fn:arg i:arg tick:arg => fn (register i) tick op g frozen p f drift degree payload
  ((menu).seats i) (time i) (menu).ordinary
section
variable (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤payload) (coeff : degree≤degreeMax) (original : (S).firstWidth G.b p≤payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0<k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤w)
    (matcher:MatcherRoom G S k p payload)
    (signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤payload)
    (palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (nonempty:0<sockets)
    (split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (beforeHeader:lo+extent storage (ch).layout≤header) (oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (oldVotes:∀a∈shelves storage lo 0 (ch).layout,∀j:Fin (slots a.src.seats storage),
      m (a.base+j.val)=((packed a.src.pin votes storage j.val).val:Computability.VPVNP.BurstRAM.Word w))
    {W:MarkedWorld F 0 pins widths} {i z D z' D':ℕ} {q:ℝ} {nonneg:0≤fee}
    {prior:Reached W G price fee S k i z D ((S).epochPower^(S).priceExponent) s}
    {T:StageInput W G q fee} {choice:(T.result nonneg).Choice} {n:Normalize ((T.result nonneg).state choice)}
    {next:Reached n.result G price fee S k (i+1) z' D' ((S).epochPower^(S).priceExponent) s}
    (ticket:OrdinaryLink prior nonneg T choice n next)
    (before:Path (trace (walk₀ votes)).origin.source prior) (after:Path next (trace (walk₀ votes)).target)
    (located:(before.ordinary ticket).append after=(trace (walk₀ votes)).path)
    (cells:geom i) (observed:ObservationRoom G S payload w)
    (old:(register i).held prior (time i) (DateCode.history program m i))
    (accepted:before.selections.length+1<((ch).rows votes).length ∨ (ch).read votes=some (walk₀ votes))
    {kinds:ℕ} (B:BitDescription W) (number:Local B) (places:DatePorts.RangeRoom (register i) prior B)
    (shape:WorldShape p kinds B)
    (labels:NodeOrder.All B→Label G s ((S).grainAt G.b p 0) op) (pointer:NodeOrder.All B→ℕ→Pointer)
    (flags:Fin (2^(register i).venue.k)→Fin (register i).nodes→Fin (register i).operandHosts→Fin (register i).venue.groups→ℕ)
    (stored:DatePorts.ArchiveRead (register i) prior B number places shape op labels pointer flags (DateCode.history program m i))
    (roles:(register i).RoleRows) (positiveRoles:0<(register i).roleLanes)
    (tags:(register i).ArchiveTags (DateCode.history program m i))

set_option hygiene false in
local notation "headerContext" => profiled_ordinary_publication_context (driftR:=driftR) (ratio:=ratio) X G t rate τ β siteCount payload
  ordinary reset branch positive room shorten w fit board op drift degree degreeMax lo header initial K headRate
  grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher
  signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes ticket before after located
  cells observed old accepted B number places shape labels pointer flags stored roles positiveRoles tags

set_option hygiene false in
local notation "core" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload ((menu).seats i) (register i)
set_option hygiene false in
local notation "basis" => (core).onTicket ticket g frozen p f payload ((menu).seats i)
  (register i).venue.lanes (register i).io.roster (menu).ordinary
set_option hygiene false in
local notation "offset" => (basis).stageStart (time i)
set_option hygiene false in
local notation "funded" => model i (cursor i) ticket
set_option hygiene false in
local notation "shapeAt" => (basis).registered_geometry (register i) offset
set_option hygiene false in
local notation "native" => (headerContext).1.1.2
set_option hygiene false in
local notation "booksAt" => (funded).registeredOperandBooks shapeAt (native).1.1.books
set_option hygiene false in
local notation "portsAt" => DatePorts.ordinary funded offset
open DescentRetainedRangeDigits DescentOrdinaryAtomFieldRAM.ScalarOperand

variable (code : (atDate DatePorts.OrdinaryCodeRoom i ticket) w)
    (exec : (atDate DatePorts.OrdinaryExecutionRoom i ticket) w ((menu).profile i) header code)
    (desc₁ : BitDescription n.result) (ord₁ : Local desc₁)
    (sites₁ : DatePorts.RangeRoom portsAt next desc₁) {range₁ : ℕ} (shape₁ : WorldShape p range₁ desc₁)
set_option hygiene false in
local notation "atCell" => DatePorts.slotAt portsAt next desc₁ ord₁ sites₁
set_option hygiene false in
local notation "spanAt" => fun x j=>booksAt x (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page 2) j)
set_option hygiene false in
local notation "measured" => DateCode.history program m i

/-- The acquired seventh field and paid census of the chosen ordinary instruction determine both
archived header pages. The arity is structural at exterior sites as well as paying sites. -/
abbrev profiled_header_node_rows_from_f6
    (maxCount : ∀ y : NodeOrder.All desc₁,(occurrences (shape₁.sites y.1) y.2).length≤(S).retainedArgumentsAt G drift)
    (seventh : ∀x node j host group,(take (a:=(funded).resolver.size+2) node (spanAt x j host group)).val=
      (atCell x node host group).elim 0 (fun y=>atSlot (shape₁.sites y.1) y.2 j.val 2)) :=
  let rows := spanAt
  have printed x j := (native).1.2.2 x (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page 2) j)
  have venue := (headerContext).2
  have mass := profiled_prefix_census X G S ordinary reset branch positive room shorten (walk₀ votes)
    observed.height (before.ordinary ticket) after located
  have cap : ∀ y : NodeOrder.All desc₁,
      (occurrences (shape₁.sites y.1) y.2).length≤(funded).resolver.operands := by
    intro y
    exact (maxCount y).trans (Nat.le_max_right (register i).argumentsPerNode ((S).retainedArgumentsAt G drift))
  have argFit u n : ((shape₁.sites u).recipe positive).arity n≤(funded).resolver.operands:= by
    exact (DescentRetainedRangeDigits.length (shape₁.sites u) n positive).symm.le.trans (cap ⟨u,n⟩)
  have width := DatePorts.ordinary_header_arity_width (register i) ticket op g frozen p f drift degree
    payload ((menu).seats i) (time i) (menu).ordinary cells.room.args
  have headerRows := DatePorts.header_arity_from_f6 (register i) ticket op g frozen p f drift degree
    payload ((menu).seats i) (time i) (menu).ordinary w ((menu).profile i) header positiveK code exec
    desc₁ ord₁ sites₁ shape₁ program m venue.1 venue.2.1 venue.2.2 rows printed positive seventh argFit mass width
  have start : initial.floor≤(time i) := RegisterTimeline.initial_below_cursor
    (issue:=RegisterTimeline.issued (w:=w) traces menu) (initial:=initial) i
  have frame := Branch.ordinary_count_frames X G S (trace (walk₀ votes)) ticket before after located op
    frozen drift degree payload ((menu).seats i) (time i) (register i) (menu).ordinary header (oldHeader.trans_le start)
  have finalRows := DatePorts.ordinary_archived_counts (register i) ticket op g frozen p f drift degree
    payload ((menu).seats i) (time i) (menu).ordinary w ((menu).profile i) header positiveK code exec
    desc₁ ord₁ sites₁ shape₁ measured venue.1 venue.2.1 venue.2.2 rows printed positive cap seventh mass frame.1 frame.2
  And.intro headerRows finalRows

end
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
