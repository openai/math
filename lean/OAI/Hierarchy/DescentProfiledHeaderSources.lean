import OAI.Hierarchy.ProofField
import OAI.Hierarchy.DescentRegisteredSpanReturn
import OAI.Hierarchy.DescentAcceptedOrdinaryTagSources
import OAI.Hierarchy.DescentRegisteredAcceptedArguments
import OAI.Hierarchy.DescentNamedProfiledOrdinaryAdvance
import OAI.Hierarchy.DescentProfiledOrdinaryArchiveEntry
import OAI.Hierarchy.DescentProfiledOrdinaryArgumentTables
import OAI.Hierarchy.DescentRegisteredHeaderReturn
import OAI.Hierarchy.DescentRegisteredHeaderArity

namespace OAI
/-! The clocked ordinary register transition, selected board and operand returns on the original accepted profile. -/

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

open Lean Elab Term in
local elab "profiledHeaderPublication% " body:term : term => elabTerm body none

/-- Apply the native ordinary header writer at the actual registered date. Its
remaining arguments describe the true node numbering and earlier resolver fragments at this
same cut. Both native operand strips and the identity of the returned cursor are taken
from the reached ballot and previous archive. -/
noncomputable def profiled_field_publications := profiledHeaderPublication%
  let evt:RunTrace.Events traces i:=⟨walk₀ votes,.ordinary before ticket after located⟩
  let at_:=cursor i
  let v:=model i at_ ticket
  have dates:=profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine i evt
  have axis:=dates.2 cells
  have envelope:0<v.resolver.lanes ∧ v.fullEnd at_.floor<2^w:=axis.1
  have extra:max (v.fullEnd at_.floor) (v.signedGuard (v.stageStart at_.floor))<2^w:=axis.2
  have word:payload≤w:=(Nat.le_mul_of_pos_left _ (by omega:0<t+1+max K headRate+2)).trans machine
  have live:i<(S).length:=ticket.hubRows.choose
  have code:=Branch.registered_geometry_fits X G S (trace (walk₀ votes)) ticket before after located op frozen drift
    degree payload at_.floor at_.ports (menu).ordinary board (menu).seats (menu).profile header w live word cells
    cells.degree ⟨rfl,rfl⟩ envelope.1 envelope.2
  have calibrated :=profiled_calibrated_execution X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader
    oldHeader i evt cells
  let tables₀ := (headerContext).1.1.1.1
  have posted:=tables₀.2.2.1
  let issuedRows := tables₀.2.2.2
  have start:initial.floor≤at_.floor:=RegisterTimeline.initial_below_cursor (RegisterTimeline.issued (w:=w) traces menu) initial i
  have frame:=Branch.ordinary_header_frames X G S (trace (walk₀ votes)) ticket before after located op
    frozen drift degree payload ((menu).seats i) at_.floor at_.ports (menu).ordinary header (oldHeader.trans_le start)
  have numericalWidths :=DatePorts.ordinary_widths G S op at_.ports ticket g frozen p f drift degree payload
    ((menu).seats i) at_.floor (menu).ordinary
  have packed:v.finalChart.field*v.resolver.nodes*v.resolver.lanes≤w:=
    numericalWidths.operands.trans ((Nat.div_le_self ..).trans word)
  let heads:=DatePorts.header_return_at_cursor at_.ports ticket op g frozen p f drift degree payload
    ((menu).seats i) at_.floor (menu).ordinary w ((menu).profile i) header positiveK code (calibrated code)
    program m posted.1 posted.2.1 frame.1 frame.2 live cells.room.args packed issuedRows.1 issuedRows.2
  let spans:=DatePorts.span_return_at_cursor at_.ports ticket op g frozen p f drift degree payload
    ((menu).seats i) at_.floor (menu).ordinary w ((menu).profile i) header positiveK code (calibrated code)
    program m posted.1 posted.2.1 frame.1 frame.2 packed issuedRows.1 issuedRows.2
  let values:=DatePorts.range_values_at_cursor at_.ports ticket op g frozen p f drift degree payload
    ((menu).seats i) at_.floor (menu).ordinary w ((menu).profile i) header positiveK code (calibrated code)
    program m posted.1 posted.2.1 frame.1 frame.2 packed issuedRows.1 issuedRows.2
  @PProd.mk (PProd (type_of% heads) (type_of% spans)) (type_of% values) (@PProd.mk (type_of% heads) (type_of% spans) heads spans) values

set_option hygiene false in
local notation "fieldExit" => profiled_field_publications (driftR:=driftR) (ratio:=ratio) X G t rate τ β siteCount payload
  ordinary reset branch positive room shorten w fit board op drift degree degreeMax lo header initial K headRate
  grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher
  signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes ticket before after located
  cells observed old accepted B number places shape labels pointer flags stored roles positiveRoles tags

noncomputable def profiled_field_returns := (fieldExit).1

open scoped OAI.Hierarchy

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun other =>
    "profiled_header_return" :: "profiled_span_return" :: "profiled_slot_return" :: other

theorem profiled_header_return :
    type_of% (proofField% profiled_field_publications [PProd.fst, PProd.fst]) :=
  no_implicit_lambda% proofField% profiled_field_publications [PProd.fst, PProd.fst]

theorem profiled_span_return :
    type_of% (proofField% profiled_field_publications [PProd.fst, PProd.snd]) :=
  no_implicit_lambda% proofField% profiled_field_publications [PProd.fst, PProd.snd]

theorem profiled_slot_return :
    type_of% (proofField% profiled_field_publications [PProd.snd]) :=
  no_implicit_lambda% proofField% profiled_field_publications [PProd.snd]

end
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
