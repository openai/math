import OAI.Hierarchy.DescentProfiledOrdinarySpans
import OAI.Hierarchy.DescentProfiledOrdinaryHeaderSources
import OAI.Hierarchy.DescentProfiledHeaderNodeRows
import OAI.Hierarchy.DescentProfiledOriginalCourse
import OAI.Hierarchy.DescentProfiledOrdinaryArgumentTables
import OAI.Hierarchy.DescentProfiledResetTagSource
import OAI.Hierarchy.DescentOriginalTaggedArchivePrefix
import OAI.Hierarchy.DescentBoughtRoleRegister
import OAI.Hierarchy.DescentProfiledHeaderSources
import OAI.Hierarchy.DescentRegisteredHeaderPlaces

namespace OAI
/-! # The padded archive tags acquired from the actual ordinary and reset shelves on an earned cut -/

namespace Hierarchy.DescentSixParty.SeedNamed

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env ("profiled_ordinary_header_from_sites" :: ·)
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Fin.CommRing
noncomputable section
open ProtocolRAM DescentOperandStateBanks DescentPrimitivePalette DescentLocalArchiveOrder DescentBundleHistory DescentKernelHistory
set_option hygiene false in
local notation "J₀" => Nat.log 2 payload/(2*β)
set_option quotPrecheck false
set_option hygiene false in
local notation "frozen" => DescentCompiler.TerminalScale.tail τ J₀
set_option hygiene false in
local notation "S" => stageNumbers G t J₀ f g rate siteCount frozen
set_option hygiene false in
local notation "k" => groupBits t J₀ (hostRate t rate) (capRate G t g) (cutRate t f g)
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
set_option hygiene false in
local notation "board" => reset.board
set_option hygiene false in
local notation "op" => RotorSpec.ofRates reset
set_option hygiene false in
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
set_option hygiene false in
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial

set_option maxHeartbeats 6000000
set_option maxRecDepth 8000

set_option hygiene false in
local notation "geom" i:arg => Geometry G S menu k w i (cursor i)

set_option hygiene false in
local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g rate).choose
set_option hygiene false in
local notation "funds" => 44*argumentDigitRate G t f g rate driftR baseRate

open DescentPackedEpochShelves
set_option hygiene false in
local notation "storage" => DescentPackedEpochShelves.grain (payload/2) G.C
set_option hygiene false in
local notation "family" => fun j H=>SignedStage.atDate G S g k j H

open DescentPackedProfileTape DescentPackedProfileInstall
set_option hygiene false in
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial
set_option hygiene false in
local notation "walk₀" votes:arg => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes

open DescentLocalArchiveOrder DescentPrimitivePalette DescentKernelHistory DescentBundleHistory
open private chosenClaim from OAI.Hierarchy.DescentNamedArchivePrefix
attribute [local irreducible] Origin.source Origin.archivePackage issued
set_option hygiene false in
local notation "claim" vote:arg => chosenClaim X G S ordinary reset branch positive room shorten w (walk₀ vote)
set_option hygiene false in
local notation "stride₁" => max 1 (max reset.bitsR (C*reset.bitsR))
set_option hygiene false in
local notation "R₁" => stride₁
section

set_option hygiene false in
local notation "headerWriter" => profiled_ordinary_header_sources X G t rate τ β siteCount payload ordinary reset branch
  positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver
  growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader
  oldHeader votes m oldVotes observed seedRoles limit ticket before after located cells old accepted previous tags
set_option hygiene false in
local notation "measuredRows" => profiled_header_node_rows X G t rate τ β siteCount payload ordinary reset branch
  positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver
  growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader
  oldHeader votes m oldVotes observed seedRoles limit ticket before after located cells old accepted previous tags originSize

/-- All four final header fields at the next recorded archive are determined by the
actual pointer keys in the incoming normalized jobs on this ballot. -/
theorem profiled_ordinary_header_from_sites
    {F : Type}
    [Field F]
    {cp nP : ℕ}
    (X : Approximation F cp nP)
    (G : PoweredGadget F)
    {n h C f g p cut : ℕ}
    (t rate τ β siteCount payload : ℕ)
    (ordinary : OrdinaryRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) cut)
    (reset : ResetRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) (atRound (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds) n h C f g cut (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))
    (branch : G.b ≤ 2^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).capGain)
    (positive : 0 < p)
    (room : 10*(X.size+1) ≤ (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).initialSites)
    (shorten : reentryRate h C*(1-(2-G.rate)/4)^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds ≤ 1/2)
    (w : ℕ)
    (fit : (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).firstWidth G.b p < 2^w)
    (drift degree degreeMax lo header : ℕ)
    (initial : RegisterTimeline.Position)
    {driftR ratio : ℕ}
    (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR)
    (sites : siteCount≤(2^payload)^2)
    (input : p≤ payload)
    (coeff : degree≤ degreeMax)
    (original : (S).firstWidth G.b p≤ payload)
    (pre : Geometry G S menu k w 0 initial)
    (positiveK : 0< k)
    (headerFits : initial.floor≤2^(headRate*payload))
    (machine : (t+1+max K headRate+2)*payload≤ w)
    (matcher:MatcherRoom G S k p payload)
    (signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤ payload)
    (palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ)
    (nonempty:0< sockets)
    (split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (beforeHeader:lo+extent storage (ch).layout≤ header)
    (oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool)
    (m:Memory w)
    (oldVotes:∀a∈shelves storage lo 0 (ch).layout,∀j:Fin (slots a.src.seats storage),
      m (a.base+j.val)=((packed a.src.pin votes storage j.val).val:Computability.VPVNP.BurstRAM.Word w))
    (observed:ObservationRoom G S payload w)
    (seedRoles:initial.ports.RoleRows ∧ 0< initial.ports.roleLanes)
    (limit:R₁≤drift)
    {W:MarkedWorld F 0 pins widths}
    {i z D z' D':ℕ}
    {q:ℝ}
    {nonneg:0≤fee}
    {prior:Reached W G price fee S k i z D ((S).epochPower^(S).priceExponent) s}
    {T:StageInput W G q fee}
    {choice:(T.result nonneg).Choice}
    {n:Normalize ((T.result nonneg).state choice)}
    {next:Reached n.result G price fee S k (i+1) z' D' ((S).epochPower^(S).priceExponent) s}
    (ticket:OrdinaryLink prior nonneg T choice n next)
    (before:Path (traces (walk₀ votes)).first prior)
    (after:Path next (traces (walk₀ votes)).last)
    (located:(before.ordinary ticket).append after=(traces (walk₀ votes)).path)
    (cells:geom i)
    (old:(cursor i).ports.held prior (cursor i).floor (DateCode.history cpu m i))
    (accepted:before.selections.length+1<((ch).rows votes).length ∨ (ch).read votes=some (walk₀ votes))
    (previous:(claim votes) before (cursor i) (DateCode.history cpu m i))
    (tags:(cursor i).ports.ArchiveTags (DateCode.history cpu m i))
    (originSize:Fintype.card (trace (walk₀ votes)).origin.source.V≤ initial.ports.operandHosts) :
    type_of% ((headerWriter) (measuredRows).1) :=
  (headerWriter) (measuredRows).1

end
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
