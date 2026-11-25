import OAI.Hierarchy.DescentProfiledOrdinarySpans
import OAI.Hierarchy.DescentProfiledOrdinaryHeaderSources

namespace OAI
/-! # All three range fields on the selected ordinary date, including partial packed pages -/
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

set_option maxHeartbeats 450000
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
open private chosenClaim witnessesAt from OAI.Hierarchy.DescentNamedArchivePrefix
attribute [local irreducible] Origin.source Origin.archivePackage issued
set_option hygiene false in
local notation "claim" vote:arg => chosenClaim X G S ordinary reset branch positive room shorten w (walk₀ vote)
set_option hygiene false in
local notation "stride₁" => max 1 (max reset.bitsR (C*reset.bitsR))
set_option hygiene false in
local notation "fullBranch" vote:arg => trace (walk₀ vote)
set_option hygiene false in
local notation "pinDiv" => dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
set_option hygiene false in
local notation "pinFactors" => (fun _ : pins=>dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b) 1)
set_option hygiene false in
local notation "R₁" => stride₁
set_option hygiene false in
local notation "one₁" => le_max_left 1 (max reset.bitsR (C*reset.bitsR))
set_option hygiene false in
local notation "pinWidth" => pinDiv
set_option hygiene false in
local notation "org" vote:arg => (trace (walk₀ vote)).origin
section

open private originalArchiveFields from OAI.Hierarchy.DescentProfiledOrdinarySpans
open private register_cap_calendar from OAI.Hierarchy.DescentNamedPrefixState
open private traceAt_kinds from OAI.Hierarchy.DescentNamedBranchMachine
set_option cleanup.letToHave false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

open Lean Elab Term in
local elab "paidArchiveWriter% " body:term : term => elabTerm body none

set_option hygiene false in
local notation "paidSpanRegisters" => profiled_ordinary_registers X G t rate τ β siteCount payload ordinary reset branch
  positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver
  growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader
  oldHeader votes m oldVotes observed seedRoles limit ticket before after located cells old accepted previous tags
set_option hygiene false in
local notation "archiveSpansProof" extent:arg => paidArchiveWriter%
  let suffix := (Path.here.ordinary ticket).append after
  let together : before.append suffix=(traces (walk₀ votes)).path:=
    (Path.append_cut_assoc before (Path.here.ordinary ticket) after).symm.trans located
  let t₀ := traces (walk₀ votes)
  let witnesses : witnessesAt t₀ p R₁ op :=
    prefix_archive_witnesses X G S ordinary reset branch positive room shorten (walk₀ votes)
  let structural := witnesses (before.ordinary ticket) after located
  let prev := originalArchiveFields X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit
    drift degree lo header initial votes m before previous structural.1 structural.2.1.1 structural.2.2
  let pl₀:=prev.choose
  let read:=prev.choose_spec
  let history₀:=before.archive p positive (org votes).archive structural.1
  let ord₀:=trajectory p positive (org votes).archive (Origin.archiveOrder (org votes)) before structural.1
  let shape₀:=archiveShape positive one₁ pinFactors (org votes).archive
    (Origin.archiveShape (org votes) p R₁ positive one₁ pinWidth) before structural.1 structural.2.1.1
  let labels₀ := (encodePath op reset.menu before positive structural.1 structural.2.2 (org votes).archive
    (Palette.encodedOrigin (p:=p) (org votes) op reset.menu)).atNode
  let pointer₀ := Reached.argumentPointer prior history₀.bit ord₀ shape₀ positive
    (fun y : pins => y.1.val) (cursor i).ports.argumentsPerNode
  let flags₀ := archiveFlag prior history₀.bit ord₀ (cursor i).ports pl₀
  let evt:RunTrace.Events traces i:=⟨walk₀ votes,.ordinary before ticket after located⟩
  let placed (j:ℕ) (e:RunTrace.Events traces j) : RegisterTimeline.fitsAt (w:=w) traces menu initial j e :=
    (profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
      input coeff original pre positiveK headerFits machine j e).1
  let cv:=profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine i evt
  let lanes:=((cv.2 cells).1).1
  let ample:=OrdinaryBooks.PrimitiveCalendar.role_unit G op t f g rate τ β drift degreeMax driftR
    payload siteCount p palette initial.ports (DatePorts.ArchiveWidths.node_bound G S op pre.room.archive) input original
  let allMoves:=all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl
  let role:=RegisterTimeline.bought_role_registers traces menu initial (fun clock ev₁ ev₂ mv₁ mv₂=>allMoves clock (cursor clock) ev₁ ev₂ mv₁ mv₂)
    placed (register_cap_calendar X G S ordinary reset branch positive room shorten menu rfl)
    (traceAt_kinds X G S ordinary reset branch positive room shorten) pre (walk₀ votes) seedRoles ample before suffix together
  let actual:=Branch.header_archive_places X G S (trace (walk₀ votes)) ticket before after located op frozen
    drift degree payload ((menu).seats i) (cursor i).floor (cursor i).ports (menu).ordinary positive reset.height structural.1 lanes
  let tables:=profiled_ordinary_argument_tables X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver
    growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets
    nonempty split beforeHeader oldHeader votes m oldVotes ticket before after located cells observed old accepted
    history₀.bit ord₀ pl₀ shape₀ labels₀ pointer₀ flags₀ read role.1 role.2 tags
  let writeSpans := profiled_span_return X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver
    growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets
    nonempty split beforeHeader oldHeader votes m oldVotes ticket before after located cells observed old accepted
    history₀.bit ord₀ pl₀ shape₀ labels₀ pointer₀ flags₀ read role.1 role.2 tags
  let path₁ := before.ordinary ticket
  let written : BitDescription n.result := (path₁.archive p positive (org votes).archive structural.1).bit
  let numbered : Local written := trajectory p positive (org votes).archive (Origin.archiveOrder (org votes)) path₁ structural.1
  let represented : WorldShape p R₁ written := DescentBundleHistory.archiveShape positive one₁ pinFactors
    (org votes).archive (Origin.archiveShape (org votes) p R₁ positive one₁ pinWidth) path₁ structural.1 structural.2.1
  let nextPorts:=tables.2.2.1.2.1
  let saved:DatePorts.RangeRoom (cursor (i+1)).ports next written:=nextPorts.symm ▸ actual
  let registers := paidSpanRegisters extent
  writeSpans written numbered saved represented positive registers.2.1 registers.1.2

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env ("profiled_ordinary_archive_spans" :: ·)

/-- Every live original interval and every count field past its arity are read on the returned memory. -/
theorem profiled_ordinary_archive_spans
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
    (originSize : Fintype.card (trace (walk₀ votes)).origin.source.V≤ initial.ports.operandHosts) :
    type_of% (archiveSpansProof originSize) :=
  no_implicit_lambda% (archiveSpansProof originSize)

end
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
