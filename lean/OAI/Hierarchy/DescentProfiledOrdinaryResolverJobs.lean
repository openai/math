import OAI.Hierarchy.DescentProfiledOrdinaryPointerSites
import OAI.Hierarchy.DescentRegisteredPointerWordIdentity
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
variable (ordinary : OrdinaryRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) cut) (reset : ResetRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) (atRound (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds) n h C f g cut (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))
variable (branch : G.b ≤ 2^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).initialSites)
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
set_option hygiene false in
local notation "board" => reset.board
set_option hygiene false in
local notation "op" => RotorSpec.ofRates reset
variable
    (drift degree degreeMax lo header : ℕ) (initial : RegisterTimeline.Position)
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
variable {driftR ratio : ℕ}
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
private theorem selectedFieldReturn (votes : (ch).Pin → Bool) :
    fieldReturnOnPath (w:=w) (fullBranch votes).origin.source (fullBranch votes).target (fullBranch votes).path
      positive (le_max_left 1 _) pinFactors op reset.menu (fullBranch votes).origin.archive
      (Origin.archiveOrder (fullBranch votes).origin)
      (Origin.archiveShape (fullBranch votes).origin p stride₁ positive (le_max_left 1 _) pinDiv)
      (Palette.encodedOrigin (p:=p) (fullBranch votes).origin op reset.menu)
      (fun y:pins=>y.1.val) (claim votes) := by
  exact fieldReturnOnBranch X G S (r:=(cert).choose) (c:=walk₀ votes) (trace (walk₀ votes))
    positive (le_max_left 1 _) op reset.menu w
set_option hygiene false in
local notation "R₁" => stride₁
set_option hygiene false in
local notation "one₁" => le_max_left 1 (max reset.bitsR (C*reset.bitsR))
set_option hygiene false in
local notation "pinWidth" => pinDiv
set_option hygiene false in
local notation "org" vote:arg => (trace (walk₀ vote)).origin
section
variable (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤ payload) (coeff : degree≤ degreeMax) (original : (S).firstWidth G.b p≤ payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0< k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤ w)
    (matcher:MatcherRoom G S k p payload)
    (signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤ payload)
    (palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (nonempty:0< sockets)
    (split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (beforeHeader:lo+extent storage (ch).layout≤ header) (oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (oldVotes:∀a∈shelves storage lo 0 (ch).layout,∀j:Fin (slots a.src.seats storage),
      m (a.base+j.val)=((packed a.src.pin votes storage j.val).val:Computability.VPVNP.BurstRAM.Word w))
    (observed:ObservationRoom G S payload w)
    (seedRoles:initial.ports.RoleRows ∧ 0< initial.ports.roleLanes) (limit:R₁≤drift)
    {W:MarkedWorld F 0 pins widths} {i z D z' D':ℕ} {q:ℝ} {nonneg:0≤fee}
    {prior:Reached W G price fee S k i z D ((S).epochPower^(S).priceExponent) s}
    {T:StageInput W G q fee} {choice:(T.result nonneg).Choice} {n:Normalize ((T.result nonneg).state choice)}
    {next:Reached n.result G price fee S k (i+1) z' D' ((S).epochPower^(S).priceExponent) s}
    (ticket:OrdinaryLink prior nonneg T choice n next)
    (before:Path (traces (walk₀ votes)).first prior) (after:Path next (traces (walk₀ votes)).last)
    (located:(before.ordinary ticket).append after=(traces (walk₀ votes)).path)
    (cells:geom i)
    (old:(cursor i).ports.held prior (cursor i).floor (DateCode.history cpu m i))
    (accepted:before.selections.length+1<((ch).rows votes).length ∨ (ch).read votes=some (walk₀ votes))
    (previous:(claim votes) before (cursor i) (DateCode.history cpu m i))
    (tags:(cursor i).ports.ArchiveTags (DateCode.history cpu m i))

private abbrev readFields {lhs rhs : Prop} (_ : lhs ↔ rhs) : Prop := rhs
set_option hygiene false in
local notation "selectedRead" => selectedFieldReturn X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit votes

open private register_cap_calendar from OAI.Hierarchy.DescentNamedPrefixState
open private traceAt_kinds from OAI.Hierarchy.DescentNamedBranchMachine
variable (originSize:Fintype.card (trace (walk₀ votes)).origin.source.V≤ initial.ports.operandHosts)

set_option hygiene false in
local notation "emitSites" => profiled_ordinary_header_from_sites X G t rate τ β siteCount payload ordinary reset branch
  positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver
  growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader
  oldHeader votes m oldVotes observed seedRoles limit ticket before after located cells old accepted previous tags originSize

set_option cleanup.letToHave false
private theorem selectedResolverWitness {P : Prop} (_ : P) : True := True.intro

open Lean Meta Elab Term Command

private partial def closeSelectedResolverWitness (input : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let term := input.consumeMData
  if term.isAppOfArity ``selectedResolverWitness 2 then
    let args := term.getAppArgs
    return (args[1]!, args[0]!)
  if term.isApp && term.getAppFn.isLambda then
    return ← closeSelectedResolverWitness term.headBeta
  match term with
  | .lam n domain body info =>
    let (value, type) ← closeSelectedResolverWitness body
    return (.lam n domain value info, .forallE n domain type info)
  | .letE n domain rhs body nondep =>
    let (value, type) ← closeSelectedResolverWitness body
    let retain (e : Lean.Expr) := if e.hasLooseBVar 0 then .letE n domain rhs e nondep else e.lowerLooseBVars 1 1
    return (retain value, retain type)
  | _ => throwError "Expected the registered word implication at the leaf of the actual paid context"

private def declareSelectedResolverWitness (name : Name) (context : Array Lean.Expr)
    (body : Syntax) : TermElabM Unit := do
  let checked ← withoutErrToSorry <| elabTerm body none
  synthesizeSyntheticMVarsNoPostponing
  let closed ← mkLambdaFVars context (← instantiateMVars checked) (usedOnly := true)
  let template ← Term.levelMVarToParam (← instantiateMVars closed)
  let (proof, type) ← closeSelectedResolverWitness template
  for e in #[proof, type] do
    if e.hasSorry || e.hasMVar || e.hasFVar || e.hasLooseBVars || e.getUsedConstants.contains ``selectedResolverWitness then
      throwError "A physical input or witness was not closed"
  addDecl <| .defnDecl {
    name := name
    levelParams := (collectLevelParams (collectLevelParams {} type) proof).params.toList
    type := type
    value := proof
    hints := .regular (getMaxHeight (← getEnv) proof + 1)
    safety := .safe }
  modifyEnv (addNoncomputable · name)

local elab "defineSelectedResolverWitness " body:term : command => do
  let name := (← getCurrNamespace) ++ `profiled_ordinary_header_from_jobs
  runTermElabM fun context => declareSelectedResolverWitness name context body

set_option maxRecDepth 18000 in
set_option maxHeartbeats 6000000 in
defineSelectedResolverWitness (
  let wholeTrace := traces (walk₀ votes)
  have witnesses : witnessesAt wholeTrace p R₁ op :=
    prefix_archive_witnesses X G S ordinary reset branch positive room shorten (walk₀ votes)
  have structural := witnesses (before.ordinary ticket) after located
  have prev := (selectedRead before (cursor i) (DateCode.history cpu m i) structural.1 structural.2.1.1 structural.2.2).mp previous
  let pl₀:=prev.choose
  have read:=prev.choose_spec
  let evt:RunTrace.Events traces i:=⟨walk₀ votes,.ordinary before ticket after located⟩
  have cv:=profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine i evt
  have lanes:=((cv.2 cells).1).1
  have role : (cursor i).ports.RoleRows ∧ 0<(cursor i).ports.roleLanes := by
    let suffix := (Path.here.ordinary ticket).append after
    have together : before.append suffix=(traces (walk₀ votes)).path :=
      (Path.append_cut_assoc before (Path.here.ordinary ticket) after).symm.trans located
    have placed (j:ℕ) (e:RunTrace.Events traces j) : RegisterTimeline.fitsAt (w:=w) traces menu initial j e :=
      (profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
        w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
        input coeff original pre positiveK headerFits machine j e).1
    have ample := OrdinaryBooks.PrimitiveCalendar.role_unit G op t f g rate τ β drift degreeMax driftR
      payload siteCount p palette initial.ports (DatePorts.ArchiveWidths.node_bound G S op pre.room.archive) input original
    let fixed := all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl
    exact RegisterTimeline.bought_role_registers traces menu initial (fun j a b x y=>fixed j (cursor j) a b x y)
      placed (register_cap_calendar X G S ordinary reset branch positive room shorten menu rfl)
      (traceAt_kinds X G S ordinary reset branch positive room shorten) pre (walk₀ votes) seedRoles ample before suffix together
  let tables:=profiled_ordinary_argument_tables X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver
    growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets
    nonempty split beforeHeader oldHeader votes m oldVotes ticket before after located cells observed old accepted
    _ _ pl₀ _ _ _ _ read role.1 role.2 tags
  let v := DatePorts.ordinaryModel (cursor i).ports ticket op g frozen p f drift degree payload ((menu).seats i) (cursor i).floor (menu).ordinary
  let path₁ := before.ordinary ticket
  let written : BitDescription n.result := (path₁.archive p positive (org votes).archive structural.1).bit
  let numbered : Local written := trajectory p positive (org votes).archive (Origin.archiveOrder (org votes)) path₁ structural.1
  let represented : WorldShape p R₁ written := DescentBundleHistory.archiveShape positive one₁ pinFactors
    (org votes).archive (Origin.archiveShape (org votes) p R₁ positive one₁ pinWidth) path₁ structural.1 structural.2.1
  have widthPrice:=Branch.registered_geometry_fits X G S (trace (walk₀ votes)) ticket before after located op frozen drift
    degree payload (cursor i).floor (cursor i).ports (menu).ordinary board (menu).seats (menu).profile header w
    ticket.hubRows.choose (by exact (Nat.le_mul_of_pos_left _ (by omega:0<t+1+max K headRate+2)).trans machine)
    cells cells.degree ⟨rfl,rfl⟩ ((cv.2 cells).1).1 ((cv.2 cells).1).2
  selectedResolverWitness (Reached.PointerSites.from_signed_words next v written numbered represented positive (fun y : pins => y.1.val)
    _ emitSites tables.2.2.2.1 widthPrice.packed lanes tables.2.1))

end
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
