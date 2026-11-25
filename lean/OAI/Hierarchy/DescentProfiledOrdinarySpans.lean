import OAI.Hierarchy.ProofField
import OAI.Hierarchy.DescentCutStoredPointerSites
import OAI.Hierarchy.DescentRegisteredOriginalGrain
import OAI.Hierarchy.DescentProfiledOrdinaryHeaderSources
import OAI.Hierarchy.DescentCutAcquiredSources
import OAI.Hierarchy.DescentPrefixPostedSlots
import OAI.Hierarchy.DescentProfiledOrdinaryPopulation

namespace OAI
/-! # The three range digits returned by the selected ordinary argument writer -/

namespace Hierarchy.DescentSixParty.SeedNamed

private def packSpan {Guard Len Header MetaRows Physical Returned Pointer : Prop}
    (raw : Guard ∧ Len) (metadataOfLength : Len → Header ∧ MetaRows)
    (slot : Header → Physical → Returned) (allFields : Physical) (pointers : Pointer) :
    PProd (PProd (PProd (Guard ∧ Len) Returned) (Header ∧ MetaRows)) Pointer :=
  let measured := metadataOfLength raw.2
  ⟨⟨⟨raw, slot measured.1 allFields⟩, measured⟩, pointers⟩

private theorem spanReturnComponentsMarker {Guard Len Header MetaRows Physical Returned Pointer : Prop}
    (_ : Guard ∧ Len) (_ : Len → Header ∧ MetaRows)
    (_ : Header → Physical → Returned) (_ : Physical) (_ : Pointer) : True := True.intro

open Lean Meta Elab Term Command

private partial def restoreHistoricalSpanProduct (e : Lean.Expr) : MetaM Lean.Expr := do
  let term := e.consumeMData
  if term.isAppOf ``spanReturnComponentsMarker then
    let parts := term.getAppArgs
    unless parts.size == 12 do throwError m!"Unexpected publication marker arity {parts.size}"
    return mkAppN (mkConst ``packSpan) parts
  if term.isApp && term.getAppFn.isLambda then
    return ← restoreHistoricalSpanProduct term.headBeta
  match term with
  | .lam n ty body bi =>
    withLocalDecl n bi ty fun x => do
      mkLambdaFVars #[x] (← restoreHistoricalSpanProduct (body.instantiate1 x))
  | .letE n ty rhs body _ =>
    withLetDecl n ty rhs fun x => do
      mkLetFVars #[x] (← restoreHistoricalSpanProduct (body.instantiate1 x)) (generalizeNondepLet := false)
  | _ => throwError m!"Expected the four physical span components, found {term.getAppFn.constName?}"

private def historicalSpanInputs (type : Lean.Expr) :
    MetaM (Lean.Expr × Array BinderInfo × Array String) :=
  forallTelescope type fun xs _ => do
    let domains ← mkForallFVars xs (mkConst ``True)
    let binders ← xs.mapM fun x => do return (← x.fvarId!.getDecl).binderInfo
    let explicitNames ← xs.filterMapM fun x => do
      let decl ← x.fvarId!.getDecl
      return if decl.binderInfo.isExplicit then some decl.userName.toString else none
    return (domains, binders, explicitNames)

/-- Close the actual paid lambda and publish its checked four-field product. -/
private def declareHistoricalSpanProduct (destination : Name) (context : Array Lean.Expr)
    (body : Syntax) : TermElabM Unit := do
  let checked ← withoutErrToSorry <| elabTerm body none
  synthesizeSyntheticMVarsNoPostponing
  let closed ← mkLambdaFVars context (← instantiateMVars checked) (usedOnly := true)
  let template ← Term.levelMVarToParam closed
  let templateType ← instantiateMVars (← inferType template)
  let result ← instantiateMVars (← restoreHistoricalSpanProduct template)
  let statement ← instantiateMVars (← inferType result)
  if result.hasSorry || statement.hasSorry || result.hasMVar || statement.hasMVar then
    throwError "An input or the resulting publication contains an unresolved proof"
  if result.hasFVar || result.hasLooseBVars || statement.hasFVar || statement.hasLooseBVars then
    throwError "The resulting publication did not close its original arguments"
  for term in #[result, statement] do
    let constants := term.getUsedConstants
    if constants.contains ``spanReturnComponentsMarker then
      throwError "The resulting span publication still contains the construction marker"
  let (originalInputs, originalBinders, originalNames) ← historicalSpanInputs templateType
  let (inputs, binders, names) ← historicalSpanInputs statement
  let expected := "X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes observed seedRoles limit ticket before after located cells old accepted previous tags originSize".splitOn " "
  unless originalNames.size == 62 && originalNames.toList == expected && names == originalNames do
    throwError m!"The original 62 paid inputs were not preserved: {names}"
  unless originalBinders.size == 88 && binders == originalBinders do
    throwError m!"The original 88 binder positions or kinds changed ({binders.size})"
  unless ← isDefEq inputs originalInputs do throwError "The original input types changed"
  addDecl <| .defnDecl {
    name := destination
    levelParams := (collectLevelParams (collectLevelParams {} statement) result).params.toList
    type := statement
    value := result
    hints := .regular (getMaxHeight (← getEnv) result + 1)
    safety := .safe }
  modifyEnv (addNoncomputable · destination)

end Hierarchy.DescentSixParty.SeedNamed

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
include previous in
private theorem originalArchiveFields
    (whole : before.whole p) (algn : before.aligned p R₁) (rot : before.OnlyRotor op) :
    readFields (selectedRead before (cursor i) (DateCode.history cpu m i) whole algn rot) :=
  (selectedRead before (cursor i) (DateCode.history cpu m i) whole algn rot).mp previous

open DescentRetainedRangeDigits
open private register_cap_calendar from OAI.Hierarchy.DescentNamedPrefixState
open private traceAt_kinds from OAI.Hierarchy.DescentNamedBranchMachine
include cells limit in
private theorem selectedPriorSlots (whole : before.whole p) (aligned : before.aligned p R₁) :
    let archived := before.archive p positive (org votes).archive whole
    let represented := DescentBundleHistory.archiveShape positive one₁ pinFactors (org votes).archive
      (Origin.archiveShape (org votes) p R₁ positive one₁ pinWidth) before whole aligned
    (∀y : NodeOrder.All archived.bit,
      (occurrences (represented.sites y.1) y.2).length ≤ (cursor i).ports.argumentsPerNode) ∧
    (∀v : W.graph.Site, ∀u : (archived.bit.recipe v).Node,
      ((represented.sites v).recipe positive).arity u ≤ (cursor i).ports.argumentsPerNode) ∧
    (cursor i).ports.argumentsPerNode ≤ (S).retainedArgumentsAt G drift := by
  intro archived represented
  have posted : (cursor i).ports.argumentsPerNode = (if i=0 then 3*(s/p) else (S).retainedArgumentsAt G drift) := cells.arguments
  have slots₀ (y : NodeOrder.All archived.bit) :
      (occurrences (represented.sites y.1) y.2).length ≤ (cursor i).ports.argumentsPerNode := by
    exact (Branch.prefix_posted_slots X G S (trace (walk₀ votes)) positive before whole aligned
      one₁ pinWidth drift limit reset.height branch y).trans posted.ge
  refine ⟨slots₀,?_,?_⟩
  · intro v u
    exact (DescentRetainedRangeDigits.length (represented.sites v) u positive).ge.trans (slots₀ ⟨v,u⟩)
  · apply posted.le.trans
    split
    · exact (S).seed_argument_capacity G p drift reset.height branch
    · exact le_rfl

private theorem seventhNeeded {α : Type*} (owner : Option α) (arity : α→ℕ) (j:ℕ) :
    owner.elim True (fun y=>j<arity y ∨ (2:Fin 3)=2) := by
  cases owner <;> simp

open DescentRetainedRangeDigits

set_option cleanup.letToHave false

open Lean Elab Command in
local elab "defineHistoricalSpanProduct " body:term : command => do
  let destination := (← getCurrNamespace) ++ `profiled_ordinary_source_registers
  runTermElabM fun context => declareHistoricalSpanProduct destination context body

/-
The ordinary instruction reads offset, start and length on each occupied argument,
and reads length on every argument slot, including all padded nodes.
-/
set_option maxRecDepth 18000 in
set_option maxHeartbeats 6000000 in
defineHistoricalSpanProduct (fun
    (originSize : Fintype.card (trace (walk₀ votes)).origin.source.V≤ initial.ports.operandHosts) =>
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
  let evidence:=profiled_ordinary_argument_evidence X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver
    growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets
    nonempty split beforeHeader oldHeader votes m oldVotes ticket before after located cells observed old accepted
    history₀.bit ord₀ pl₀ shape₀ labels₀ pointer₀ flags₀ read role.1 role.2 tags
  let pose:=profiled_ordinary_argument_pose X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver
    growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets
    nonempty split beforeHeader oldHeader votes m oldVotes ticket before after located cells observed old accepted
    history₀.bit ord₀ pl₀ shape₀ labels₀ pointer₀ flags₀ read role.1 role.2 tags
  let actual:=Branch.header_archive_places X G S (trace (walk₀ votes)) ticket before after located op frozen
    drift degree payload ((menu).seats i) (cursor i).floor (cursor i).ports (menu).ordinary positive reset.height structural.1 lanes
  let population:=profiled_prefix_population X G S ordinary reset branch positive room shorten
    w fit frozen drift degree payload lo header initial pre placed (walk₀ votes) originSize before suffix together
  let priorSlots := selectedPriorSlots (X:=X) (G:=G) (t:=t) (rate:=rate) (τ:=τ) (β:=β)
    (siteCount:=siteCount) (payload:=payload) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
    (positive:=positive) (room:=room) (shorten:=shorten) (w:=w) (fit:=fit) (drift:=drift)
    (degree:=degree) (lo:=lo) (header:=header) (initial:=initial) (votes:=votes) (before:=before)
    (cells:=cells) (limit:=limit) structural.1 structural.2.1.1
  let slots₀ := priorSlots.1
  let recordWidth := (OrdinaryBooks.record_width G S op g k i p frozen drift degree payload ((menu).seats i) (cursor i).ports).1
  let fieldLower : 2 ≤ DescentOperandWidth.recordBits G S k frozen drift degree p :=
    (Nat.le_max_left 2 _).trans (Nat.le_max_left _ _)
  let fieldWide : 2 ≤ (cursor i).ports.operandBits := cells.room.archive.digits.symm ▸ fieldLower
  let field := recordWidth.trans cells.room.archive.digits.symm
  let word : payload≤w := (Nat.le_mul_of_pos_left _ (by omega : 0<t+1+max K headRate+2)).trans machine
  let packed := cells.room.archive.operands.trans ((Nat.div_le_self ..).trans word)
  let live:i<(S).length:=ticket.hubRows.choose
  let paid := priorSlots.2.1
  let previousArgs := priorSlots.2.2
  let capPositive : 0<(S).capGain:=by
    change 0<capRate G t g
    unfold capRate
    omega
  let unitRead:=ordinary_original_grain X G S ordinary reset branch positive room shorten
    (walk₀ votes) ticket before after located (cursor i).ports op frozen drift degree payload
    ((menu).seats i) (cursor i).floor (menu).ordinary
  let pointers:=fun (walks:DescentHaloWalkRAM.breadth (maximumDegree ((S).rounds+1))≤2^k)=>
    Branch.cut_argument_pointer_sites (X:=X) (G:=G) («S»:=S) (br:=trace (walk₀ votes))
      (ticket:=ticket) (before:=before) (tail:=after) (cut:=located)
      («ports»:=(cursor i).ports) («op»:=op) («tailBits»:=frozen) (drift:=drift) (degree:=degree) (payload:=payload)
      (seats:=(menu).seats i) (root:=(cursor i).floor) («ordinary»:=(menu).ordinary) (stores:=evidence.1.1)
      (canon:=pose) (arch:=history₀) (places:=pl₀) (enough:=population)
      (width:=field) (hp:=positive) (one:=one₁) (pin:=pinFactors) (shape:=shape₀)
      (step:=structural.2.1.2) (number:=ord₀) (pinCode:=fun y:pins=>y.1.val)
      (labels:=labels₀) (flags:=flags₀) (earlier:=evidence.2.1) (paid:=paid) (packed:=packed) (arityFit:=paid)
      (issued:=evidence.2.2) (cutRead:=unitRead) capPositive previousArgs walks
  let allFields:=Branch.cut_span_values (X:=X) (G:=G) («S»:=S) (br:=trace (walk₀ votes))
    (ticket:=ticket) (before:=before) (tail:=after) (cut:=located) (stores:=evidence.1.1)
    (enough:=population) (history:=history₀) (localOrder:=ord₀) (placed:=pl₀) (previous:=shape₀)
    (hp:=positive) (one:=one₁) (pinsFit:=pinFactors) (unit:=structural.2.1.2)
    (age:=live) (pose:=pose) (width:=field) (precision:=fieldWide) (packed:=packed) (newRoom:=actual)
    (labels:=labels₀) (seen:=evidence.2.1) (slots:=slots₀) (registered:=evidence.2.2)
  let seventh := fun blockIdx nodeIdx operandIdx hostIdx groupIdx =>
    allFields blockIdx nodeIdx hostIdx groupIdx operandIdx (2 : Fin 3) (seventhNeeded _ _ _)
  let raw := And.intro
    (fun blockIdx nodeIdx operandIdx hostIdx groupIdx rangeField =>
      allFields blockIdx nodeIdx hostIdx groupIdx operandIdx rangeField)
    seventh
  let tables:=profiled_ordinary_argument_tables X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver
    growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets
    nonempty split beforeHeader oldHeader votes m oldVotes ticket before after located cells observed old accepted
    history₀.bit ord₀ pl₀ shape₀ labels₀ pointer₀ flags₀ read role.1 role.2 tags
  let post:=profiled_slot_return X G t rate τ β siteCount payload ordinary reset branch positive room shorten
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
  let bounds:=(cv.2 cells).1
  let code:=Branch.registered_geometry_fits X G S (trace (walk₀ votes)) ticket before after located op frozen drift
    degree payload (cursor i).floor (cursor i).ports (menu).ordinary board (menu).seats (menu).profile header w live word
    cells cells.degree ⟨rfl,rfl⟩ bounds.1 bounds.2
  let calibrated:=profiled_calibrated_execution X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader
    oldHeader i evt cells
  let cap (y:NodeOrder.All written) : (DescentRetainedRangeDigits.occurrences (represented.sites y.1) y.2).length≤
      (S).retainedArgumentsAt G drift :=
    (Branch.prefix_argument_capacity X G S (trace (walk₀ votes)) positive path₁ structural.1 reset.height branch
      represented y.1 y.2).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right limit 1))
  let metadataForLength:=profiled_header_node_rows_from_f6 X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver
    growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets
    nonempty split beforeHeader oldHeader votes m oldVotes ticket before after located cells observed old accepted
    history₀.bit ord₀ pl₀ shape₀ labels₀ pointer₀ flags₀ read role.1 role.2 tags
    code (calibrated code) written numbered actual represented cap
  let returnedForSource := post written numbered saved represented positive
  spanReturnComponentsMarker raw metadataForLength returnedForSource allFields pointers)

open scoped OAI.Hierarchy

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun other =>
    "profiled_ordinary_pointer_sources" :: "profiled_ordinary_spans" ::
      "profiled_ordinary_range_values" :: "profiled_header_node_rows" :: other

set_option hygiene false in
local notation "sourceRegisters" extent:arg => profiled_ordinary_source_registers X G t rate τ β siteCount payload
  ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial K headRate grant
  purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette
  bin sockets nonempty split beforeHeader oldHeader votes m oldVotes observed seedRoles limit ticket before after
  located cells old accepted previous tags extent

noncomputable def profiled_ordinary_registers
    (originSize : Fintype.card (trace (walk₀ votes)).origin.source.V≤ initial.ports.operandHosts) :=
  (sourceRegisters originSize).1

/-- The normalized words in the actual ordinary instruction and the argument-pointer
semantics of those same resolver jobs on the selected successor archive. -/
theorem profiled_ordinary_pointer_sources :
    type_of% (proofField% profiled_ordinary_source_registers [PProd.snd]) :=
  no_implicit_lambda% proofField% profiled_ordinary_source_registers [PProd.snd]

set_option hygiene false in
local notation "reachedRanges" extent:arg => profiled_ordinary_registers X G t rate τ β siteCount payload
  ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial K headRate grant
  purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette
  bin sockets nonempty split beforeHeader oldHeader votes m oldVotes observed seedRoles limit ticket before after
  located cells old accepted previous tags extent

noncomputable def profiled_ordinary_range_publication
    (originSize : Fintype.card (trace (walk₀ votes)).origin.source.V≤ initial.ports.operandHosts) :=
  (reachedRanges originSize).1

theorem profiled_ordinary_spans :
    type_of% (proofField% profiled_ordinary_registers [PProd.fst, PProd.fst]) :=
  no_implicit_lambda% proofField% profiled_ordinary_registers [PProd.fst, PProd.fst]

/-- The three interval fields persist on the archive of the accepted successor date. -/
theorem profiled_ordinary_range_values :
    type_of% (proofField% profiled_ordinary_registers [PProd.fst, PProd.snd]) :=
  no_implicit_lambda% proofField% profiled_ordinary_registers [PProd.fst, PProd.snd]

/-- The selected span read also gives the earlier arity header and the two final metadata pages. -/
theorem profiled_header_node_rows :
    type_of% (proofField% profiled_ordinary_registers [PProd.snd]) :=
  no_implicit_lambda% proofField% profiled_ordinary_registers [PProd.snd]

end
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
