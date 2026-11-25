import OAI.Hierarchy.DescentAcceptedOrdinaryTagSources
import OAI.Hierarchy.DescentRegisteredAcceptedArguments
import OAI.Hierarchy.DescentNamedProfiledOrdinaryAdvance
import OAI.Hierarchy.DescentProfiledOrdinaryArchiveEntry

namespace OAI
namespace Hierarchy.DescentSixParty.SeedNamed

universe u v

/-- The original date computation records the six values used by the publication theorem. -/
private def publicationComponentsMarker {Board : Sort u} {Fixed Seen : Prop}
    {Model : Sort v} {Tags Header : Prop} (_ : Board) (_ : Fixed) (_ : Seen)
    (_ : Model) (_ : Tags) (_ : Header) : Unit := ()

open Lean Meta Elab Term Command

private def joinPublicationParts (left right : Expr) : MetaM Expr := do
  let leftType ← inferType left
  let rightType ← inferType right
  return mkApp4 (.const ``PProd.mk [← getLevel leftType, ← getLevel rightType])
    leftType rightType left right

private def joinPublicationProofs (left right : Expr) : MetaM Expr := do
  return mkApp4 (mkConst ``And.intro) (← inferType left) (← inferType right) left right

/-- The argument model retains its own dependent operand reads and canonical pose. -/
private def assembleOriginalPublication (parts : Array Expr) : MetaM Expr := do
  let [board, fixed, seen, model, tags, header] := (parts.extract 6 12).toList
    | throwError "Expected the six components of the original dated publication"
  let evidence := Expr.proj ``PProd 0 model
  let pose := Expr.proj ``PProd 1 model
  let table := Expr.proj ``PProd 0 evidence
  let reads := Expr.proj ``PProd 1 table
  let returned ← joinPublicationProofs fixed (← joinPublicationProofs seen reads)
  let published ← joinPublicationParts (← joinPublicationParts board returned) tags
  let previous ← joinPublicationParts (← joinPublicationParts published evidence) pose
  joinPublicationParts previous header

/-- Rebuild the checked paid computation under exactly its original binders and local definitions. -/
private partial def restorePublicationResult (e : Expr) : MetaM Expr := do
  let term := e.consumeMData
  if term.isAppOf ``publicationComponentsMarker then
    let parts := term.getAppArgs
    unless parts.size == 12 do throwError m!"Unexpected publication marker arity {parts.size}"
    return ← assembleOriginalPublication parts
  match term with
  | .lam n ty body bi =>
    withLocalDecl n bi ty fun x => do
      mkLambdaFVars #[x] (← restorePublicationResult (body.instantiate1 x))
  | .letE n ty rhs body _ =>
    withLetDecl n ty rhs fun x => do
      mkLetFVars #[x] (← restorePublicationResult (body.instantiate1 x)) (generalizeNondepLet := false)
  | _ => throwError m!"Expected the six publication components, found {term.getAppFn.constName?}"

private def defineOriginalPublication (staged destination : Name) : TermElabM Unit := do
  let .defnInfo template ← getConstInfo staged | throwError m!"Expected a definition at {staged}"
  let result ← restorePublicationResult template.value
  let statement ← inferType result
  if result.hasSorry || statement.hasSorry || result.hasMVar || statement.hasMVar then
    throwError "An input or the resulting publication contains an unresolved proof"
  if result.hasFVar || result.hasLooseBVars || statement.hasFVar || statement.hasLooseBVars then
    throwError "The resulting publication did not close its original arguments"
  if result.getUsedConstants.contains ``publicationComponentsMarker || result.getUsedConstants.contains staged then
    throwError "The resulting proof still contains the construction marker"
  addDecl <| .defnDecl {
    name := destination
    levelParams := template.levelParams
    type := statement
    value := result
    hints := template.hints
    safety := .safe }

end Hierarchy.DescentSixParty.SeedNamed

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
private noncomputable def originalPublicationComponents (K headRate : ℕ)
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
    (tags:(register i).ArchiveTags (DateCode.history program m i)) : Unit :=
  let evt:RunTrace.Events traces i:=⟨walk₀ votes,.ordinary before ticket after located⟩
  let at_:=cursor i
  let v:=model i at_ ticket
  let dates:=profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine i evt
  let axis:=dates.2 cells
  let buy:0<v.resolver.lanes ∧ v.fullEnd at_.floor<2^w:=axis.1
  let extra:max (v.fullEnd at_.floor) (v.signedGuard (v.stageStart at_.floor))<2^w:=axis.2
  let word:payload≤w:=(Nat.le_mul_of_pos_left _ (by omega:0<t+1+max K headRate+2)).trans machine
  let live:i<(S).length:=ticket.hubRows.choose
  let code:=Branch.registered_geometry_fits X G S (trace (walk₀ votes)) ticket before after located op frozen drift
    degree payload at_.floor at_.ports (menu).ordinary board (menu).seats (menu).profile header w live word cells
    cells.degree ⟨rfl,rfl⟩ buy.1 buy.2
  let total:=profiled_calibrated_execution X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader
    oldHeader i evt cells
  let protected_:=profiled_calibrated_instruction X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader
  let resources:=Branch.registered_positive_venue_rooms X G S (trace (walk₀ votes)) ticket before after located
    op frozen drift degree payload at_.floor at_.ports (menu).ordinary board (menu).seats (menu).profile header
    w code cells ⟨rfl,rfl⟩ matcher word positiveK (signed i _ live.le) buy.1 ((le_max_right ..).trans_lt extra) buy.2
    purchase returns rfl rfl rfl growth coeff input original positive
  let layoutRoom:(menu).seats i*(G.C+8+8*G.k)<2^w:=by
    obtain ⟨shelf,_,hit,entry,_⟩:=registered_profile_exists X G S ordinary reset branch positive room shorten
      w fit payload lo (walk₀ votes) ticket before after located
    have atShelf:=RegisterTimeline.fromProfiles_at G S board op k frozen p f g drift degree payload lo header
      (ch).layout i shelf hit
    have seats:=(normalized_shelf_widths X G S ordinary reset branch positive room shorten w fit
      shelf.src (List.mem_of_getElem? entry)).2
    exact (Nat.mul_le_mul_right (G.C+8+8*G.k) (atShelf.2.1.le.trans seats)).trans_lt observed.score
  let floors:=((v.full_spent at_.floor).1).trans_lt buy.2
  let selected:=accepted_at_donor X G S ordinary reset branch positive room shorten w fit board op frozen drift
    degree payload lo header initial protected_ beforeHeader oldHeader votes m oldVotes ticket before after located accepted
    code (total code) cells old observed.height live floors (observed.key i live.le) (observed.count i live.le)
    observed.grain layoutRoom
  let actualBoard:=Classical.choice selected.choose_spec.choose_spec.2
  let books:=OrdinaryBooks.atDate G S op g k i p frozen drift degree payload ((menu).seats i) at_.ports
  let props:=Branch.issued_return_fields X G S (trace (walk₀ votes)) ticket before after located books frozen payload
    ((menu).seats i) at_.ports.venue.lanes at_.ports.io.roster (menu).ordinary
  let fixed:=(DatePorts.ordinary_registered_signed at_.ports ticket op g frozen p f drift degree payload
    ((menu).seats i) at_.floor (menu).ordinary props.2.2.2).1
  let common:=all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl i at_
  let native:=(atDate DatePorts.ordinaryDate i ticket) w ((menu).profile i) header positiveK code
  let result : RegisterTimeline.Position:=⟨atDate DatePorts.ordinaryPorts i ticket,v.fullEnd at_.floor⟩
  let mv : RegisterTimeline.Move w:=⟨native,result⟩
  let posted : RegisterTimeline.issued traces menu i evt at_ mv:=⟨positiveK,code,rfl⟩
  let seen:=RegisterTimeline.ordinary_posted_cut traces menu initial (walk₀ votes) m before ticket after located
    positiveK code (total code) (fun ev y hy=>common ev evt y mv hy posted)
  let source:=accepted_argument_model (X:=X) (G:=G) («S»:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (w:=w) (fit:=fit) (board:=board) (op:=op)
    («frozen»:=frozen) (drift:=drift) (degree:=degree) (payload:=payload) (lo:=lo) (header:=header) (initial:=initial)
    (protected_:=protected_) (beforeHeader:=beforeHeader) (lower:=oldHeader) (votes:=votes) (m:=m) (original:=oldVotes)
    (ticket:=ticket) (before:=before) (after:=after) (located:=located) (accepted:=accepted) (codeRoom:=code)
    (exec:=total code) (cells:=cells) (old:=old) (height:=observed.height) (age:=live) (floorFit:=floors)
    (keys:=observed.key i live.le) (counts:=observed.count i live.le) (grainRoom:=observed.grain) (layoutRoom:=layoutRoom)
    B number places shape labels pointer flags stored roles positiveRoles tags resources word
  let tagRows:=accepted_tag_sources (X:=X) (G:=G) («S»:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (w:=w) (fit:=fit) (board:=board) (op:=op)
    («frozen»:=frozen) (drift:=drift) (degree:=degree) (payload:=payload) (lo:=lo) (header:=header) (initial:=initial)
    (protected_:=protected_) (beforeHeader:=beforeHeader) (lower:=oldHeader) (votes:=votes) (m:=m) (original:=oldVotes)
    (ticket:=ticket) (before:=before) (after:=after) (located:=located) (accepted:=accepted) (codeRoom:=code)
    (exec:=total code) (cells:=cells) (old:=old) (height:=observed.height) (age:=live) (floorFit:=floors)
    (keys:=observed.key i live.le) (counts:=observed.count i live.le) (grainRoom:=observed.grain) (layoutRoom:=layoutRoom)
    B number places shape labels pointer flags stored roles positiveRoles tags resources word
  let headers:=accepted_header_venue (X:=X) (G:=G) («S»:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (w:=w) (fit:=fit) (board:=board) (op:=op)
    («frozen»:=frozen) (drift:=drift) (degree:=degree) (payload:=payload) (lo:=lo) (header:=header) (initial:=initial)
    (protected_:=protected_) (beforeHeader:=beforeHeader) (lower:=oldHeader) (votes:=votes) (m:=m) (original:=oldVotes)
    (ticket:=ticket) (before:=before) (after:=after) (located:=located) (accepted:=accepted) (codeRoom:=code)
    (exec:=total code) (cells:=cells) (old:=old) (height:=observed.height) (age:=live) (floorFit:=floors)
    (keys:=observed.key i live.le) (counts:=observed.count i live.le) (grainRoom:=observed.grain) (layoutRoom:=layoutRoom)
    resources
  publicationComponentsMarker actualBoard fixed seen source tagRows headers

open Lean Elab Command in
set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM <| defineOriginalPublication ``originalPublicationComponents `OAI.Hierarchy.DescentSixParty.SeedNamed.profiled_ordinary_publication_context


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
local notation "headerContext" => profiled_ordinary_publication_context X G t rate τ β siteCount payload
  ordinary reset branch positive room shorten w fit board op drift degree degreeMax lo header initial K headRate
  grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher
  signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes ticket before after located
  cells observed old accepted B number places shape labels pointer flags stored roles positiveRoles tags

-- The projection definitions are reducible for dependent field selection.
noncomputable def profiled_ordinary_publication_model := (headerContext).1
noncomputable abbrev profiled_ordinary_header_venue := (headerContext).2
set_option hygiene false in
local notation "datedModel" => (headerContext).1
set_option hygiene false in
local notation "witness" => (datedModel).1
noncomputable def profiled_ordinary_publication_evidence := witness
noncomputable abbrev profiled_ordinary_argument_pose := (datedModel).2

/-- The selected board, its full returned register, and the native tag write. -/
noncomputable def profiled_ordinary_publication := (witness).1

/-- The measured operands for the same returned register, with the signed old archive and full role digits. -/
noncomputable def profiled_ordinary_argument_evidence := (witness).2

/-- All seven argument shelves and the selected board returned by this ordinary date. -/
noncomputable def profiled_ordinary_argument_tables := (witness).1.1

/-- The original paid date publishes valid tag bytes on every cell of its returned register. -/
noncomputable abbrev profiled_ordinary_tag_sources := (witness).1.2

end

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
