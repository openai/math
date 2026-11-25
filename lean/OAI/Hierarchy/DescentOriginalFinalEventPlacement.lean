import OAI.Hierarchy.DescentOriginalWordReplay
import OAI.Hierarchy.DescentOriginalLastBankPlacement
import OAI.Hierarchy.DescentTerminalMaskWordFromReadout

namespace OAI
/-! # The registered final event and the terminal census on the original paid addresses -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentTerminalFixedSlices
open DescentInitialHost DescentSeedRoot DescentDatedSeedStartup DescentPackedEpochShelves DescentWideSeedFlags
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentMixedRouter DescentResetInvoice Chronology RegisterTimeline
open DescentPackedProfileInstall DescentExterior DescentExteriorShelf Catalyst CatalystSubstitution CorrectionBatch
open Computability.BorderVNP.Crossing ThreeFlat.Routing
open DescentTerminalCompiledPrefix DescentTerminalPreflightSpace DescentTerminalLocalPortBook
open DescentTerminalLast DescentDatedAddressBook.PhysicalReset ProtocolRAM
open DescentExteriorMatrixUpdate
open DescentTerminalCompiledPrefix.AddressPlan
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] normalizedPackedChart SeedNamed.issued
set_option maxRecDepth 12000
set_option cleanup.letToHave false
section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
variable (c : (Epochs.finish G _ _ (SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice) (height : 0<S.height)


private def eventResetOnPath : Path.FinalReset p (issued X G S ordinary reset branch positive room shorten c).path := by
  exact ((issued X G S ordinary reset branch positive room shorten c).path).finalReset p (issued X G S ordinary reset branch positive room shorten c).recorded (by
    rw [(issued X G S ordinary reset branch positive room shorten c).kinds]
    exact kindCalendar_last S.rounds height)

open private register_cap_calendar from OAI.Hierarchy.DescentNamedPrefixState
open private traceAt_kinds from OAI.Hierarchy.DescentNamedBranchMachine
variable (w : ℕ) {nn dd : ℕ} (b : Menu nn dd) (initial : Position)
local notation "traceFamily" => traceAt X G S ordinary reset branch positive room shorten
local notation "point" => RegisterTimeline.calendar (w:=w) traceFamily b initial
local notation "prevDate" => point (S.length-1)
local notation "lastPhase" => Phase.atPorts G S b.board k b.tail (S.length-1) b.p b.f b.gain b.drift
  b.degreeLimit b.payload b.ordinary b.op (prevDate).ports (prevDate).floor
include c height in
private theorem profileFinalCoordinates (gainEq : b.gain=g) (grainEq : b.p=p) (arityEq : b.f=f)
    (seedRoom : Geometry G S b k w 0 initial)
    (placed : ∀i (e : RunTrace.Events (traceAt X G S ordinary reset branch positive room shorten) i),
      RegisterTimeline.fitsAt (traceAt X G S ordinary reset branch positive room shorten) b initial (w:=w) i e) :
    (prevDate).ports.venue.k=k ∧ (lastPhase).output.metadataEnd (lastPhase).dateBase=(point S.length).floor ∧
    S.length-1+1=S.length :=by
  let ticket:=issuedFinalReset X G S ordinary reset branch positive room shorten c height
  have same := all_registered_moves X G S ordinary reset branch positive room shorten w b gainEq grainEq arityEq
  let fixed := fun i l r x y=>same i (point i) l r x y
  have caps := register_cap_calendar X G S ordinary reset branch positive room shorten b gainEq
  have tags := traceAt_kinds X G S ordinary reset branch positive room shorten
  have geo := RegisterTimeline.geometry_on_event traceFamily b initial fixed caps tags seedRoom placed c (S.length-1) ticket.event
  obtain ⟨move,hit,_,_⟩:=placed (S.length-1) ⟨c,ticket.event⟩ geo
  obtain ⟨_,_,_,_,next⟩:=RegisterTimeline.final_move traceFamily b initial c ticket fixed ⟨move,hit⟩
  exact ⟨geo.format.width,(congrArg Position.floor next).symm,ticket.succ_age⟩

end

variable {F:Type} [Field F] (G:PoweredGadget F) {n d:ℕ} (board:NonlinearExpanders.Graph n d)
  (op:RotorSpec) (t f g rate cut drift limit τ β h:ℕ) (x:ShellSource F h)
  (branch:G.b≤2^(capRate G t g)) (head dates billed last W slots:ℕ)
local notation "J" => Nat.log 2 h/(2*β)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G t J f g rate x.sites tb
local notation "k" => groupBits t J (hostRate t rate) (capRate G t g) (cutRate t f g)
local notation "p" => headGrain G S k h
local notation "s" => (S).firstWidth G.b p
local notation "W₀" => NativeBranch.binLimit («k»:=k) S
local notation "q" => headArity G S
local notation "w" => W*h
variable (ordinary:OrdinaryRates G (stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β)))) (groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) cut) (reset:ResetRates G (stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β)))) (groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) (atRound t) n d op.C f g cut (tail τ (Nat.log 2 h/(2*β))))
  (positive:0<(headGrain G (stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β)))) (groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) h)) (shorten:reentryRate d op.C*(1-(2-G.rate)/4)^t≤1/2) (fit:(((stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β))))).firstWidth G.b (headGrain G (stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β)))) (groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) h))<2^(W*h))
  (H degree wire hist:ℕ)
local notation "trace" => traceAt x.X G S ordinary reset branch positive x.opened shorten
local notation "chart" => normalizedPackedChart x.X G S ordinary reset branch positive x.opened shorten w fit
local notation "ss" => (chart).layout
local notation "bins" => terminalBinCount x.X G S p q W₀ n d op.C f g+1
local notation "raw" => terminalRawRows x.X G S p q n d op.C f g
local notation "V" => originalSeedHead G op drift x.X ss S k tb h H degree wire hist bins raw
local notation "origin" => (V).position G op t f g drift h
local notation "lo" => selectorBase x.X (S).copies s h (ss).length
local notation "header" => (V).base G h-1
local notation "menu" => fromProfiles G S board op k tb p f g drift degree h lo header ss
local notation "cursor" => calendar («w»:=w) trace menu origin
local notation "age" => (S).length-1
local notation "phase" => Phase.atPorts G S board k tb age p f g drift degree h (menu).ordinary op
  (cursor age).ports (cursor age).floor
local notation "pitch" => grain (h/2) G.C
local notation "snapshots" => SnapshotCalendar reset (kindCalendar (S).rounds (S).height)
  (capCalendar G.b (S).rounds g (S).height) (snapshotDirectory («w»:=w) trace menu origin)

local notation "z" => originalReplay G board op t f g rate cut drift τ β h x branch W ordinary reset positive
  shorten fit H degree wire hist
local notation "headRate" => t+1+max dates head+2
variable (funds:OriginalWord G board op t f g rate cut drift limit branch head dates billed last W τ β h (drift+1) slots)
  (low:2^h≤x.sites) (dyadic:∃a,x.sites=2^a) (host:x.sites≤H) (upper:H≤hostRows x.sites)
  (coeff:degree≤limit)

local notation "specDate" => earnedPreflight G t f g rate τ β n d op.C op drift x
local notation "replay" => (z).replayStart G t f g rate β x
local notation "early" => Calendar.earlyEnd S k tb replay (V).j (V).rest s (Fintype.card (Port x.ports x.X.width))
local notation "sliceEnd" => (phase).stop early
local notation "cal" => Branch.replayCalendar x.X S k tb (V).j (V).rest snapshots
local notation "page" => (specDate).scanPages ((cal).packetEnd sliceEnd) q
local notation "census" => (page).stop
local notation "out" => (phase).output
local notation "base" => (phase).dateBase
local notation "shops" => (specDate).scalar.shops
local notation "paidPage" => fun i : Fin (specDate).scalar.blocks => (out).terminalPaid base i.val
local notation "actorPage" => fun i : Fin (specDate).scalar.blocks => (out).terminalActor base i.val
local notation "wing" => fun (i:Fin (specDate).scalar.blocks) (a:Fin (2*(specDate).cap)) =>
  (out).terminalWing base i.val a.val
local notation "rawCensus" => censusScanBase G t f g rate τ β n d op.C op drift x z

open Lean Elab Term in
local elab "eventApply% " fn:term:arg "[" args:term,* "]" : term => do
  let e ← elabTerm fn none
  return mkAppN e (← args.getElems.mapM fun arg => elabTerm arg none)

open Lean Elab Term in
local elab "eventConjunction% " "[" args:term,* "]" : term => do
  let terms := args.getElems
  let mut result ← elabTerm terms.back! none
  let mut resultType ← Lean.Meta.inferType result
  for item in terms.pop.reverse do
    let proof ← elabTerm item none
    let proofType ← Lean.Meta.inferType proof
    result := mkApp4 (mkConst ``And.intro) proofType resultType proof result
    resultType := mkApp2 (mkConst ``And) proofType resultType
  return result

private theorem positive_group_sum (a b : ℕ) : 0<a+8+b :=by omega

set_option maxHeartbeats 2400000 in
include funds low dyadic host upper coeff in
/-- The installed final reset and its measured lookup determine the last slice and the native cursor. -/
theorem original_final_event_geometry :
    FinalSliceFields G S k drift h phase ∧ (cursor age).ports.venue.k=k ∧
    (phase).output.metadataEnd (phase).dateBase=(cursor (S).length).floor ∧ age+1=(S).length :=by
  let source:=funds.calendar.words.seed x.sites low x.upper dyadic x.X ordinary reset positive x.opened shorten
    w fit H degree wire hist host upper funds.calendar.words.seedFits
  have native : s≤h:=(S).split_first_width G.b h W₀ (2^headChunk G S) (Nat.two_pow_pos _)
  have grainSize:p≤h:=(S).grain_le_payload G.b p h G.base_pos native
  have group : 0<k:=positive_group_sum _ _
  have growing:drift+1≤ TerminalScale.scale J (drift+1):=by
    unfold TerminalScale.scale
    exact (Nat.le_mul_of_pos_right (drift+1) (Nat.succ_pos _)).trans Nat.lt_two_pow_self.le
  have places:=profiled_calendar_at_rate x.X G t rate τ β x.sites h ordinary reset branch positive x.opened shorten
    w fit board op drift degree limit lo header origin dates head funds.calendar.words.steps funds.pitches.old
    funds.pitches.returned funds.receiver growing x.upper grainSize coeff native source.geometry group source.head
    funds.calendar.words.datesFit
  let walk:=(normalizedRoute x.X G S ordinary reset branch positive x.opened shorten w fit).follow (fun _=>false)
  have occupied (i : ℕ) (e : RunTrace.Events trace i) :
      RegisterTimeline.fitsAt trace menu origin («w»:=w) i e := (places i e).1
  have receipt := eventApply% (@eventResetOnPath) [F, (inferInstance : Field F), x.cp, x.ports, x.X, G, S,
    k, cut, tb, n, d, op.C, f, g, p, ordinary, reset, branch, positive, x.opened, shorten, walk, funds.started]
  have located := eventApply% (@original_last_lookup) [F, (inferInstance : Field F), x.cp, x.ports,
    x.X, G, n, d, op.C, f, g, p, cut, tb, t, rate, τ, β, x.sites, h, ordinary, reset,
    branch, positive, x.opened, shorten, w, fit, n, d, board, op, drift, degree, limit, lo,
    header, origin, x.upper, grainSize, coeff, source.geometry, occupied, walk, receipt, funds.lookup]
  have levels := eventApply% (@profileFinalCoordinates) [F, (inferInstance : Field F), x.cp, x.ports, x.X, G, S,
    k, cut, tb, n, d, op.C, f, g, p, ordinary, reset, branch, positive, x.opened, shorten, walk, funds.started,
    w, n, d, menu, origin, (rfl : (menu).gain=g), (rfl : (menu).p=p), (rfl : (menu).f=f), source.geometry, occupied]
  exact ⟨located,levels⟩

private theorem stop_from_fields {K : Type} [Field K] {G₀ : PoweredGadget K} {A : AtomSchedule}
    {bits delay height : ℕ} {P : Phase K} (current : FinalSliceFields G₀ A bits delay height P) (start : ℕ) :
    P.stop start = AddressPlan.sliceStop start P.output.argumentSlots P.digits (2^bits) (A.hostSize A.length) :=
  congrArg₂ (AddressPlan.sliceStop start P.output.argumentSlots P.digits) current.blocks current.hosts

private theorem transport_mask_bound (mask : ℕ → ℕ) {a b w₀ : ℕ} (same : a=b)
    (bound : mask b < 2^w₀) : mask a < 2^w₀ :=
  (congrArg mask same).trans_lt bound

private theorem transport_role_bound (stop : ℕ → ℕ) {a b x₀ : ℕ} (same : a=b)
    (fits : x₀ ≤ stop b) : x₀ ≤ stop a :=
  fits.trans_eq (congrArg stop same.symm)

set_option maxHeartbeats 2400000 in
include funds low dyadic host upper coeff in
/-- The paid readout places every final-event bank for the same registered schedule and ballot-independent program. -/
theorem original_final_event_placement (history:drift=max 1 (max reset.bitsR (op.C*reset.bitsR)))
    (L:TerminalPlacement) (channels:DescentTerminalVertexFields.MaskAllocation.Channels (S).radix) :
    shops=(out).receiver.hosts ∧ 0<shops ∧ (out).metadataEnd base≤early ∧
    DescentSIMDLookup.chunks (out).receiver.groups (out).receiver.lanes=1 ∧
    (z).roleBase G t f g rate β x+DescentTerminalRoleTables.count (originalRoleBits G op S p drift)≤
      (specDate).cohortEnd census ∧
    (specDate).Before census paidPage actorPage wing ((out).terminalPeer base) (page).total (page).modulo
      ((cal).homes sliceEnd) (page).boundaries ∧
    (∀i,shops≤(paidPage i).size) ∧ (∀i a,shops≤(wing i a).size) ∧
    (out).venue.next.signedLanes=(S).groupCount (S).length ∧ (specDate).maskBase census<2^w :=by
  have eventBounds := eventApply% (@original_final_event_geometry) [F, (inferInstance : Field F), G, n, d, board, op,
    t, f, g, rate, cut, drift, limit, τ, β, h, x, branch, head, dates, billed, last, W, slots, ordinary, reset,
    positive, shorten, fit, H, degree, wire, hist, funds, low, dyadic, host, upper, coeff]
  have located := eventBounds.1
  have oldK := eventBounds.2.1
  have finish := eventBounds.2.2.1
  have atEnd := eventBounds.2.2.2
  have baseGroups : (S).baseGroups=2^tb:=rfl
  have earlier : (out).metadataEnd base≤early:=by
    have first : (cursor (S).length).floor≤(z).roleBase G t f g rate β x:=Nat.le_max_left ..
    have second : (z).roleBase G t f g rate β x≤replay:=Nat.le_add_right ..
    have third : replay≤early:=by
      exact (((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
    exact finish.le.trans (first.trans (second.trans third))
  have splice := eventApply% (@stop_from_fields) [F, (inferInstance : Field F), G, S, k, drift, h, phase, located, early]
  let stopFor := fun e : ℕ => ((specDate).scanPages ((cal).packetEnd e) q).stop
  have same : census=rawCensus := congrArg stopFor splice
  have word := eventApply% (@original_replay_word) [F, (inferInstance : Field F), G, n, d, board, op, t, f, g,
    rate, cut, drift, limit, τ, β, h, x, branch, head, dates, billed, last, W, slots, ordinary, reset, positive,
    shorten, fit, H, degree, wire, hist, funds, low, dyadic, host, upper, coeff, history, L, channels]
  have funded := word.2
  have rawMask := eventApply% (@AddressPlan.mask_room_from_trailing) [(S).radix, w, earnedFormat G op S q p drift,
    earnedShell G t f g rate τ β n d op.C x L, earnedInput G t f g rate τ β n d op.C op drift x L, channels,
    (specDate).maskBase rawCensus, raw, (V).appendix.codes*2^(q*p), funded]
  have mask := eventApply% (@transport_mask_bound) [(specDate).maskBase, census, rawCensus, w, same, rawMask]
  have rawRoles := eventApply% (@original_role_before_census) [F, (inferInstance : Field F), G, n, d, board, op, t, f, g,
    rate, cut, drift, τ, β, h, x, branch, W, ordinary, reset, positive, shorten, fit, H, degree, wire, hist]
  have roles := eventApply% (@transport_role_bound) [(specDate).cohortEnd, census, rawCensus,
    (z).roleBase G t f g rate β x+DescentTerminalRoleTables.count (originalRoleBits G op S p drift), same, rawRoles]
  have rows := eventApply% (@Branch.last_bank_placement) [F, (inferInstance : Field F), x.cp, x.ports,
    x.X, G, S, k, g, p, tb, q, drift, op, terminalPool x.X G S p q W₀ n d op.C f g, terminalPool x.X G S p q W₀ n d op.C f g,
    (V).j, (V).rest, snapshots, n, d, board, age, f, degree, h, (menu).ordinary,
    (cursor age).ports.operandLanes, (cursor age).ports.roleLanes, (cursor age).ports.venue,
    (cursor age).ports.io.wire, (cursor age).ports.io.roster, (cursor age).ports.priorStart k (cursor age).floor,
    early, w, baseGroups, atEnd, oldK, earlier, mask]
  have sitesPositive : 0<x.sites:=(Nat.two_pow_pos h).trans_le low
  have alive : 0<shops:=by
    change 0<x.sites*(2^_*2^_)^_
    exact Nat.mul_pos sitesPositive (pow_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) _)
  exact eventConjunction% [located.hosts.symm, alive, earlier, located.receiver, roles, rows.1,
    rows.2.1, rows.2.2.1, located.rawSigned, mask]

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
