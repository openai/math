import OAI.Hierarchy.DescentNamedProfileOnCPU
import OAI.Hierarchy.DescentRegisteredIncomingVenue
import OAI.Hierarchy.DescentNamedObservedSeats
import OAI.Hierarchy.DescentObservedWordRoom
import OAI.Hierarchy.DescentRegisteredOrdinaryExecution

namespace OAI
/-! # Reading an original packed ballot with the reached registered matcher -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
set_option cleanup.letToHave false
open scoped Fin.CommRing
open StarKeys DescentStageEdgeReceipt
attribute [local irreducible] normalizedPackedChart SeedNamed.issued
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : (S.firstWidth G.b p) < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook
variable {n₀ δ : ℕ} (board : NonlinearExpanders.Graph n₀ δ) (op : RotorSpec)
    (frozen drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial

open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
local notation "pitch" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial


open DescentCompiler.TerminalScale DescentGroupPeerOrder DescentStageEdgeReceipt
open DescentColonies DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentPackedColony
local notation "pos₀" => cursor
local notation "v₂" i:arg tick:arg => DatePorts.ordinaryModel (cursor i).ports tick op g frozen p f drift degree
  payload ((menu).seats i) (cursor i).floor (menu).ordinary
local notation "liveCPU" => DateCode.history cpu
local notation "load₂" i:arg tick:arg => (v₂ i tick).archivePhase (cursor i).floor ((menu).profile i) w

open Lean Elab Term in
local elab "applyProfileArguments% " f:term:arg "[" xs:term,* "]" : term => do
  let fn ← elabTerm f none
  return mkAppN fn (← xs.getElems.mapM fun x => elabTerm x none)

open Lean Meta Elab Term in
local elab "roomForProfile% " fn:term:arg br:term:arg tk:term:arg "[" xs:term,* "]" : term => do
  let f ← elabTerm fn none
  let b ← elabTerm br none
  let t ← elabTerm tk none
  let some bt ← whnfUntil (← inferType b) ``SeedNamed.Branch | throwError "expected a named branch"
  let some tt ← whnfUntil (← inferType t) ``OrdinaryLink | throwError "expected an ordinary link"
  unless bt.getAppFn.isConstOf ``SeedNamed.Branch && tt.getAppFn.isConstOf ``OrdinaryLink do
    throwError "expected branch/link, got {bt.getAppFn} ({bt.getAppNumArgs}) and {tt.getAppFn} ({tt.getAppNumArgs})"
  let bs := bt.getAppArgs
  let ts := tt.getAppArgs
  unless bs.size == 20 && ts.size == 25 do throwError "unexpected branch or ordinary-link telescope"
  let branchArgs := bs.extract 0 14 ++ #[bs[17]!, bs[14]!, bs[15]!, bs[16]!, bs[18]!, bs[19]!, b]
  let event := #[ts[11]!, ts[12]!, ts[13]!, ts[14]!, ts[22]!, ts[23]!, ts[8]!, ts[17]!,
    ts[19]!, ts[18]!, ts[20]!, ts[21]!, ts[24]!, t]
  return mkAppN f (branchArgs ++ event ++ (← xs.getElems.mapM fun x => elabTerm x none))

theorem registered_physical_report (protected_ : ∀j,RegisterTimeline.Protected (cpu j) (cursor j).floor header)
    (beforeHeader : lo+extent pitch (ch).layout≤header) (lower : header< initial.floor)
    (votes : (ch).Pin→Bool) (m : Memory w)
    (original : ∀a∈shelves pitch lo 0 (ch).layout,∀j:Fin (slots a.src.seats pitch),
      m (a.base+j.val)=((packed a.src.pin votes pitch j.val).val:Word w))
    (c : (last).Choice) {W : MarkedWorld F 0 pins widths}
    {i z D z' D' : ℕ} {rate : ℝ} {nonneg : 0 ≤ fee}
    {prior : Reached W G price fee S k i z D (S.epochPower^S.priceExponent) s} {T : StageInput W G rate fee}
    {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' (S.epochPower^S.priceExponent) s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path (trace c).origin.source prior) (after : Path next (trace c).target)
    (joined : (before.ordinary ticket).append after=(trace c).path)
    (codeRoom : DatePorts.OrdinaryCodeRoom (cursor i).ports ticket op g frozen p f drift degree payload
      ((menu).seats i) (cursor i).floor (menu).ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom (cursor i).ports ticket op g frozen p f drift degree payload
      ((menu).seats i) (cursor i).floor (menu).ordinary w ((menu).profile i) header codeRoom)
    (cells : RegisterTimeline.Geometry G S menu k w i (cursor i))
    (old : (cursor i).ports.held prior (cursor i).floor (liveCPU m i))
    (height : 0<S.height) (age : i<S.length) (floorFit : (cursor i).floor<2^w)
    (keys : S.groupCount i*hostRows (S.hostSize i)*S.radix<2^w)
    (counts : (S.groupCount i*hostRows (S.hostSize i)*S.radix)*2^(8+S.capGain*i)<2^w)
    (grainRoom : 2*DescentPackedEpochShelves.unit G.C≤payload/2) :
    ∃(e:Source (ch).Pin) (wide:Fintype.card prior.V≤2^(v₂ i ticket).level)
      (actual:(prior.placement.stage.result nonneg).Choice)
      (ext:DescentTerminalEpochBits.width e.C≤(v₂ i ticket).area.shapeAt.digit),
      (ch).layout[before.selections.length]?=some e ∧ HEq choice actual ∧
      (load₂ i ticket).Runs (liveCPU m i) ∧
      stageVenue prior wide (cursor i).ports.io (v₂ i ticket).area.lanesAt (v₂ i ticket).bitsPerField
        ((v₂ i ticket).stageStart (cursor i).floor) (prior.venueRoster wide) ((load₂ i ticket).image (liveCPU m i)) ∧
      (v₂ i ticket).reachedReport (cursor i).ports.io ((v₂ i ticket).stageStart (cursor i).floor) wide
        ((load₂ i ticket).image (liveCPU m i)) actual e votes ext:=by
  let V:=v₂ i ticket
  let position_:=cursor i
  let a:=V.area
  let report := applyProfileArguments% (@profile_on_cpu) [
    F, (inferInstance : Field F), cp, nP, X, G, S, k, cut, tail, n, h, C, f, g, p,
    ordinary, reset, branch, positive, room, shorten, w, fit, n₀, δ, board, op,
    frozen, drift, degree, payload, lo, header, initial, protected_, beforeHeader, lower,
    votes, m, original, c, W, i, z, D, z', D', rate, nonneg, prior, T, choice, norm, next,
    ticket, before, after, joined, floorFit]
  let e := report.choose
  have reportFields := report.choose_spec
  have head := reportFields.1
  have alphabet := reportFields.2.1
  have seats := reportFields.2.2.1
  have sourceFit := reportFields.2.2.2.2.2.1
  have readback := reportFields.2.2.2.2.2.2
  let pulse := applyProfileArguments% (@issued_observation_inputs) [
    F, (inferInstance : Field F), cp, nP, X, G, S, k, cut, tail, n, h, C, f, g, p,
    ordinary, reset, branch, positive, room, shorten, w, fit, c, W, i, z, D, z', D',
    rate, nonneg, prior, T, choice, norm, next, ticket, before, after, joined, height, age.le, e, head]
  have names := pulse.1
  have mass := pulse.2.1
  let actual := pulse.2.2.choose
  have chosen := pulse.2.2.choose_spec.1
  have seated := pulse.2.2.choose_spec.2
  have matcher_ : ((menu).ordinary i).payload=payload ∧
      ((menu).ordinary i).unit=(DonorDate.atDate G S g k i p).amount := ⟨rfl,rfl⟩
  let incoming := roomForProfile% (@Branch.registered_incoming_venue) (trace c) ticket [
    before, after, joined, op, frozen, drift, degree, payload, position_.floor, position_.ports,
    (menu).ordinary, n₀, δ, board, (menu).seats, (menu).profile, header, w,
    (liveCPU m i), age, cells, matcher_, old]
  let wide := incoming.choose
  have stored := incoming.choose_spec.1
  have wires := incoming.choose_spec.2.1
  have ext : DescentTerminalEpochBits.width e.C≤a.shapeAt.digit:=by
    rw [alphabet]
    exact le_max_left ..
  have nativeSite : (GroupStage.plane V.hostNumbers wide).trans Fin.valEmbedding=prior.vertex.trans Fin.valEmbedding:=by
    ext v
    rfl
  have named : prior.placement.SiteNamed (groupRank ((Equiv.refl (Fin (S.groupCount i))).toEmbedding.trans Fin.valEmbedding)
      ((GroupStage.plane V.hostNumbers wide).trans Fin.valEmbedding)):=by rw [nativeSite];exact names
  have capPos : 0<prior.placement.cap:=lt_of_lt_of_le (by decide : 0<256)
    (roomForProfile% (@Branch.signed_source_capacity) (trace c) ticket [before, after, joined])
  let date_:=DonorDate.atDate G S g k i p
  have dated:=roomForProfile% (@Branch.donor_date_eq) (trace c) ticket [before, after, joined]
  have geom : a=date_.schedule payload ((menu).seats i) (S.censusBits p):=by
    change ticket.ordinaryArea (Nat.clog 2 (S.hostSize i)) (S.censusBits p) payload date_.amount
      (DescentTerminalEpochBits.width G.C) ((menu).seats i)=_
    exact congrArg₂ (fun degree_ cap_ => (⟨hostRows (S.hostSize i), S.groupCount i,
      k, S.censusBits p, degree_, cap_, payload, date_.amount, DescentTerminalEpochBits.width G.C,
      (menu).seats i⟩ : DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary))
      (congrArg DonorDate.degree dated) (congrArg DonorDate.cap dated)
  have safe : a.Space position_.ports.io w (V.stageStart position_.floor):=geom.symm ▸ exec.matcher
  have U : Phase.unit a.k a.b≤a.unit:=(le_max_left ..).trans safe.chooserWidth
  have up : 0<a.unit:=(show 0<Phase.unit a.k a.b by dsimp [Phase.unit];omega).trans_le U
  have arrayPos : 0<a.lanesAt:=(occupancy a.payload a.unit up safe.laneWidth).1
  have pairPos : 0<a.shapeAt.pairs:=by
    change 0<2^k*(2^k*(1+prior.placement.degree*2^k)*(2*prior.placement.cap))
    positivity
  have oldPos : 0<pitch:=(occupancy (payload/2) (DescentPackedEpochShelves.unit G.C)
    (Nat.succ_pos _) grainRoom).1
  have newPitch : V.profileRepack.newLanes = a.lanesAt*a.shapeAt.pairs :=
    (congrArg (fun area : DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary =>
      area.lanesAt * area.shapeAt.pairs) geom).symm
  have radix:=ordinary.radix
  refine ⟨e,wide,actual,ext,head,chosen,?_⟩
  apply V.observed_venue_from_shelf position_.ports.io position_.floor ((menu).profile i) wide
    (liveCPU m i) actual e votes ext safe rfl stored wires named mass
  · have count : V.schedule.groupCount V.age * 2^V.level = S.groupCount i * hostRows (S.hostSize i) := rfl
    have sides : 2^V.k = S.radix := radix.symm
    exact (congrArg₂ Nat.mul count sides).trans_lt keys
  · exact prior.core_padded.trans_lt (by simpa only [radix] using counts)
  · exact seated.trans seats.le
  · exact seats.symm
  · rw [alphabet];rfl
  · exact newPitch
  · exact oldPos
  · exact (Nat.mul_pos arrayPos pairPos).trans_eq newPitch.symm
  · exact sourceFit
  · exact exec.raw
  · exact readback

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
