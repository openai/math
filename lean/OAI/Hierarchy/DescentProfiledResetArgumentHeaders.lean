import OAI.Hierarchy.DescentProfiledPreviousArchive
import OAI.Hierarchy.DescentProfiledResetArgumentGeometry
import OAI.Hierarchy.DescentMatchedRetainedHeaders
import OAI.Hierarchy.DescentMatchedFreshHeaders
import OAI.Hierarchy.DescentScheduledSelectedReady
import OAI.Hierarchy.DescentProfiledMathematicalReset

namespace OAI
/-! # The four headers of every original operand at a registered reset -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentKernelHistory DescentRotor
noncomputable section
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k : ℕ} {W₀ W : MarkedWorld F d P bits}
variable {i₀ z₀ D₀ i z D w hist : ℕ} {start : Reached W₀ G q ε S k i₀ z₀ D₀ w hist}
variable {source : Reached W G q ε S k i z D w hist}
private theorem profiled_rank_reset {n h C f g cut tail : ℕ} {ctl : ResetRates G S k D n h C f g cut tail}
    (hp : 0 < p) (b : ClosedReset source ctl) (a : Archive W₀)
    (initial : DescentLocalArchiveOrder.Local a.bit) (before : Path start source)
    (whole : (before.reset b).whole p) :
    DescentLocalArchiveOrder.trajectory p hp a initial (before.reset b) whole =
      DescentLocalArchiveOrder.reset b p hp whole.2 (before.archive p hp a whole.1)
        (DescentLocalArchiveOrder.trajectory p hp a initial before whole.1) := rfl

end
end Hierarchy.DescentBundleHistory

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline DescentExteriorReplay ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
local notation "cert" => SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage
variable (drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "board" => reset.board
local notation "op" => RotorSpec.ofRates reset
local notation "frozen" => tail
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) a.ports a.floor

local notation "data" => fun i=>Geometry G S menu k w i (cursor i)
local notation "program" => RegisterTimeline.instruction (w:=w) traces menu initial

variable (bus : payload≤w) (seedDegree : initial.ports.venue.degree=3)
    (degreeRoom : maximumDegree (S.rounds+1)+1<2^w)

variable (walk : (last).Choice) (m : Memory w)
variable {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
  {r : Reached U G price fee S k i z D (S.epochPower^S.priceExponent) s}
  {n₁ h₁ C₁ f₁ g₁ cut₁ tail₁ : ℕ} {ctl : ResetRates G S k D n₁ h₁ C₁ f₁ g₁ cut₁ tail₁}
  (before : Path (trace walk).origin.source r) (B : ClosedReset r ctl)
  (after_ : Path B.next (trace walk).target) (joined : (before.reset B).append after_=(trace walk).path)
local notation "evt" => (Path.Event.reset before B after_ joined : (traces walk).path.Event i)
local notation "cur" => cursor i
local notation "history" => DateCode.history program m i
local notation "padEnd" => (cur).ports.priorStart k (cur).floor

local notation "inner₁" => (resetAt i cur).inner

local notation "prior₁" => ((cur).ports.afterPad k (cur).floor).archive
local notation "support₁" => PhysicalReset.ScheduledCodeRoom G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports.operandLanes (cur).ports.roleLanes
  (cur).ports.venue (cur).ports.io padEnd w prior₁
local notation "tag₁" => ((kindCalendar S.rounds S.height).drop i).head?
local notation "full₁" => (resetAt i cur).fullEnd
local notation "issued₁" cap₁:arg sp₁:arg => DatePorts.resetDate G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w cap₁ sp₁
local notation "ready₁" cap₁:arg sp₁:arg => PhysicalReset.ScheduledReady G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports.operandLanes (cur).ports.roleLanes (cur).ports.venue
  (cur).ports.io padEnd w prior₁ cap₁ sp₁

local notation "R₁" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "one₁" => le_max_left 1 (max reset.bitsR (C*reset.bitsR))
open private first_width_multiple_of_p from OAI.Hierarchy.DescentProfiledResetArgumentGeometry
local notation "pinWidth" => first_width_multiple_of_p S G.b p
local notation "divides" => fun _ : pins=>by simpa only [Nat.mul_one] using (pinWidth : p∣s)
local notation "source" => (trace walk).origin
open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
open private Origin.archiveOrder from OAI.Hierarchy.DescentNamedPrivateArchive
open private Palette.encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
local notation "firstShape" => Origin.archiveShape source p R₁ positive one₁ pinWidth
local notation "rawCode" => Palette.encodedOrigin (p:=p) source op reset.menu
local notation "pinNumber" => fun y : pins=>y.1.val
open private chosenClaim from OAI.Hierarchy.DescentNamedArchivePrefix
local notation "claim" => chosenClaim X G S ordinary reset branch positive room shorten w walk
local notation "nextPath" => before.reset B
local notation "oldDesc" hw:arg => (before.archive p positive (source).archive (hw).1).bit
local notation "rank₀" hw:arg => trajectory p positive (source).archive (Origin.archiveOrder source) before (hw).1
local notation "shape₀" hw:arg hb:arg => archiveShape positive one₁ divides (source).archive firstShape before (hw).1 (hb).1
local notation "label₀" hw:arg hr:arg => (encodePath op reset.menu before positive (hw).1 (hr).1 (source).archive rawCode).atNode
local notation "capacity" => ((capCalendar G.b S.rounds g S.height).take i).prod*256
local notation "u₁" sp:arg => DatePorts.resetInputs G S board k frozen i p f g drift degree payload (menu).ordinary op
  s (S.grainAt G.b p 0) (cur).ports (cur).floor w sp
local notation "z₁" geo:arg sp:arg => DatePorts.resetFinalInputs G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w (geo).capacity sp
local notation "ports₁" sp:arg => DatePorts.resetPorts G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w sp
local notation "pad₁" => priorArchivePhase G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w
local notation "ingress" => (inner₁).ingress
local notation "ingressPhase" => (ingress).phase padEnd w (cur).ports.io.hubs (fun x=>(cur).ports.io.atoms x.val)
  (fun j=>(cur).ports.io.wire j.1.val j.2.val)
local notation "atMem" => (ingressPhase).image ((pad₁).image history)
local notation "dst" => DateCode.history program m (i+1)

local notation "desc₁" hw:arg => ((nextPath).archive p positive (source).archive hw).bit
local notation "rank₁" hw:arg => trajectory p positive (source).archive (Origin.archiveOrder source) nextPath hw
local notation "shape₁" hw:arg hb:arg => archiveShape positive one₁ divides (source).archive firstShape nextPath hw hb
local notation "label₁" hw:arg hr:arg => (encodePath op reset.menu nextPath positive hw hr (source).archive rawCode).atNode

local notation "oldA" hw:arg => before.archive p positive (source).archive (hw).1

attribute [local irreducible] SeedNamed.issued Origin.source Origin.archivePackage

private def profiledHeaderConsequence : Prop := ∀
    (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁) (hr : (nextPath).OnlyRotor op)
    (bounds : DatePorts.RangeRoom (cur).ports r (oldDesc hw))
    (geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space)
    (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (boardAt : HEq ctl.board board) (opAt : RotorSpec.ofRates ctl=op)
    (degreeAt : (cur).ports.venue.degree=D) (capAt : r.placement.cap=capacity)
    (held : RegisterTimeline.MatchedRegisteredOperandPanels board op B p drift degree payload w
      (menu).ordinary (menu).seats (menu).profile (menu).header cur space (rank₀ hw) bounds (shape₀ hw hb)
      (label₀ hw hr) geo geo.room.archive hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt)
    (previous : claim before cur history) (sized : (cur).ports.RoleRows) (rolePos : 0<(cur).ports.roleLanes)
    (layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space))
    (places : DatePorts.RangeRoom (ports₁ space) B.next (desc₁ hw)) (limit : R₁≤drift)
    (actorMem : Memory w) (acted : (u₁ space).ThroughActors atMem actorMem)
    (orig : RegisterTimeline.MatchedPublicOriginsAt board op B p drift degree payload w (menu).ordinary cur space
      hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt actorMem)
    (fresh : RegisterTimeline.MatchedFreshInputsAt board op B p drift degree payload w (menu).ordinary cur space
      hn hh hf hg ht boardAt opAt admitted.1 actorMem)
    (choice : ∀ix,DatePorts.OrdinalRead (u₁ space) admitted.1 layout.small actorMem ix)
    (oldHeaders : DatePorts.SevenOriginHeaders (u₁ space) B.next (desc₁ hw) (rank₁ hw) places (shape₁ hw hb)
      positive pinNumber admitted.1 layout.small layout.axes actorMem choice (resetOrigin B positive hw.2 (oldA hw)) Sum.inl),
    DatePorts.SevenHeaders (u₁ space) B.next (desc₁ hw) (rank₁ hw) places
      (shape₁ hw hb) positive pinNumber admitted.1 layout.small layout.axes actorMem choice

include after_ joined in
private theorem profiled_header_from_old :
    profiledHeaderConsequence X G S ordinary reset branch positive room shorten w fit
      drift degree payload lo header initial walk m before B :=by
  unfold profiledHeaderConsequence
  intro seed₁ placed₁ hw hb hr bounds geo space admitted hn hh hf hg ht boardAt opAt degreeAt capAt held previous
    sized rolePos layout places limit actorMem acted orig fresh choice oldHeaders
  let ctlData := profiled_reset_controls X G S ordinary reset branch positive room shorten walk before B after_ joined
  exact DatePorts.registered_reset_headers (u₁ space) B.next (desc₁ hw) (rank₁ hw) places (shape₁ hw hb)
    positive pinNumber admitted.1 layout.small layout.axes actorMem choice (resetOrigin B positive hw.2 (oldA hw))
    oldHeaders (RegisterTimeline.matched_fresh_headers board op B p drift degree payload w (menu).ordinary cur space
      (oldA hw) (rank₀ hw) (shape₀ hw hb) ctlData.1 positive one₁ hb.2.1 hw.2 hb.2.2.2 pinNumber places ctl.height
      ctlData.2.2.2.2.2 branch hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt actorMem ctlData.2.2.2.1
      ctlData.2.2.2.2.1 fresh orig layout.small layout.axes choice)


open Lean Elab Term in
local elab "retainedKernel% " fn:term:arg "[" xs:term,* "]" : term => do
  let f ← elabTerm fn none
  let args := xs.getElems
  unless args.size == 89 do throwError "matched_retained_headers requires its 89 arguments"
  return mkAppN f (← args.mapM fun x => elabTerm x none)

private def profiledOldHeaderConsequence : Prop := ∀
    (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁) (hr : (nextPath).OnlyRotor op)
    (bounds : DatePorts.RangeRoom (cur).ports r (oldDesc hw))
    (geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space)
    (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (boardAt : HEq ctl.board board) (opAt : RotorSpec.ofRates ctl=op)
    (degreeAt : (cur).ports.venue.degree=D) (capAt : r.placement.cap=capacity)
    (held : RegisterTimeline.MatchedRegisteredOperandPanels board op B p drift degree payload w
      (menu).ordinary (menu).seats (menu).profile (menu).header cur space (rank₀ hw) bounds (shape₀ hw hb)
      (label₀ hw hr) geo geo.room.archive hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt)
    (previous : claim before cur history) (sized : (cur).ports.RoleRows) (rolePos : 0<(cur).ports.roleLanes)
    (layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space))
    (places : DatePorts.RangeRoom (ports₁ space) B.next (desc₁ hw)) (limit : R₁≤drift)
    (actorMem : Memory w) (acted : (u₁ space).ThroughActors atMem actorMem)
    (orig : RegisterTimeline.MatchedPublicOriginsAt board op B p drift degree payload w (menu).ordinary cur space
      hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt actorMem)
    (fresh : RegisterTimeline.MatchedFreshInputsAt board op B p drift degree payload w (menu).ordinary cur space
      hn hh hf hg ht boardAt opAt admitted.1 actorMem)
    (choice : ∀ix,DatePorts.OrdinalRead (u₁ space) admitted.1 layout.small actorMem ix),
    DatePorts.SevenOriginHeaders (u₁ space) B.next (desc₁ hw) (rank₁ hw) places (shape₁ hw hb)
      positive pinNumber admitted.1 layout.small layout.axes actorMem choice (resetOrigin B positive hw.2 (oldA hw)) Sum.inl


set_option maxHeartbeats 3600000 in
include after_ joined bus in
private theorem profiled_old_headers :
    profiledOldHeaderConsequence X G S ordinary reset branch positive room shorten w fit
      drift degree payload lo header initial walk m before B :=by
  unfold profiledOldHeaderConsequence
  intro seed₁ placed₁ hw hb hr bounds geo space admitted hn hh hf hg ht boardAt opAt degreeAt capAt held previous
    sized rolePos layout places limit actorMem actionProof orig fresh choice
  let controls := profiled_reset_controls X G S ordinary reset branch positive room shorten walk before B after_ joined
  let capacityRows := profiled_reset_argument_geometry X G S ordinary reset branch positive room
    shorten w fit drift degree payload lo header initial walk before B after_ joined seed₁ placed₁ hw hb geo space
    layout controls.2.2.2.1 limit
  let nextNumber : DescentLocalArchiveOrder.Local (desc₁ hw) :=
    DescentLocalArchiveOrder.reset B p positive hw.2 (oldA hw) (rank₀ hw)
  let nextShape : WorldShape p R₁ (desc₁ hw) :=
    DescentBundleHistory.reset_shape_at positive one₁ B (oldA hw) (shape₀ hw hb) hb.2.1 hw.2 hb.2.2.2
  have shapeStep : shape₁ hw hb = nextShape := DescentBundleHistory.archive_shape_reset positive one₁ divides B
    (source).archive firstShape before hw hb
  have rankStep : rank₁ hw = nextNumber := DescentBundleHistory.profiled_rank_reset positive B (source).archive
    (Origin.archiveOrder source) before hw
  let fitsShape (sh : WorldShape p R₁ (desc₁ hw)) : Prop :=
    ∀ v y, ((sh.sites v).recipe positive).arity y ≤ (ports₁ space).argumentsPerNode
  have physicalArity : fitsShape nextShape := Eq.mp (congrArg fitsShape shapeStep) capacityRows.2.2
  let headersAt (num : DescentLocalArchiveOrder.Local (desc₁ hw)) (sh : WorldShape p R₁ (desc₁ hw)) : Prop :=
    DatePorts.SevenOriginHeaders (u₁ space) B.next (desc₁ hw) num places sh positive pinNumber
      admitted.1 layout.small layout.axes actorMem choice (resetOrigin B positive hw.2 (oldA hw)) Sum.inl
  have sameHeaders : headersAt (rank₁ hw) (shape₁ hw hb) = headersAt nextNumber nextShape :=
    (congrArg (fun num => headersAt num (shape₁ hw hb)) rankStep).trans
      (congrArg (fun sh => headersAt nextNumber sh) shapeStep)
  refine Eq.mpr sameHeaders ?_
  exact retainedKernel% (@RegisterTimeline.matched_retained_headers) [
    F, pins, (inferInstance : Field F), 0, widths, U,
    G, price, fee, S, k, i,
    z, D, n₁, h₁, C₁, f₁,
    g₁, cut₁, tail₁, S.epochPower^S.priceExponent, s, r,
    ctl, n, h, f, g, tail,
    board, op, B, p, drift, degree,
    payload, w, (menu).ordinary, (menu).seats, (menu).profile, (menu).header,
    cur, space, oldA hw, R₁, rank₀ hw, bounds,
    shape₀ hw hb, label₀ hw hr, geo, geo.room.archive, controls.1,
    positive, one₁, hb.2.1, hw.2, hb.2.2.2, pinNumber,
    places, capacityRows.2.1, physicalArity, ctl.height, controls.2.2.2.2.2, branch,
    sized, rolePos, bus, capacityRows.1, archiveFlag r (oldA hw).bit (rank₀ hw) (cur).ports bounds, hn,
    hh, hf, hg, ht, boardAt, opAt,
    degreeAt, admitted.1, history, capAt, (RegisterTimeline.archive_read_at_bounds
      (fun bd : DatePorts.RangeRoom (cur).ports r (oldA hw).bit =>
        DatePorts.ArchiveRead (cur).ports r (oldA hw).bit (rank₀ hw) bd (shape₀ hw hb) op (label₀ hw hr)
          (Reached.argumentPointer r (oldA hw).bit (rank₀ hw) (shape₀ hw hb) positive pinNumber (cur).ports.argumentsPerNode)
          (archiveFlag r (oldA hw).bit (rank₀ hw) (cur).ports bd) history)
      (previous hw.1 hb.1 hr.1) bounds), held,
    actorMem, (@actionProof), orig, layout.small, layout.axes, choice]



set_option maxHeartbeats 3600000 in
include after_ joined bus in
theorem profiled_reset_headers
    (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁) (hr : (nextPath).OnlyRotor op)
    (bounds : DatePorts.RangeRoom (cur).ports r (oldDesc hw))
    (geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space)
    (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (boardAt : HEq ctl.board board) (opAt : RotorSpec.ofRates ctl=op)
    (degreeAt : (cur).ports.venue.degree=D) (capAt : r.placement.cap=capacity)
    (held : RegisterTimeline.MatchedRegisteredOperandPanels board op B p drift degree payload w
      (menu).ordinary (menu).seats (menu).profile (menu).header cur space (rank₀ hw) bounds (shape₀ hw hb)
      (label₀ hw hr) geo geo.room.archive hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt)
    (previous : claim before cur history) (sized : (cur).ports.RoleRows) (rolePos : 0<(cur).ports.roleLanes)
    (layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space))
    (places : DatePorts.RangeRoom (ports₁ space) B.next (desc₁ hw)) (limit : R₁≤drift)
    (actorMem : Memory w) (acted : (u₁ space).ThroughActors atMem actorMem)
    (orig : RegisterTimeline.MatchedPublicOriginsAt board op B p drift degree payload w (menu).ordinary cur space
      hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt actorMem)
    (fresh : RegisterTimeline.MatchedFreshInputsAt board op B p drift degree payload w (menu).ordinary cur space
      hn hh hf hg ht boardAt opAt admitted.1 actorMem)
    (choice : ∀ix,DatePorts.OrdinalRead (u₁ space) admitted.1 layout.small actorMem ix) :
    DatePorts.SevenHeaders (u₁ space) B.next (desc₁ hw) (rank₁ hw) places
      (shape₁ hw hb) positive pinNumber admitted.1 layout.small layout.axes actorMem choice :=by
  let full : profiledHeaderConsequence X G S ordinary reset branch positive room shorten w fit
      drift degree payload lo header initial walk m before B := profiled_header_from_old X G S ordinary reset branch positive room shorten w fit
    drift degree payload lo header initial walk m before B after_ joined
  let retained : profiledOldHeaderConsequence X G S ordinary reset branch positive room shorten w fit
      drift degree payload lo header initial walk m before B := profiled_old_headers X G S ordinary reset branch positive room shorten w fit
    drift degree payload lo header initial bus walk m before B after_ joined
  exact full seed₁ placed₁ hw hb hr bounds geo space admitted hn hh hf hg ht boardAt opAt degreeAt capAt
      held previous sized rolePos layout places limit actorMem acted orig fresh choice
    (retained seed₁ placed₁ hw hb hr bounds geo space admitted hn hh hf hg ht boardAt opAt degreeAt capAt
      held previous sized rolePos layout places limit actorMem acted orig fresh choice)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
