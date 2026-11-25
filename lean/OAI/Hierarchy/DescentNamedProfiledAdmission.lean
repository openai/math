import OAI.Hierarchy.DescentRegisteredClipRoom
import OAI.Hierarchy.DescentNamedRegisteredProfile
import OAI.Hierarchy.DescentNamedPrefixState
import OAI.Hierarchy.DescentRegisteredResetFits

namespace OAI
/-! # Public room for the actual profiled ordinary and reset opcodes -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM DescentSIMDLookup DescentOrdinaryVenueIngress
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 500000

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))} {hu : 0 ≤ (((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ))*((S.epochPower^S.priceExponent):ℝ))} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=(GroupStage.depthBound (atRound S.rounds) n f g)) (t:=S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 ((Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))) ((fun _ : ((Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))))=>(S.firstWidth G.b p)*1))} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G ((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)) ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))}
    {nonneg : 0 ≤ ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G ((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)) ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)

open DescentTerminalEpochChart DescentPackedEpochShelves
open Chronology.RegisterTimeline
variable {bn bd : ℕ} {A : Type} (board:NonlinearExpanders.Graph bn bd) (op:RotorSpec) (frozen drift degree payload lo header w : ℕ)
    (entries:List (Source A)) (a:RegisterTimeline.Position)
local notation "selected" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header entries
local notation "m₀" => DatePorts.ordinaryModel a.ports ticket op g frozen p f drift degree payload ((selected).seats i) a.floor (selected).ordinary
include before cut tail in
private theorem geometry_of_profile_menu (geom:RegisterTimeline.Geometry G S selected k w i a)
    (bus : payload≤w) (positiveLanes : 0<(m₀).resolver.lanes) (space:(m₀).fullEnd a.floor<2^w) :
    DatePorts.OrdinaryCodeRoom a.ports ticket op g frozen p f drift degree payload ((selected).seats i) a.floor (selected).ordinary w := by
  have clock:=tail.kinds_length
  have age : i<S.length:=by omega
  exact @registered_geometry_fits F _ cp pins X G S k n h C f g p R he hu radix run c br
    W i z D z' D' rate prior T nonneg choice norm next ticket before tail cut op frozen drift degree payload
    a.floor a.ports (selected).ordinary bn bd board (selected).seats (selected).profile header w age bus geom
    geom.degree ⟨rfl,rfl⟩ positiveLanes space
end
end Hierarchy.DescentSixParty.SeedNamed.Branch

namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentCompiler
noncomputable section

private theorem ordinaryProfileMove {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F}
    {S : AtomSchedule} {bits : P → ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C → RunTrace G q ε S k wire hist final bits d)
    {bn bd : ℕ} (b : Menu bn bd) (a : Position)
    (c : C) {i z D z' D' : ℕ} {rate : ℝ} {U : MarkedWorld F d P bits}
    {src : Reached U G q ε S k i z D wire hist} {he : 0 ≤ ε}
    {T : StageInput U G rate ε} {choice : (T.result he).Choice}
    {norm : Normalize ((T.result he).state choice)}
    {dst : Reached norm.result G q ε S k (i+1) z' D' wire hist}
    (before : Path (traces c).first src) (ticket : OrdinaryLink src he T choice norm dst)
    (after : Path dst (traces c).last) (joined : (before.ordinary ticket).append after = (traces c).path)
    (sites : 0 < k) (admitted : DatePorts.OrdinaryCodeRoom a.ports ticket b.op b.gain b.tail b.p b.f
      b.drift b.degreeLimit b.payload (b.seats i) a.floor b.ordinary w)
    (roof : (DatePorts.ordinaryModel a.ports ticket b.op b.gain b.tail b.p b.f b.drift
      b.degreeLimit b.payload (b.seats i) a.floor b.ordinary).fullEnd a.floor < 2^w) :
    let event : RunTrace.Events traces i := ⟨c, .ordinary before ticket after joined⟩
    ∃ m : Move w, issued traces b i event a m ∧ m.next.floor < 2^w ∧
      (event.2.isReset = true → 8*b.receiverWidth G S k i a.ports ≤ b.payload) := by
  dsimp only
  refine ⟨_, ⟨sites, admitted, rfl⟩, roof, ?_⟩
  intro impossible
  cases impossible

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
set_option maxRecDepth 12000
set_option cleanup.letToHave false
attribute [local irreducible] normalizedPackedChart
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
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
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
local notation "model" i:arg a:arg tick:arg =>
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) (a).floor (menu).ordinary
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) a.ports a.floor
set_option maxHeartbeats 6000000

/-- Only three concrete scalar bounds remain after the preceding register geometry
has been installed. The hardware and the chosen profile are already fixed. -/
def profiledNumbers (i : ℕ) (evt : RunTrace.Events traces i) : Prop:=by
  let pos:=cursor i
  rcases evt with ⟨c,e⟩
  cases e with
  | ordinary before ticket after eqn=>
    let v:=model i pos ticket
    exact 0<v.resolver.lanes ∧ v.fullEnd pos.floor<2^w
  | reset before ctl after eqn=>
    exact 8*(menu).receiverWidth G S k i pos.ports≤payload ∧ (resetAt i pos).fullEnd<2^w


local notation "numbers" => profiledNumbers X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
section
private theorem chosenKind (c : (last).Choice) :
    (traces c).path.kinds = kindCalendar S.rounds S.height := by
  dsimp only [traceAt]
  exact (SeedNamed.issued X G S ordinary reset branch positive room shorten c).kinds

attribute [local irreducible] SeedNamed.issued traceAt

private theorem concreteResetFits (bus : payload ≤ w)
    (seedDegree : initial.ports.venue.degree = 3) (degreeRoom : maximumDegree (S.rounds+1)+1 < 2^w)
    (i : ℕ) (evt : RunTrace.Events traces i) (isReset : evt.2.isReset = true)
    (numeric : numbers i evt) : fitsAt traces menu initial (w:=w) i evt := by
  obtain ⟨c,e⟩ := evt
  cases e with
  | ordinary before ticket after joined => cases isReset
  | reset before ctl after joined =>
    let event : RunTrace.Events traces i := ⟨c,.reset before ctl after joined⟩
    let pos := cursor i
    change 8*(menu).receiverWidth G S k i pos.ports ≤ payload ∧ (resetAt i pos).fullEnd < 2^w at numeric
    exact RegisterTimeline.reset_fits traces menu initial
      (chosenKind X G S ordinary reset branch positive room shorten) i event rfl numeric.1 bus
      seedDegree degreeRoom numeric.2
end

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

include fit in
theorem profiled_placement (bus : payload≤w) (sites : 0<k)
    (seedDegree : initial.ports.venue.degree=3) (degreeRoom : maximumDegree (S.rounds+1)+1<2^w)
    (i : ℕ) (evt : RunTrace.Events traces i)
    (paid : Geometry G S menu k w i (cursor i)→numbers i evt) :
    fitsAt traces menu initial (w:=w) i evt:=by
  intro geom
  obtain ⟨c,e⟩:=evt
  cases e with
  | ordinary before ticket after joined=>
    let pos:=cursor i
    let v:=model i pos ticket
    have size:=paid geom
    change 0<v.resolver.lanes ∧ v.fullEnd pos.floor<2^w at size
    have admitted : DatePorts.OrdinaryCodeRoom pos.ports ticket op g frozen p f drift degree payload
        ((menu).seats i) pos.floor (menu).ordinary w :=
      roomForProfile% (@Branch.geometry_of_profile_menu) (trace c) ticket [
      before, after, joined, n₀, δ, (ch).Pin, board, op, frozen, drift, degree,
      payload, lo, header, w, (ch).layout, pos, geom, bus, size.1, size.2]
    exact RegisterTimeline.ordinaryProfileMove traces menu pos c before ticket after joined sites admitted size.2
  | reset before ctl after joined=>
    let e : RunTrace.Events traces i := ⟨c,.reset before ctl after joined⟩
    exact concreteResetFits X G S ordinary reset branch positive room shorten w fit
      board op frozen drift degree payload lo header initial bus seedDegree degreeRoom i e rfl
      (paid geom) geom

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
