import OAI.Hierarchy.DescentNamedProfiledAdmission
import OAI.Hierarchy.DescentRegisteredPositivePitch
import OAI.Hierarchy.DescentRegisteredReceiverWidth
import OAI.Hierarchy.DescentRegisteredDegreeOnCut
import OAI.Hierarchy.DescentRegisterCandidateFloor

namespace OAI
/-! # The native numeric admission checks at a profiled chronological date -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentDatedAddressBook Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)
local notation "cursor" => calendar (w:=w) traces b initial
local notation "steps" => issued (w:=w) traces b
local notation "geo" i:arg => Geometry G S b k w i (cursor i)
variable (tags : ∀c,(traces c).path.kinds=kindCalendar S.rounds S.height)
    (seedDegree : initial.ports.venue.degree=3)
variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x→
  issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y→x=y)
variable (caps : ∀c,(traces c).path.capFactors=capCalendar G.b S.rounds b.gain S.height)
variable (seed : Geometry G S b k w 0 initial)


include tags seedDegree fixed caps seed in
omit [Fintype P] in
private theorem geometryAtEvent (i : ℕ) (evt : RunTrace.Events traces i)
    (previous : ∀j < i, ∀e : RunTrace.Events traces j, fitsAt traces b initial (w:=w) j e) : geo i := by
  obtain ⟨c,e⟩ := evt
  cases e with
  | ordinary before ticket after joined =>
    exact (geometry_degree_on_fitted_cut traces b initial tags seedDegree c fixed caps seed before
      ((Path.here.ordinary ticket).append after)
      ((Path.append_cut_assoc before (Path.here.ordinary ticket) after).symm.trans joined) previous).1
  | reset before ctl after joined =>
    exact (geometry_degree_on_fitted_cut traces b initial tags seedDegree c fixed caps seed before
      ((Path.here.reset ctl).append after)
      ((Path.append_cut_assoc before (Path.here.reset ctl) after).symm.trans joined) previous).1
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
attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
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

open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler.TerminalScale
variable {n₀ δ : ℕ} (board : NonlinearExpanders.Graph n₀ δ) (op : RotorSpec)
    (frozen drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial
local notation "model" i:arg a:arg tick:arg =>
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) (a).floor (menu).ordinary
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) (a).ports (a).floor
set_option maxHeartbeats 6000000

/-- The first unused address of the program selected on the given dated branch. -/
def profiledEnd (i : ℕ) (evt : RunTrace.Events traces i) : ℕ:=by
  let pos:=cursor i
  obtain ⟨c,e⟩:=evt
  cases e with
  | ordinary before ticket after joined=>exact (model i pos ticket).fullEnd pos.floor
  | reset before ctl after joined=>exact (resetAt i pos).fullEnd

local notation "roof" => profiledEnd X G S ordinary reset branch positive room shorten w fit board op frozen drift degree payload lo header initial
local notation "numbers" => profiledNumbers X G S ordinary reset branch positive room shorten w fit board op frozen drift degree payload lo header initial

variable {t rate τ β copies driftR degreeMax ratio : ℕ}
local notation "J" => Nat.log 2 payload/(2*β)
local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g rate).choose
local notation "funds" => 44*argumentDigitRate G t f g rate driftR baseRate

variable (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (schedule : S=stageNumbers G t J f g rate copies frozen)
    (depth : k=groupBits t J (hostRate t rate) (capRate G t g) (cutRate t f g))
    (cutoff : frozen=TerminalScale.tail τ J) (dr : drift+1 ≤ scale J driftR)
    (reach : degree≤degreeMax) (digits : p≤payload) (original : S.firstWidth G.b p≤payload)

include purchase returns receiver schedule depth cutoff dr reach digits original in
theorem profiled_numbers (i : ℕ) (evt : RunTrace.Events traces i)
    (cells : Geometry G S menu k w i (cursor i)) (space : roof i evt<2^w) : numbers i evt:=by
  obtain ⟨c,e⟩:=evt
  cases e with
  | ordinary before ticket after joined=>
    let pos:=cursor i
    have lanes:=Branch.registered_geometry_pitch X G S (trace c) ticket before after joined op
      frozen drift degree payload pos.floor pos.ports (menu).ordinary board (menu).seats (menu).profile header
      cells purchase returns schedule depth cutoff dr reach digits original positive
    exact ⟨lanes.1,space⟩
  | reset before ctl after joined=>
    have rounds : S.rounds=t:=by rw [schedule]; rfl
    have epochs : S.height=J:=by rw [schedule]; rfl
    have atDegree := (cells.degree.le.trans (round_degree_le S.rounds i)).trans_eq
      (congrArg (fun n => maximumDegree (n+1)) rounds)
    have gain : (menu).gain = g := rfl
    have size:=receiver.measured copies i p degree menu (cursor i).ports
      rfl rfl rfl cutoff rfl rfl rfl rfl rfl digits reach atDegree
      (by simpa only [rounds,epochs,gain] using cells.capacity)
      (by rw [←cutoff,←schedule]; exact cells.format.paid)
    exact ⟨by simpa only [←cutoff,←schedule,←depth] using size.1,space⟩

include purchase returns receiver schedule depth cutoff dr reach digits original in
theorem profiled_fits_from_roofs (bus : payload≤w) (sites : 0<k) (seed : initial.ports.venue.degree=3)
    (ends : ∀i (e : RunTrace.Events traces i),
      (∀ j < i, ∀old : RunTrace.Events traces j, fitsAt traces menu initial (w:=w) j old) →
      Geometry G S menu k w i (cursor i) → roof i e<2^w)
    (i : ℕ) (evt : RunTrace.Events traces i) : fitsAt traces menu initial (w:=w) i evt:=by
  revert evt
  induction i using Nat.strong_induction_on with
  | h i previous=>
    intro evt
    have degrees : maximumDegree (S.rounds+1)+1<2^w:=by
      have e : S.rounds=t:=by rw [schedule]; rfl
      rw [e]
      exact receiver.degreeWord w bus
    apply profiled_placement X G S ordinary reset branch positive room shorten w fit board op frozen drift degree
      payload lo header initial bus sites seed degrees i evt
    intro geom
    exact profiled_numbers X G S ordinary reset branch positive room shorten w fit board op frozen drift
      degree payload lo header initial purchase returns receiver schedule depth cutoff dr reach digits original
      i evt geom (ends i evt previous geom)

local notation "steps" => RegisterTimeline.issued (w:=w) traces menu
local notation:max "geom" age:arg => Geometry G S menu k w age (cursor age)

theorem profiled_end_of_issue (i : ℕ) (e : RunTrace.Events traces i) (m : Move w)
    (posted : steps i e (cursor i) m) : m.next.floor=roof i e:=by
  obtain ⟨c,e⟩:=e
  cases e with
  | ordinary before ticket after eqn=>obtain ⟨_,_,rfl⟩:=posted; rfl
  | reset before ctl after eqn=>obtain ⟨_,_,rfl⟩:=posted; rfl

private theorem geometry_before_profile (seed : geom 0) (i : ℕ) (e : RunTrace.Events traces i)
    (previous : ∀ j < i, ∀old : RunTrace.Events traces j, fitsAt traces menu initial (w:=w) j old) :
    geom i:=by
  let common:=all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl
  have seedDegree : initial.ports.venue.degree=3:=by
    have atZero : calendar (w := w) traces menu initial 0 = initial := rfl
    simpa only [atZero, Nat.zero_mod, atRound] using seed.degree
  have kinds (c : (last).Choice) : (traces c).path.kinds = kindCalendar S.rounds S.height := by
    dsimp only [SeedNamed.traceAt]
    exact (trace c).kinds
  have caps (c : (last).Choice) : (traces c).path.capFactors = capCalendar G.b S.rounds (menu).gain S.height := by
    dsimp only [SeedNamed.traceAt]
    exact (trace c).calendar
  exact RegisterTimeline.geometryAtEvent traces menu initial kinds seedDegree
    (fun j a b x y=>common j (cursor j) a b x y) caps seed i e previous

/-- A single exponential bound on offered address increments covers the selected
prefix and the first unplaced event. The empty selector contributes zero. -/
theorem profiled_address_before (seed : geom 0) (A B : ℕ) (live : 0<payload)
    (stages : S.length≤2^(A*payload)) (head : initial.floor≤2^(B*payload))
    (budget : ∀j (e : RunTrace.Events traces j),geom j → roof j e-(cursor j).floor≤2^(B*payload))
    (i : ℕ) (evt : RunTrace.Events traces i)
    (previous : ∀ j < i, ∀old : RunTrace.Events traces j, fitsAt traces menu initial (w:=w) j old)
    (next : ℕ) (offered : next-(cursor i).floor≤2^(B*payload)) : next<2^((A+B+2)*payload):=by
  have still : i<S.length:=by
    obtain ⟨c,e⟩:=evt
    cases e with
    | ordinary before ticket after joined=>have := after.kinds_length; omega
    | reset before ctl after joined=>have := after.kinds_length; omega
  apply candidate_floor steps initial next live still stages head _ offered
  intro j hj
  apply span_of_issued (ι:=fun _=>Unit) (w:=fun _=>w)
    (Cut:=fun _ _ j=>RunTrace.Events traces j) (h:=0) (i:=()) (fun _ _=>steps) (fun _ _=>initial)
  intro old m hit
  have lower:=geometry_before_profile X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial seed j old (fun l hl=>previous l (hl.trans hj))
  rw [profiled_end_of_issue X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial j old m hit]
  exact budget j old lower

theorem profiled_candidate_floor (seed : geom 0) (A B : ℕ) (live : 0<payload)
    (stages : S.length≤2^(A*payload)) (head : initial.floor≤2^(B*payload))
    (budget : ∀j (e : RunTrace.Events traces j),geom j → roof j e-(cursor j).floor≤2^(B*payload))
    (i : ℕ) (evt : RunTrace.Events traces i)
    (previous : ∀ j < i, ∀old : RunTrace.Events traces j, fitsAt traces menu initial (w:=w) j old)
    (current : geom i) : roof i evt<2^((A+B+2)*payload):=by
  exact profiled_address_before X G S ordinary reset branch positive room shorten w fit board op frozen drift
    degree payload lo header initial seed A B live stages head budget i evt previous (roof i evt) (budget i evt current)

include purchase returns receiver schedule depth cutoff dr reach digits original in
theorem profiled_fits_from_spans (bus : payload≤w) (sites : 0<k) (seed : geom 0) (A B : ℕ)
    (stages : S.length≤2^(A*payload)) (head : initial.floor≤2^(B*payload))
    (width : (A+B+2)*payload≤w)
    (budget : ∀j (e : RunTrace.Events traces j),geom j → roof j e-(cursor j).floor≤2^(B*payload))
    (i : ℕ) (evt : RunTrace.Events traces i) : fitsAt traces menu initial (w:=w) i evt:=by
  have seedDegree : initial.ports.venue.degree=3 := by
    have atZero : calendar (w := w) traces menu initial 0 = initial := rfl
    simpa only [atZero, Nat.zero_mod, atRound] using seed.degree
  apply profiled_fits_from_roofs X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial purchase returns receiver schedule depth cutoff dr reach digits original
    bus sites seedDegree _ i evt
  intro j e earlier current
  exact (profiled_candidate_floor X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial seed A B (positive.trans_le digits) stages head budget j e earlier current).trans_le
    (Nat.pow_le_pow_right (by decide) width)

include purchase returns receiver schedule depth cutoff dr reach digits original in
/-- Admission and the actual numeric receipts required by the executable
profiled program hold together for every visited ordinary or reset date. -/
theorem profiled_numbers_from_spans (bus : payload≤w) (sites : 0<k) (seed : geom 0) (A B : ℕ)
    (stages : S.length≤2^(A*payload)) (head : initial.floor≤2^(B*payload))
    (width : (A+B+2)*payload≤w)
    (budget : ∀j (e : RunTrace.Events traces j),geom j → roof j e-(cursor j).floor≤2^(B*payload))
    (i : ℕ) (evt : RunTrace.Events traces i) :
    fitsAt traces menu initial (w:=w) i evt ∧ (geom i → numbers i evt):=by
  have accepted:=profiled_fits_from_spans X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial purchase returns receiver schedule depth cutoff dr reach digits original
    bus sites seed A B stages head width budget
  refine ⟨accepted i evt,?_⟩
  intro current
  have finish:=profiled_candidate_floor X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial seed A B (positive.trans_le digits) stages head budget i evt
    (fun j _=>accepted j) current
  exact profiled_numbers X G S ordinary reset branch positive room shorten w fit board op frozen drift degree
    payload lo header initial purchase returns receiver schedule depth cutoff dr reach digits original i evt current
    (finish.trans_le (Nat.pow_le_pow_right (by decide) width))

/-- Each cut of any actual ballot has both its predecessor geometry and the
native successor required by the terminal raster and readback theorems. -/
theorem profiled_installed (seed : geom 0)
    (placed : ∀i (e : RunTrace.Events traces i),fitsAt traces menu initial (w:=w) i e)
    (i : ℕ) (e : RunTrace.Events traces i) :
    geom i ∧ ∃move : Move w,steps i e (cursor i) move ∧ move.next.floor<2^w ∧
      (e.2.isReset=true → 8*(menu).receiverWidth G S k i (cursor i).ports≤payload):=by
  have early:=geometry_before_profile X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial seed i e (fun j _=>placed j)
  exact ⟨early,placed i e early⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
