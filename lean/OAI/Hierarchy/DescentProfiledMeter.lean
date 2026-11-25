import OAI.Hierarchy.DescentProfiledResetPrivateWord
import OAI.Hierarchy.DescentAcceptedPrivateStep
import OAI.Hierarchy.DescentProfiledOriginalReadbacks
import OAI.Hierarchy.DescentNamedShelfWidths

namespace OAI
/-! # The true private charge accumulated at every selected ordinary and reset cut -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
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
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
set_option cleanup.letToHave false
attribute [local irreducible] SeedNamed.issued Origin.source Origin.archivePackage
attribute [local irreducible] RegisterTimeline.privateStep RegisterTimeline.issued RegisterTimeline.position
  RegisterTimeline.date DateCode.history
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
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

open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
local notation "pitch" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial


open DescentCompiler.TerminalScale DescentGroupPeerOrder DescentStageEdgeReceipt
open DescentColonies DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup
local notation "pos₀" => cursor
local notation "v₂" i:arg tick:arg => DatePorts.ordinaryModel (cursor i).ports tick op g frozen p f drift degree
  payload ((menu).seats i) (cursor i).floor (menu).ordinary
local notation "liveCPU" => DateCode.history cpu
local notation "load₂" i:arg tick:arg => (v₂ i tick).archivePhase (cursor i).floor ((menu).profile i) w


local notation "windows" => profiledExecution X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
local notation "data" => fun i=>RegisterTimeline.Geometry G S menu k w i (cursor i)
local notation "tag" => RegisterTimeline.Menu.resetFlag S
local notation "rot" => fun i=>(menu).rotationAt G S k i (cursor i)
local notation "sel" => fun i=>(menu).selectorAt G S k i (cursor i)

local notation "numbers" => profiledNumbers X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
local notation "chosen" v:arg => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow v

/-- On every accepted history, each ordinary instruction accumulates the fee measured
at the original winning rows. Each reset preserves the same running total. -/
theorem profiled_meter (bus:payload≤ w) (site:0< k)
    (seedDegree:initial.ports.venue.degree=3) (degreeRoom:maximumDegree (S.rounds+1)+1<2^w)
    (seed:data 0) (paid:∀i (e:RunTrace.Events traces i),data i→numbers i e)
    (hardware:∀i (e:RunTrace.Events traces i),data i→windows i e)
    (beforeHeader:lo+extent pitch (ch).layout≤ header) (lower:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (oldVotes:∀a∈shelves pitch lo 0 (ch).layout,∀j:Fin (slots a.src.seats pitch),
      m (a.base+j.val)=((packed a.src.pin votes pitch j.val).val:Word w))
    (observed:ObservationRoom G S payload w) :
    ∀i (event:(traces (chosen votes)).path.Event i),(ch).read votes=some (chosen votes) →
      event.incoming (cursor i) (DateCode.history cpu m i) →
      privateStep traces menu initial (chosen votes) m header i event :=by
  have placed (j:ℕ) (e:RunTrace.Events traces j) : RegisterTimeline.fitsAt traces menu initial (w:=w) j e := profiled_placement X G S ordinary reset branch positive
    room shorten w fit board op frozen drift degree payload lo header initial bus site seedDegree degreeRoom j e (paid j e)
  have protected_:=profiled_instruction X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial bus site seedDegree degreeRoom seed paid hardware
  intro i event accepted seen
  dsimp only [SeedNamed.traceAt] at event
  cases event with
  | @ordinary owner srcZ srcD dstZ dstD sourceRate sourceRecord nonnegative entryStage selectedChoice normalizeStage destination before ticket after joined=>
    let evt:RunTrace.Events traces i:=⟨chosen votes,.ordinary before ticket after joined⟩
    let localized := profiled_installed X G S ordinary reset branch positive room shorten w fit
      board op frozen drift degree payload lo header initial seed placed i evt
    let geom := localized.1
    let move := Classical.choose localized.2
    have provision := Classical.choose_spec localized.2
    have posted := provision.1
    have roomAt := (RegisterTimeline.forward traces menu i evt (cursor i) move posted).trans_lt provision.2.1
    dsimp only [evt] at posted
    unfold RegisterTimeline.issued at posted
    let lowerK := Classical.choose posted
    let code := Classical.choose posted.choose_spec
    have active : i < S.length := by
      have date := after.kinds_length
      omega
    let shelfFound := registered_profile_exists X G S ordinary reset branch positive room shorten
      w fit payload lo (chosen votes) (W:=owner) (i:=i) (z:=srcZ) (D:=srcD) (z':=dstZ) (D':=dstD) (rate:=sourceRate)
      (nonneg:=nonnegative) (prior:=sourceRecord) (T:=entryStage) (choice:=selectedChoice)
      (norm:=normalizeStage) (next:=destination) ticket before after joined
    let shelf := Classical.choose shelfFound
    have atDate := Classical.choose_spec shelfFound
    have hit := atDate.2.1
    have entry := atDate.2.2.1
    have atShelf:=RegisterTimeline.fromProfiles_at G S board op k frozen p f g drift degree payload lo header
      (ch).layout i shelf hit
    have seats:=(normalized_shelf_widths X G S ordinary reset branch positive room shorten w fit
      shelf.src (List.mem_of_getElem? entry)).2
    have layoutRoom:=(Nat.mul_le_mul_right (G.C+8+8*G.k) (atShelf.2.1.le.trans seats)).trans_lt observed.score
    unfold RegisterTimeline.privateStep
    intro prior
    apply accepted_private_step X G S ordinary reset branch positive room shorten w fit board op frozen drift degree
      payload lo header initial protected_ beforeHeader lower votes m oldVotes (W:=owner) (i:=i) (z:=srcZ) (D:=srcD) (z':=dstZ) (D':=dstD) (rate:=sourceRate)
      (nonneg:=nonnegative) (prior:=sourceRecord) (T:=entryStage) (choice:=selectedChoice)
      (norm:=normalizeStage) (next:=destination) ticket before after joined (Or.inr accepted)
      code (hardware i evt geom code) geom seen observed.height active roomAt (observed.key i active.le)
      (observed.count i active.le) observed.grain layoutRoom prior
    intro other change_ acquired
    apply all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl i
      (cursor i) other evt change_ _ acquired
    dsimp only [evt]
    unfold RegisterTimeline.issued
    exact ⟨lowerK,code,rfl⟩
  | reset before B after joined=>
    exact profiled_reset_private_step X G S ordinary reset branch positive room shorten w fit board op frozen
      drift degree payload lo header initial bus seedDegree degreeRoom seed paid (chosen votes) m i
      (.reset before B after joined) rfl lower placed

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
