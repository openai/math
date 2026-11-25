import OAI.Hierarchy.DescentRegisteredAcceptedDonor
import OAI.Hierarchy.DescentDatedOrdinaryPostedCut

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ}
    {C : Type*} (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position) (c : C) (mem : Memory w)

local notation "t" => (traces c)
local notation "code" => instruction (w:=w) traces b initial
variable {i z D z' D' : ℕ} {u : ℝ} {W : MarkedWorld F d P bits}
    {src : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {nrm : Normalize ((T.result he).state choice)}
    {dst : Reached nrm.result G q ε S k (i+1) z' D' wire hist}
    (before : Path (traces c).first src) (ticket : OrdinaryLink src he T choice nrm dst)
    (after : Path dst (traces c).last) (cut : (before.ordinary ticket).append after=(traces c).path)
local notation "evt" => (Path.Event.ordinary before ticket after cut)
local notation "at₀" => (calendar (w:=w) traces b initial i)
local notation "ports" => (at₀).ports
local notation "root₀" => (at₀).floor
local notation "ram" => DateCode.history code mem i
local notation "make" f:arg => f ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload
    (b.seats i) root₀ b.ordinary
local notation "v" => make DatePorts.ordinaryModel


local notation "prog" pos:arg cash:arg => (make DatePorts.ordinaryDate) w (b.profile i) b.header pos cash
local notation "next₀" => (⟨make DatePorts.ordinaryPorts,(v).fullEnd root₀⟩ : Position)
local notation "mv" pos:arg cash:arg => (⟨(prog pos cash),next₀⟩ : Move w)


set_option maxHeartbeats 1000000 in
include before ticket after cut in
omit [Fintype P] in
private theorem settledMeteredStep (positive : 0<k) (room : (make DatePorts.OrdinaryCodeRoom) w)
    (exec : (make DatePorts.OrdinaryExecutionRoom) w (b.profile i) b.header room)
    (fixed : ∀r : RunTrace.Events traces i, ∀y : Move w, issued traces b i r at₀ y → y = mv positive room)
    (header : ℕ) (held : (before.ordinary ticket).Held header
        ((make DatePorts.ordinaryOutput) w (b.profile i) b.header positive room exec ram)) :
    (before.ordinary ticket).Held header (DateCode.history code mem (i+1)) := by
  have actual := ordinary_posted_cut traces b initial c mem before ticket after cut positive room exec fixed
  exact actual.2.2.symm ▸ held
end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
set_option cleanup.letToHave false
local notation "s" => S.firstWidth G.b p
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
open DescentSIMDLookup DescentGroupPeerOrder DescentHaloWalkRAM
local notation "v₂" i:arg tick:arg => DatePorts.ordinaryModel (cursor i).ports tick op g frozen p f drift degree
  payload ((menu).seats i) (cursor i).floor (menu).ordinary
local notation "liveCPU" => DateCode.history cpu


private abbrev acceptedWalkAt (votes : (ch).Pin→Bool) :=
  (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes
local notation "walk₀" z:arg => acceptedWalkAt X G S ordinary reset branch positive room shorten w fit z
attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage normalizedRoute

private theorem meterFromDonor {A B : Sort*} {P Q : A → B → Prop} {oldHeld newHeld : Prop}
    (measured : ∃ a b, P a b ∧ Q a b ∧ (oldHeld → newHeld)) (ready : oldHeld) : newHeld :=
  measured.choose_spec.choose_spec.2.2 ready

/-- An accepted ordinary date advances the private charge in the native chronological memory. -/
theorem accepted_private_step (protected_ : ∀j,RegisterTimeline.Protected (cpu j) (cursor j).floor header)
    (beforeHeader : lo+extent pitch (ch).layout≤header) (lower : header< initial.floor)
    (votes : (ch).Pin→Bool) (m : Memory w)
    (original : ∀a∈shelves pitch lo 0 (ch).layout,∀j:Fin (slots a.src.seats pitch),
      m (a.base+j.val)=((packed a.src.pin votes pitch j.val).val:Word w))
    {W : MarkedWorld F 0 pins widths} {i z D z' D' : ℕ} {rate : ℝ} {nonneg : 0 ≤ fee}
    {prior : Reached W G price fee S k i z D (S.epochPower^S.priceExponent) s} {T : StageInput W G rate fee}
    {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' (S.epochPower^S.priceExponent) s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path (trace (walk₀ votes)).origin.source prior) (after : Path next (trace (walk₀ votes)).target)
    (located : (before.ordinary ticket).append after=(trace (walk₀ votes)).path)
    (accepted : before.selections.length+1<((ch).rows votes).length ∨ (ch).read votes=some (walk₀ votes))
    (codeRoom : DatePorts.OrdinaryCodeRoom (cursor i).ports ticket op g frozen p f drift degree payload
      ((menu).seats i) (cursor i).floor (menu).ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom (cursor i).ports ticket op g frozen p f drift degree payload
      ((menu).seats i) (cursor i).floor (menu).ordinary w ((menu).profile i) header codeRoom)
    (cells : RegisterTimeline.Geometry G S menu k w i (cursor i))
    (old : (cursor i).ports.held prior (cursor i).floor (liveCPU m i))
    (height : 0<S.height) (age : i<S.length) (floorFit : (cursor i).floor<2^w)
    (keys : S.groupCount i*hostRows (S.hostSize i)*S.radix<2^w)
    (counts : (S.groupCount i*hostRows (S.hostSize i)*S.radix)*2^(8+S.capGain*i)<2^w)
    (grainRoom : 2*DescentPackedEpochShelves.unit G.C≤payload/2)
    (layoutRoom : (menu).seats i*(G.C+8+8*G.k)<2^w)
    (oldHeld : before.Held header (liveCPU m i))
    (fixed : ∀r : RunTrace.Events traces i,∀y : RegisterTimeline.Move w,
      RegisterTimeline.issued traces menu i r (cursor i) y →
        y=⟨DatePorts.ordinaryDate (cursor i).ports ticket op g frozen p f drift degree payload
            ((menu).seats i) (cursor i).floor (menu).ordinary w ((menu).profile i) header
            prior.placement.fieldBits codeRoom,
          DatePorts.ordinaryPorts (cursor i).ports ticket op g frozen p f drift degree payload
            ((menu).seats i) (cursor i).floor (menu).ordinary,(v₂ i ticket).fullEnd (cursor i).floor⟩) :
    (before.ordinary ticket).Held header (liveCPU m (i+1)) :=by
  have measured := accepted_at_donor_and_meter X G S ordinary reset branch positive room shorten w fit
    board op frozen drift degree payload lo header initial protected_ beforeHeader lower votes m original ticket
    before after located accepted codeRoom exec cells old height age floorFit keys counts grainRoom layoutRoom
  exact RegisterTimeline.settledMeteredStep traces menu initial (walk₀ votes) m before ticket after located
    prior.placement.fieldBits codeRoom exec fixed header (meterFromDonor measured oldHeld)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
