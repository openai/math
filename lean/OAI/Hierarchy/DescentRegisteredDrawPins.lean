import OAI.Hierarchy.DescentNamedProfileOnCPU
import OAI.Hierarchy.DescentNamedObservedProfiles
import OAI.Hierarchy.DescentRegisteredOrdinaryStep
import OAI.Hierarchy.DescentDatedStageObserved

namespace OAI
/-! # The registered matcher's profile words at an accepted ordinary cut -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open SeedNamed DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing DescentDatedAddressBook
open DescentStageEdgeReceipt DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open DescentKernelHistory.BitDescription DescentPackedProfileWide StarKeys
open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open scoped Classical Fin.CommRing
set_option maxHeartbeats 1200000

variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "s" => S.firstWidth G.b p
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : s < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "route" => normalizedRoute X G S ordinary reset branch positive room shorten w fit
variable (z : (ch).Pin → Bool)
local notation "walk" => (route).follow z
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

variable {W : MarkedWorld F 0 pins widths} {i grain D z' D' : ℕ} {rate : ℝ} {he : 0 ≤ fee}
    {prior : Reached W G price fee S k i grain D (S.epochPower^S.priceExponent) s} {T : StageInput W G rate fee}
    {choice : (T.result he).Choice} {norm : Normalize ((T.result he).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' (S.epochPower^S.priceExponent) s}
    (ticket : OrdinaryLink prior he T choice norm next)
    (before : Path (trace walk).origin.source prior) (after : Path next (trace walk).target)
    (located : (before.ordinary ticket).append after=(trace walk).path)
    (accepted : before.selections.length+1 < ((ch).rows z).length ∨ (ch).read z=some walk)
variable (ports : DatePorts) (op : RotorSpec) (frozen drift degree payload seats root : ℕ) (dates : ℕ→Dated.Ordinary)
local notation "v" => ordinaryModel ports ticket op g frozen p f drift degree payload seats root dates
local notation "gid" => (Equiv.refl (Fin (S.groupCount i))).toEmbedding

include located accepted in
/-- The padded host number used by the actual donor gives the scanned profile
at every address, including the addresses beyond its genuine matched pairs. -/
theorem registered_draw_pins (entry : Source (ch).Pin)
    (header : (ch).layout[before.selections.length]?=some entry)
    (wide : Fintype.card prior.V ≤ (v).area.H) (ext : DescentTerminalEpochBits.width entry.C ≤ (v).area.shapeAt.digit) :
    ∃pick : (prior.placement.stage.result he).Choice, HEq choice pick ∧
      ∀j,(wideCell entry.pin z (v).area.shapeAt.digit ext j).val =
        profileAt (inputNumber he prior.placement gid (GroupStage.plane (v).hostNumbers wide))
          ((scannedRows he prior.placement.stage).profile pick) j :=by
  exact observed_profile_pins X G S ordinary reset branch positive room shorten w fit z ticket
    before after located entry header accepted (GroupStage.plane (v).hostNumbers wide) wide
    (fun _=>rfl) (v).area.shapeAt.digit ext

variable {n₀ δ : ℕ} (board : NonlinearExpanders.Graph n₀ δ)
    (lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial
local notation "model" => ordinaryModel (cursor i).ports ticket op g frozen p f drift degree payload
  ((menu).seats i) (cursor i).floor (menu).ordinary
local notation "pitch" => DescentPackedEpochShelves.grain (payload/2) G.C

set_option hygiene true
include located accepted in
/-- A single selected header supplies both the retained input words on the
registered CPU and every wide profile digit accepted by the physical matcher. -/
theorem registered_loaded_draw_pins (wide : Fintype.card prior.V ≤ (model).area.H)
    (protected_ : ∀j,RegisterTimeline.Protected (cpu j) (cursor j).floor header)
    (beforeHeader : lo+extent pitch (ch).layout ≤ header) (lower : header < initial.floor)
    (m : Memory w) (original : ∀a∈shelves pitch lo 0 (ch).layout,∀j:Fin (slots a.src.seats pitch),
      m (a.base+j.val)=((packed a.src.pin z pitch j.val).val:Word w))
    (space : (cursor i).floor < 2^w) :
    ∃entry : Source (ch).Pin,(ch).layout[before.selections.length]?=some entry ∧
      entry.C=G.C ∧ entry.seats=(menu).seats i ∧ entry.seats≤S.batch ∧
      Fintype.card (NativePair W.graph W.core (scanHomeAt he prior.placement.stage)
        (scanColorAt he prior.placement.stage) prior.placement.cap) ≤ entry.seats ∧
      (sourceBank ((menu).profile i) ((menu).seats i) pitch).Fits w (cursor i).floor ∧
      (∀j:Fin (slots entry.seats pitch),DateCode.history cpu m i ((menu).profile i+j.val)=
        ((packed entry.pin z pitch j.val).val:Word w)) ∧
      ∃(ext : DescentTerminalEpochBits.width entry.C ≤ (model).area.shapeAt.digit) (pick : (prior.placement.stage.result he).Choice),
        HEq choice pick ∧ ∀j,(wideCell entry.pin z (model).area.shapeAt.digit ext j).val =
          profileAt (inputNumber he prior.placement gid (GroupStage.plane (model).hostNumbers wide))
            ((scannedRows he prior.placement.stage).profile pick) j :=by
  let observed := profile_on_cpu X G S ordinary reset branch positive room shorten w fit board op frozen drift
      degree payload lo header initial protected_ beforeHeader lower z m original walk ticket before after located space
  let entry := observed.choose
  have seen := observed.choose_spec
  have ext : DescentTerminalEpochBits.width entry.C ≤ (model).area.shapeAt.digit :=by
    rw [show entry.C = G.C from seen.2.1]
    exact (shape_width ..).2.2.2
  refine ⟨entry,seen.1,seen.2.1,seen.2.2.1,seen.2.2.2.1,seen.2.2.2.2.1,
    seen.2.2.2.2.2.1,seen.2.2.2.2.2.2,ext,?_⟩
  exact registered_draw_pins X G S ordinary reset branch positive room shorten w fit z ticket
    before after located accepted (cursor i).ports op frozen drift degree payload
    ((menu).seats i) (cursor i).floor (menu).ordinary entry seen.1 wide ext

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
