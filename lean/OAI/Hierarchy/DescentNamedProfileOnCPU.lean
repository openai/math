import OAI.Hierarchy.DescentNamedProfiledAdmission
import OAI.Hierarchy.DescentRegisteredRetainedTape
import OAI.Hierarchy.DescentNamedShelfWidths

namespace OAI
/-! # Reading the selected immutable profile at its actual program cut -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option cleanup.letToHave false
open scoped Fin.CommRing
open StarKeys DescentStageEdgeReceipt
attribute [local irreducible] normalizedPackedChart SeedNamed.issued
open DescentCompiler DescentDatedAddressBook Chronology RegisterTimeline
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
private theorem readProfileCore {A F : Type} [Field F] {bn bd w k frozen p f g drift degree payload lo header idx mass i : ℕ}
    (G : PoweredGadget F) (S : AtomSchedule) (board : NonlinearExpanders.Graph bn bd) (op : RotorSpec)
    (entries : List (Source A)) {Cut : ℕ→Type*} (steps : ∀i,Cut i→Position→Move w→Prop)
    (initial : Position) (votes : A→Bool) (m : Memory w)
    (ok : ∀j, Protected (RegisterTimeline.date steps initial j) (RegisterTimeline.position steps initial j).floor header)
    (below : lo+extent (grain (payload/2) G.C) entries≤header) (lower : header < initial.floor)
    (space : (RegisterTimeline.position steps initial i).floor<2^w)
    (original : ∀a∈shelves (grain (payload/2) G.C) lo 0 entries,∀j:Fin (slots a.src.seats (grain (payload/2) G.C)),
      m (a.base+j.val)=((packed a.src.pin votes (grain (payload/2) G.C) j.val).val:Word w))
    (witness : ∃sl : DescentPackedEpochShelves.Shelf A, sl∈shelves (grain (payload/2) G.C) lo 0 entries ∧
      profileAt S (grain (payload/2) G.C) lo entries i=some sl ∧ entries[idx]?=some sl.src ∧ mass ≤ sl.src.seats)
    (widths : ∀v∈entries,v.C=G.C ∧ v.seats≤S.batch) :
    let menu:=fromProfiles G S board op k frozen p f g drift degree payload lo header entries
    let pitch:=grain (payload/2) G.C
    ∃e:Source A,entries[idx]?=some e ∧ e.C=G.C ∧ e.seats=menu.seats i ∧ e.seats≤S.batch ∧ mass≤e.seats ∧
      (sourceBank (menu.profile i) (menu.seats i) pitch).Fits w (RegisterTimeline.position steps initial i).floor ∧
      ∀j:Fin (slots e.seats pitch),DateCode.history (RegisterTimeline.date steps initial) m i (menu.profile i+j.val)=
        ((packed e.pin votes pitch j.val).val:Word w) := by
  obtain ⟨sl,listed,atRow,receipt,live⟩ := witness
  have chosen := fromProfiles_at G S board op k frozen p f g drift degree payload lo header entries i sl atRow
  have data := retained_tape steps initial header ok sl listed below lower space votes m (original sl listed)
  obtain ⟨width,cap⟩ := widths sl.src (List.mem_of_getElem? receipt)
  refine ⟨sl.src,receipt,width,chosen.2.1.symm,cap,live,?_,?_⟩
  · simpa only [chosen.1,chosen.2.1] using data.1
  · simpa only [chosen.1] using data.2

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


open Lean Elab Term in
local elab "applyProfileArguments% " f:term:arg "[" xs:term,* "]" : term => do
  let fn ← elabTerm f none
  return mkAppN fn (← xs.getElems.mapM fun x => elabTerm x none)

/-- The ballot encodes the complete original profile even at its first rejected row. -/
theorem profile_on_cpu (protected_ : ∀j,RegisterTimeline.Protected (cpu j) (cursor j).floor header)
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
    (space : (cursor i).floor<2^w) :
    ∃e:Source (ch).Pin,(ch).layout[before.selections.length]?=some e ∧
      e.C=G.C ∧ e.seats=(menu).seats i ∧ e.seats≤S.batch ∧
      Fintype.card (NativePair W.graph W.core (scanHomeAt nonneg prior.placement.stage)
        (scanColorAt nonneg prior.placement.stage) prior.placement.cap)≤e.seats ∧
      (sourceBank ((menu).profile i) ((menu).seats i) pitch).Fits w (cursor i).floor ∧
      ∀j:Fin (slots e.seats pitch),DateCode.history cpu m i ((menu).profile i+j.val)=
        ((packed e.pin votes pitch j.val).val:Word w):=by
  let selected := applyProfileArguments% (@registered_profile_exists) [
    F, (inferInstance : Field F), cp, nP, X, G, S, k, cut, tail, n, h, C, f, g, p,
    ordinary, reset, branch, positive, room, shorten, w, fit, payload, lo, c, W, i, z, D,
    z', D', rate, nonneg, prior, T, choice, norm, next, ticket, before, after, joined]
  let sizes := applyProfileArguments% (@normalized_shelf_widths) [
    F, (inferInstance : Field F), cp, nP, X, G, S, k, cut, tail, n, h, C, f, g, p,
    ordinary, reset, branch, positive, room, shorten, w, fit]
  let pairCount := Fintype.card (NativePair W.graph W.core (scanHomeAt nonneg prior.placement.stage)
    (scanColorAt nonneg prior.placement.stage) prior.placement.cap)
  exact applyProfileArguments% (@readProfileCore) [
    (ch).Pin, F, (inferInstance : Field F), n₀, δ, w, k, frozen, p, f, g, drift, degree, payload, lo,
    header, before.selections.length, pairCount, i, G, S, board, op, (ch).layout,
    (fun j => RunTrace.Events traces j), issue, initial, votes, m, protected_, beforeHeader, lower, space,
    original, selected, sizes]
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
