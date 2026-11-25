import OAI.Hierarchy.DescentNamedNormalizedChart
import OAI.Hierarchy.DescentRankedSeatList

namespace OAI
/-! # The actual occupied profile seats at a cut of the named chronology -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentStageEdgeReceipt DescentPacking DescentTerminalEpochDecoder StarKeys
noncomputable section
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {dim k : ℕ}
    {bits : P→ℕ} {q ε : ℝ} {W₀ W₁ W₂ : MarkedWorld F dim P bits}
    {i₀ z₀ D₀ i z D i₂ z₂ D₂ wire hist : ℕ}
    {first : Reached W₀ G q ε S k i₀ z₀ D₀ wire hist} {middle : Reached W₁ G q ε S k i z D wire hist}
    {last : Reached W₂ G q ε S k i₂ z₂ D₂ wire hist}

theorem Path.inputRanked_length (p : Path first middle) :
    p.inputRanked.length=p.selections.length := by
  induction p with
  | here => rfl
  | ordinary prev ticket ih =>
    change (prev.inputRanked ++ [_]).length = (prev.selections ++ [_]).length
    simp only [List.length_append,List.length_singleton,ih]
  | reset prev bank ih => exact ih

variable {rate : ℝ} {he : 0≤ε} {T : StageInput W₁ G rate ε} {choice : (T.result he).Choice}
    {norm : Normalize ((T.result he).state choice)} {z' D' : ℕ}
    {target : Reached norm.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink middle he T choice norm target)

theorem OrdinaryLink.input_at_cut (before : Path first middle) (after : Path target last) {path : Path first last}
    (cut : (before.ordinary ticket).append after=path) :
    path.inputRanked[before.selections.length]?=some ⟨ticket.selection,ticket.inputPair⟩ := by
  rw [←cut,Path.inputRanked_append,←before.inputRanked_length]
  change ((before.inputRanked++[_])++after.inputRanked)[before.inputRanked.length]?=_
  rw [List.append_assoc,List.getElem?_append_right le_rfl,Nat.sub_self]
  rfl

set_option maxHeartbeats 1200000 in
/-- Both the selected coefficient and its actual native pair cardinality survive the
transport from the chronological ticket to the physical old layout. -/
theorem OrdinaryLink.placed_choice :
    ∃actual : (middle.placement.stage.result he).Choice, HEq choice actual ∧
      Fintype.card (NativePair W₁.graph W₁.core (scanHomeAt he middle.placement.stage)
        (scanColorAt he middle.placement.stage) middle.placement.cap)=selectionCount G ticket.selection := by
  obtain rfl:=ticket.sourceRate
  obtain rfl:=eq_of_heq ticket.placement
  exact ⟨choice,HEq.rfl,rfl⟩

end
end Hierarchy.DescentSixParty.Chronology

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
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

/-- Each original chart header bounds the input order of the genuine selected history,
including the first row at which an externally supplied coefficient is rejected. -/
theorem issued_seat_at (c : (last).Choice) (i : ℕ) (entry : Source (ch).Pin)
    (v : RankedSelection F _ _ _ G _) (selected : (ch).layout[i]?=some entry)
    (entered : (trace c).path.inputRanked[i]?=some v) : selectionCount G v.1 ≤ entry.seats := by
  rw [issued_inputRanked] at entered
  exact epochs_seat_at G _ _ run order (seedChart X S.copies s w fit) rfl c i v entry entered selected

open StarKeys DescentStageEdgeReceipt
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

set_option maxHeartbeats 1600000 in
theorem issued_profile_seats (c : (last).Choice) {W : MarkedWorld F 0 pins widths}
    {i z D z' D' : ℕ} {rate : ℝ} {nonneg : 0 ≤ fee}
    {prior : Reached W G price fee S k i z D (S.epochPower^S.priceExponent) s} {T : StageInput W G rate fee}
    {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' (S.epochPower^S.priceExponent) s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path (trace c).origin.source prior) (after : Path next (trace c).target)
    (cut : (before.ordinary ticket).append after=(trace c).path)
    (entry : Source (ch).Pin) (header : (ch).layout[before.selections.length]?=some entry) :
    ∃actual : (prior.placement.stage.result nonneg).Choice, HEq choice actual ∧
      Fintype.card (NativePair W.graph W.core (scanHomeAt nonneg prior.placement.stage)
        (scanColorAt nonneg prior.placement.stage) prior.placement.cap) ≤ entry.seats := by
  have placed := @OrdinaryLink.placed_choice F pins _ G S 0 k widths price fee W i z D
    (S.epochPower^S.priceExponent) s prior rate nonneg T choice norm z' D' next ticket
  obtain ⟨actual,same,size⟩ := placed
  exact ⟨actual,same,size.le.trans (issued_seat_at X G S ordinary reset branch positive room shorten w fit
    c _ entry _ header (ticket.input_at_cut before after cut))⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
