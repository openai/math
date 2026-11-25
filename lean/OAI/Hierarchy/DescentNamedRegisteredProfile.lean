import OAI.Hierarchy.DescentNamedSelectorCapture
import OAI.Hierarchy.DescentNamedProfileNumber

namespace OAI
/-! # The actual ballot header and stored shelf selected by the date menu -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option Elab.async false
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
variable (w : ℕ) (fit : (S.firstWidth G.b p) < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

open StarKeys DescentStageEdgeReceipt
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

theorem registered_profile_exists (payload lo : ℕ) (c : (last).Choice) {W : MarkedWorld F 0 pins widths}
    {i z D z' D' : ℕ} {rate : ℝ} {nonneg : 0 ≤ fee}
    {prior : Reached W G price fee S k i z D (S.epochPower^S.priceExponent) s} {T : StageInput W G rate fee}
    {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' (S.epochPower^S.priceExponent) s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path (trace c).origin.source prior) (after : Path next (trace c).target)
    (cut : (before.ordinary ticket).append after=(trace c).path)
 :
    ∃sl : DescentPackedEpochShelves.Shelf (ch).Pin,
      sl∈DescentPackedEpochShelves.shelves (DescentPackedEpochShelves.grain (payload/2) G.C) lo 0 (ch).layout ∧
      RegisterTimeline.profileAt S (DescentPackedEpochShelves.grain (payload/2) G.C) lo (ch).layout i=some sl ∧
      (ch).layout[before.selections.length]?=some sl.src ∧
      Fintype.card (NativePair W.graph W.core (scanHomeAt nonneg prior.placement.stage)
        (scanColorAt nonneg prior.placement.stage) prior.placement.cap)≤ sl.src.seats :=by
  let n:=RegisterTimeline.rowNumber S i
  let pitch:=DescentPackedEpochShelves.grain (payload/2) G.C
  let ls:=DescentPackedEpochShelves.shelves pitch lo 0 (ch).layout
  have cutRows := Branch.profile_number X G S (trace c) ticket before after cut
  have size : ls.length=(ch).layout.length:=by
    simpa only [List.length_map] using congrArg List.length (DescentPackedEpochShelves.sources pitch lo 0 (ch).layout)
  have inside : n<ls.length := cutRows.2.trans_eq
    ((scheduled_capture_length X G S ordinary reset branch positive room shorten w fit).trans size.symm)
  let sl:=ls[n]
  have hit : RegisterTimeline.profileAt S pitch lo (ch).layout i=some sl:=List.getElem?_eq_getElem inside
  have entry:=RegisterTimeline.profileAt_entry S sl hit
  have rowAt := (congrArg (fun j => (ch).layout[j]?) cutRows.1).symm.trans entry
  have evidence := issued_profile_seats X G S ordinary reset branch positive room shorten w fit c
    (W:=W) (i:=i) (z:=z) (D:=D) (z':=z') (D':=D') (rate:=rate) (nonneg:=nonneg)
    (prior:=prior) (T:=T) (choice:=choice) (norm:=norm) (next:=next)
    ticket before after cut sl.src rowAt
  have occupied := evidence.choose_spec.2
  exact ⟨sl,List.getElem_mem ..,hit,rowAt,occupied⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
