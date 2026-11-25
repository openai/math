import OAI.Hierarchy.DescentDatedObservedProfile
import OAI.Hierarchy.DescentNamedRoutePrefix

namespace OAI
/-! # The original profile for every accepted step and every predecessor of the first failure -/
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


open DescentKernelHistory.BitDescription DescentStageEdgeReceipt DescentPacking.PackedMatch.Local
open DescentPackedProfileWide DescentPackedProfileWindow DescentTerminalEpochBits
open StarKeys
open scoped Classical Fin.CommRing
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)
local notation "rr" => normalizedRoute X G S ordinary reset branch positive room shorten w fit
variable (z : (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin→Bool)
local notation "walk" => (rr).follow z
local notation "path" => (issued X G S ordinary reset branch positive room shorten walk).path
set_option maxHeartbeats 1200000 in
theorem observed_profile_pins {W : MarkedWorld F 0 pins widths}
    {i grain D z' D' : ℕ} {rate : ℝ} {nonneg : 0 ≤ fee}
    {prior : Reached W G price fee S k i grain D (S.epochPower^S.priceExponent) s} {T : StageInput W G rate fee}
    {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' (S.epochPower^S.priceExponent) s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path (trace walk).origin.source prior) (after : Path next (trace walk).target)
    (cut : (before.ordinary ticket).append after=(trace walk).path)
    (entry : Source (ch).Pin) (header : (ch).layout[before.selections.length]?=some entry)
    (go : before.selections.length+1< ((ch).rows z).length ∨ (ch).read z=some walk)
    {H : ℕ} (host : prior.V↪Fin H) (wide : Fintype.card prior.V≤ H)
    (physical : ∀x,(host x).val=(prior.vertex x).val)
    (digit : ℕ) (ext : DescentTerminalEpochBits.width entry.C≤ digit) :
    ∃actual : (prior.placement.stage.result nonneg).Choice, HEq choice actual ∧
      ∀q,(wideCell entry.pin z digit ext q).val=
        profileAt (inputNumber nonneg prior.placement (Equiv.refl _).toEmbedding host)
          ((scannedRows nonneg prior.placement.stage).profile actual) q :=by
  have located:=ticket.input_at_cut before after cut
  let physicalProfile := OrdinaryLink.padded_profile (source := prior) ticket host wide physical
  refine ⟨physicalProfile.choose,physicalProfile.choose_spec.1,?_⟩
  have read : ∀q,(wideCell entry.pin z digit ext q).val=issuedProfile G ⟨ticket.selection,ticket.inputPair⟩ q:=by
    rcases go with past|accepted
    · exact previous_profile X G S ordinary reset branch positive room shorten w fit z
        (before.selections.length+1) past (Nat.lt_succ_self _) entry header _ located digit ext
    · have all:=packedChart_fields X G S ordinary reset branch positive room shorten w fit z walk accepted
      have at_:=congrArg (fun xs : List (ℕ→ℕ)=>xs[before.selections.length]?) all
      simp only [List.getElem?_map,header,located,Option.map_some,Option.some.injEq] at at_
      intro q
      rw [cell_eq,cell_read]
      exact congrFun at_ q
  exact fun q=>(read q).trans (physicalProfile.choose_spec.2 q)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
