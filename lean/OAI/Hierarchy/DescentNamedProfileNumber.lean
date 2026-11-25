import OAI.Hierarchy.DescentRegisteredProfileMenu
import OAI.Hierarchy.DescentNamedProfileSeatFit

namespace OAI
/-! # Original selector row at a physical date -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
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
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height



private theorem profileAtCut (first rest sequence_ : List Bool) (age : ℕ)
    (cutKinds : sequence_ = first ++ false :: rest) (atAge : first.length = age) :
    (countDates 0 (sequence_.take age)).length = (countDates 0 first).length ∧
    (countDates 0 (sequence_.take age)).length < (countDates 0 sequence_).length := by
  subst sequence_
  subst age
  rw [List.take_left]
  refine ⟨rfl, ?_⟩
  rw [countDates_append]
  simp [countDates]

include before tail cut in
theorem profile_number :
    RegisterTimeline.rowNumber S i=before.selections.length ∧
      RegisterTimeline.rowNumber S i<(countDates 0 (kindCalendar S.rounds S.height)).length :=by
  have span : before.kinds.length=i:=by have t:=before.kinds_length;omega
  have kinds : kindCalendar S.rounds S.height=before.kinds++(false::tail.kinds) :=by
    exact br.kinds.symm.trans ((congrArg Path.kinds cut).symm.trans
      (((Path.ordinary before ticket).kinds_append tail).trans (by
        change (before.kinds ++ [false]) ++ tail.kinds = _
        rw [List.append_assoc]
        rfl)))
  have atCut := profileAtCut before.kinds tail.kinds _ i kinds span
  exact ⟨atCut.1.trans before.countDates_length, atCut.2⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
