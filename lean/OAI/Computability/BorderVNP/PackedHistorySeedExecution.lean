import OAI.Computability.BorderVNP.PackedHistorySeedPlan
import OAI.Computability.BorderVNP.PackedHistoryNormalizedGridBirth
import OAI.Computability.BorderVNP.PackedHistoryNormalizedProfile

/-! # Accepted physical histories of the actual repeated verifier grid -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Shortening.Adaptive BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing Packing.PhysicalEpochs
open Packing.DeckGrid Diagonal Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire
open VPVNP VPVNP.ParseGrammar VPVNP.VerifierNetwork EnrichedOuter TeamScales
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {teams t pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring teams r t pins link inner n Edge)

local notation "axes" => Fintype.card (Cube D)
local notation "degree" => Fintype.card (Direction axes)
local notation "W" => 60*logWidth r n
local notation "tileWidth" => GridHosts.inputBlockWidth r n axes d
local notation "mass" => initialMass (D:=D) n r d copies headerFactor
local notation "budget" => boundaryBudget S mass
local notation "cap" => seedBoxCapacity n r axes d degree
local notation "dB" => seedDescriptionWidth n r axes d (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)
local notation "outerPins" => Boundary.Pins S (d+1) (boundaryShape S (d+1)) W
local notation "proc" => Compiled.machine (SeedPlan.compiled plan)

variable (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (σ : Type) [Fintype σ]

set_option maxHeartbeats 1200000 in
/-- A single seed initializer and a single sparse history circuit work
simultaneously for every private verifier, row assignment and coefficient
table. Their accepted profile words are in bijection with the genuine
physical branches, with exactly the assigned terminal words and tensor sum. -/
theorem execute :
    ∃ f : Frame σ (outerPins 0), f.size≤2 ∧
      ((Q*(compile (proc).steps T le_rfl (repeatLeaf (fan S) f T)).size+
        Fintype.card (Slot (fan S) (Machine.Guess S (d+1) (fun _ _ => W)) T) : ℕ) : ℝ) < r*(n:ℝ)^(92/100:ℝ) ∧
      ∀ {g : ℕ} {len : Fin n} {state : Fin g} (privateInput : WiredWitness G len D axes d order state)
        (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
        (siteID : (privateInput.routedFine position).Site ↪ Fin ns)
        (edgeID : (privateInput.routedFine position).Edge ↪ Fin ne) (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np)
        (table : (seedBundle G axes d order position copies).Tables K) (x : σ → Bool),
        let a := Boundary.seedState S G d order position copies table (f.eval x)
        let fields := Boundary.seedBirthFields privateInput position tag siteID edgeID portID copies dB
        ∃ h : Boundary.Good budget 0 a,
          let leaf : Admissible (Boundary.Good (S:=S) (start:=d+1) (w:=W) (shape:=boundaryShape S (d+1))
              (bits:=fun _ : Fin (GridHosts.tileCount axes d) => copies*tileWidth) budget) 0 := ⟨a,h⟩
          let history := packHistory leaf (proc).epoch T
          SiteCap a.route (fields false) false (seedPublicBase degree) ∧ SiteCap a.route (fields true) true mass ∧
          (∃ code : history.Index ≃ {y : Slot (fan S) (Machine.Guess S (d+1) (fun _ _ => W)) T → Bool //
              flag (proc).steps T le_rfl (repeatLeaf (fan S) f T) x y = true},
            ∀ q, output (proc).steps T le_rfl (repeatLeaf (fan S) f T) x (code q).val = (history.term q).val.words) ∧
          ∀ y, (parallelPacks (fun _ : Fin ((fan S)^T) => a.pack)).tensor y =
            ∑ q, (flattenPack T (history.term q).val.pack).tensor y := by
  have hmass : mass ≤ 1+budget 0 := by rw [boundary_zero]; omega
  obtain ⟨f,cost,prepare⟩ := Boundary.exists_seed_birth_frame (d:=d) (G:=G) (order:=order) (w:=W)
    S position copies dB σ plan.fits plan.small budget hmass
  refine ⟨f,cost,plan.within f cost,?_⟩
  intro g len state privateInput tag ns ne np siteID edgeID portID table x a fields
  obtain ⟨ready,sparse,expanded⟩ := prepare privateInput tag siteID edgeID portID table x
  refine ⟨ready,?_⟩
  intro leaf history
  have initial : f.eval x = leaf.val.words := rfl
  let rep := Machine.represents (good := Boundary.Good (S:=S) (start:=d+1) (w:=W) (shape:=boundaryShape S (d+1))
    (bits:=fun _ : Fin (GridHosts.tileCount axes d) => copies*tileWidth) budget)
  let code := acceptedOuterBounded (proc).epoch (fun _ _ => True) (proc).closed ⟨leaf,trivial⟩ (proc).profileCodec
    rep (proc).steps (proc).profileCorrect f x initial
  refine ⟨sparse,expanded,⟨code,?_⟩,fun y => (proc).repeated_tensor leaf T le_rfl y⟩
  intro q
  exact acceptedOuterBounded_state (proc).epoch (fun _ _ => True) (proc).closed ⟨leaf,trivial⟩ (proc).profileCodec
    rep (proc).steps (proc).profileCorrect f x initial q

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
