import OAI.Computability.BorderVNP.PackedFrozenSeedFrame
import OAI.Computability.BorderVNP.PackedInheritedWorkBottomPrepPlan
import OAI.Computability.BorderVNP.PackedHistorySeedExecution

/-! # The augmented initializer of the actual accepted grouped-grid execution -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape Diagonal.ExternalSew
open TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar EnrichedOuter TeamScales
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2400000
set_option maxRecDepth 7500

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {teams time pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (σ : Type) [Fintype σ]

local notation "axes" => Fintype.card (Cube D)
local notation "w" => 60*logWidth r n
local notation "B" => boundary S (d+1)
local notation "mass" => initialMass (D:=D) n r d copies headerFactor
local notation "cap" => seedBoxCapacity n r axes d (Fintype.card (Direction axes))
local notation "dB" => seedDescriptionWidth n r axes d (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)
local notation3 "fmt" => Boundary.seedFormat G order position copies
local notation3 (prettyPrint := false) "geometric" => (plan.execute G order position σ).choose

omit [NeZero D] in
/-- Every scalar printed in the literal seed rows fits the same initial mass
used by the actual execution, including copies when a work range is empty. -/
theorem seedScalar_le_mass :
    FrozenTape.Seed.scalarCap n r axes d copies ≤ mass := by
  have body : 0 < BottomGridBank.bodyBudget cap := by unfold BottomGridBank.bodyBudget; positivity
  have desc : 0 < dB := by unfold seedDescriptionWidth; omega
  let H := seedChannelWidth n r axes d
  let degree := Fintype.card (Direction axes)
  have one : 1 ≤ 2*cap+dB+(2*degree+1)*H := by omega
  have b := Nat.mul_le_mul_left copies one
  rw [Nat.mul_one] at b
  have twos := Nat.mul_le_mul_left copies (show 2*cap ≤ 2*cap+dB+(2*degree+1)*H by omega)
  unfold FrozenTape.Seed.scalarCap initialMass baseMass
  change max 2 (max copies (max cap (2*copies*cap))) ≤
    seedPublicBase degree+12+810487*cap+copies*(2*cap+dB+(2*degree+1)*H)
  rw [show 2*copies*cap = copies*(2*cap) by ring]
  omega

/-- One public augmented leaf, selected from the same geometry witness used
by the accepted history machine and shared by all private factor tables. -/
noncomputable def frozenStart : Frame σ (ProgramSchemas.outerPins S (d+1) w fmt 0) :=
  Boundary.seedTapeFrame S plan G order position geometric

/-- Its gate charge includes the initial true work, extent and row records. -/
theorem frozenStart_cost (edgeFit : (B 0).edges ≤ 2^w) (hL : 1 ≤ logWidth r n) :
    (plan.frozenStart G order position σ).size+1 ≤ rowWork (5+64000*66^3) (CoverScale.sites (Cube D) (d+1))
      (logWidth r n) 3 (bottom (D:=D) (d+1)) :=
  Boundary.seedTapeFrame_rowWork S plan G order position geometric
    (plan.execute G order position σ).choose_spec.1 edgeFit hL

/-- Simultaneous readback for every private verifier on this single public
leaf. The seed budget already pays for every scalar and every work bit. -/
theorem frozenStart_reads (room : mass < 2^w) {g : ℕ} {len : Fin n} {state : Fin g}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order state) (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np) (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K)
    (x : σ → Bool) :
    let a := Boundary.seedState S G d order position copies table ((geometric).eval x)
    let programs := Boundary.seedBirthPrograms S order position W tag sites edges ports table ((geometric).eval x)
    let words := (plan.frozenStart G order position σ).eval x
    Boundary.Good (boundaryBudget S mass) 0 a ∧ Boundary.WidthReads a programs (words ∘ Sum.inl) ∧
      (fmt).schema.Image (words ∘ Sum.inr) (a.rows.site.trans Fin.valEmbedding) (fun v => (programs v).program) := by
  intro a programs words
  obtain ⟨good,_⟩ := (plan.execute G order position σ).choose_spec.2.2 W tag sites edges ports table x
  refine ⟨good,?_⟩
  exact Boundary.seedTapeFrame_reads S plan G order position geometric W tag sites edges ports table x
    (boundaryBudget S mass) good (Boundary.seedBirth_room_of_mass room) ((seedScalar_le_mass (D:=D)).trans_lt room)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
