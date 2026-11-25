import OAI.Computability.BorderVNP.PackedInheritedWorkBottomPrepSeed

/-! # A public width initializer shared by all private wired witnesses -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.DeckGrid Packing.PhysicalEpochs Packing.Inherited Packing.Inherited.WorkWords Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport
open Shortening.PreparedBins TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar SelectedSchedule
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1200000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {teams time pins link inner : ℕ} {Edge : Type} [Fintype Edge] {G : Wiring teams r time pins link inner n Edge}

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "w" => 60*TeamScales.logWidth r n
local notation "B" => boundary S (d+1)
local notation "O" => Pins S (d+1) B w 0
local notation "cap" => seedBoxCapacity n r axes d (Fintype.card (Direction axes))
local notation "mass" => initialMass (D:=D) n r d copies headerFactor
local notation "dB" => seedDescriptionWidth n r axes d (headerFactor*TeamScales.logWidth r n) (BottomGridBank.bodyBudget cap)
local notation "extent" => copies*GridHosts.inputBlockWidth r n axes d
local notation "header" => WorkWords.grouped tiles extent

variable {σ : Type} [Fintype σ] (base : Frame σ (Pins S (d+1) (boundary S (d+1)) (60*TeamScales.logWidth r n) 0))

/-- Pre-evaluate the actual joint public seed circuit on its fixed all-zero input. Every
published output wire selects one of two constants. Only the public frame is used to choose
these wires, before the private factor lists and field tables are supplied. -/
noncomputable def staticSeedWidthFrame : Frame σ (OuterWidthPins S (d+1) B w 0) :=
  (constants σ).select (Sum.inr ∘ (seedWidthFrame S plan base).eval (fun _ => false))

theorem staticSeedWidthFrame_size : (staticSeedWidthFrame S plan base).size ≤ 2 := by
  simpa only [staticSeedWidthFrame,Frame.select_size] using constants_size σ

/-- Every literal is the corresponding output bit of the public width computation. -/
theorem staticSeedWidthFrame_eval (x : σ → Bool) : (staticSeedWidthFrame S plan base).eval x =
    (seedWidthFrame S plan base).eval (fun _ => false) := by
  funext j
  simp [staticSeedWidthFrame,constants_eval]

omit [NeZero D] in
/-- The actual total record budget for the seed pays both its work and incidence slab. -/
theorem seedBirth_room_of_mass (room : mass < 2^w) : copies*(2*cap) < 2^w := by
  apply lt_of_le_of_lt _ room
  change copies*(2*cap) ≤ baseMass _ cap _ copies dB
  unfold baseMass
  exact (Nat.mul_le_mul_left copies (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))).trans
    (Nat.le_add_left _ _)

variable (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- Choose the shared physical seed before the private witnesses. For each private verifier
the original computed geometry is admissible, the two width words match its native birth
lineages, and the grouped port rows read the correct attachment and width. -/
theorem exists_seedWidth_frame (σ : Type) [Fintype σ] (room : mass < 2^w) :
    ∃ base : Frame σ O, base.size ≤ 2 ∧
    ∀ {g : ℕ} {len : Fin n} {state : Fin g} (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
      (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
      (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
      (ports : Fin r × Fin (publicWidth G) ↪ Fin np) (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K)
      (x : σ → Bool), let a := seedState S G d order position copies table (base.eval x)
      Good (boundaryBudget S mass) 0 a ∧
      WidthReads a (seedBirthPrograms S order position W tag sites edges ports table (base.eval x))
        ((seedWidthFrame S plan base).eval x) ∧ (header).Reads a.pack.layout a.rows.site (Function.Embedding.refl _) ∧
      let fields := seedBirthFields W position tag sites edges ports copies dB
      SiteCap a.route (fields false) false (seedPublicBase (Fintype.card (DeckGrid.Direction axes))) ∧
        SiteCap a.route (fields true) true mass := by
  have cap₀ : mass ≤ 1+boundaryBudget S mass 0 := by rw [boundary_zero]; omega
  obtain ⟨f,hf,h⟩ := exists_seed_birth_frame (d := d) (G := G) (order := order) («w» := w)
    S position copies dB σ plan.fits plan.small (boundaryBudget S mass) cap₀
  refine ⟨f,hf,?_⟩
  intro g len state W tag ns ne np sites edges ports table x a
  have good := (h W tag sites edges ports table x).1
  have read := seedWidthFrame_reads S plan f order position W tag sites edges ports table x (boundaryBudget S mass)
    good (seedBirth_room_of_mass (D := D) room)
  exact ⟨good,read.1,read.2,(h W tag sites edges ports table x).2⟩

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
