import OAI.Computability.BorderVNP.PackedHistoryNormalizedGrid
import OAI.Computability.BorderVNP.PackedSeedBaseCaps

/-! # The wired verifier's physical birth records at the compiled grid boundary -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Packing Packing.PhysicalEpochs Packing.DeckGrid
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction Shortening.PreparedBins
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open VPVNP.VerifierNetwork (Frame)
open scoped Classical
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {R r t pins link inner n g d : ℕ} {Edge : Type} [Fintype Edge] {G : Wiring R r t pins link inner n Edge}
    {len : Fin n} {state : Fin g}
    {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {ns ne np : ℕ} (siteID : (W.routedFine position).Site ↪ Fin ns)
    (edgeID : (W.routedFine position).Edge ↪ Fin ne) (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np)
    (copies dB : ℕ) {w : ℕ}

local notation "axes" => Fintype.card (Cube D)
local notation "N" => seedBundle G axes d order position copies
local notation "O" => Pins S (d+1) (SelectedSchedule.boundary S (d+1)) w
local notation "degree" => Fintype.card (Direction axes)
local notation "H" => seedChannelWidth n r axes d
local notation "cap" => seedBoxCapacity n r axes d degree
local notation "expanded" => baseMass degree cap H copies dB

/-- The actual birth fields, with the grouped grid's channel row numbers and block ordinals. -/
noncomputable def seedBirthFields : Bool → RecordData N :=
  W.seedFields position code siteID edgeID portID (groupedGridRows G axes d order position copies).edge
    (Equiv.refl _).toEmbedding copies dB

set_option maxHeartbeats 1500000 in
/-- Install the true wired verifier's grouped seed and its sparse and expanded physical
birth fields. The same two-gate frame works for every private witness, descriptor
code, fine row numbering, factor table and input. -/
theorem exists_seed_birth_frame (σ : Type) [Fintype σ] (fit : GridHosts.tileCount axes d ≤ 2^w)
    (small : copies*H < 2^w) (budget : ℕ → ℕ) (mass : expanded ≤ 1+budget 0) :
    ∃ base : Frame σ (O 0), base.size ≤ 2 ∧
    ∀ {g : ℕ} {len : Fin n} {state : Fin g} (W : WiredWitness G len D axes d order state)
      (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
      {ns ne np : ℕ} (siteID : (W.routedFine position).Site ↪ Fin ns)
      (edgeID : (W.routedFine position).Edge ↪ Fin ne) (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np)
      (table : (N).Tables K) (x : σ → Bool),
      let fields := seedBirthFields W position code siteID edgeID portID copies dB
      let bottom := seedState S G d order position copies table (base.eval x)
      Good budget 0 bottom ∧ SiteCap bottom.route (fields false) false (seedPublicBase degree) ∧
        SiteCap bottom.route (fields true) true expanded := by
  let channels := (groupedGridRows G axes d order position copies).edge
  let groups := (Equiv.refl (Fin (GridHosts.tileCount axes d))).toEmbedding
  obtain ⟨base,cost,ready⟩ := exists_seed_frame S G d order position copies σ fit small
  refine ⟨base,cost,?_⟩
  intro g len state W code ns ne np siteID edgeID portID table x fields bottom
  constructor
  · apply ready table x budget (fields true).prior (fields true).payload
    intro v
    have h := (W.seedFields_cell position code siteID edgeID portID channels groups copies dB v).2.trans mass
    exact (seed_localRecords G axes d order position copies true (fields true).prior (fields true).payload v).ge.trans
      (Nat.le_of_add_le_add_left h)
  · let native := seedRoutes S G d order position copies table
    let coord := GridShape.coordinate (d := d+1) (factorEnum D).symm
    let ht := W.seedFields_siteCap position code siteID edgeID portID channels groups copies dB table native coord
      (seed_origin S G d order position copies table)
    let tested (f : Fintype (Fin (GridHosts.tileCount axes d))) :=
      @SiteCap D K _ _ f _ _ _ _ bottom.pack bottom.route (fields false) false (seedPublicBase degree) ∧
      @SiteCap D K _ _ f _ _ _ _ bottom.pack bottom.route (fields true) true expanded
    exact (congrArg tested (Subsingleton.elim (portFintype (k := fan S) (P := Fin (GridHosts.tileCount axes d)) (b := 0))
      (Fin.fintype (GridHosts.tileCount axes d)))).mpr ht

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
