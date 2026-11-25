import OAI.Computability.BorderVNP.PackedInheritedWorkBottomPrepSeed
import OAI.Computability.BorderVNP.PackedBankProgramCapacity

/-! # Charging the physical work compiler's actual wired-verifier birth programs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.DeckGrid Packing.Inherited Packing.PhysicalEpochs Packing.Inherited.WorkWords
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire
open VPVNP VPVNP.ParseGrammar SelectedSchedule Shortening.PreparedBins
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {n r d copies : ℕ} {teams time pins link inner : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring teams r time pins link inner n Edge}
variable (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {g : ℕ} {len : Fin n} {state : Fin g} (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np) (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K)
variable (words : Pins S (d+1) (boundary S (d+1)) (60*TeamScales.logWidth r n) 0 → Bool)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "degree" => Fintype.card (Direction axes)
local notation "a" => seedState S G d order position copies table words
local notation "pr" => seedBirthPrograms S order position W tag sites edges ports table words

/-- The actual persistent birth programs fit their expanded field account. A public
descriptor uses at most the full stored syntax and its private work uses at most
the expanded payload of the very same routed seed. -/
theorem seedBirthPrograms_bankCap (dB : ℕ)
    (hcap : SiteCap (a).route (seedBirthFields W position tag sites edges ports copies dB true) true
      (baseMass degree (seedBoxCapacity n r axes d degree) (seedChannelWidth n r axes d) copies dB)) :
    SiteCap (a).route (pr).bankFields true
      (baseMass degree (seedBoxCapacity n r axes d degree) (seedChannelWidth n r axes d) copies dB) := by
  let fields := seedBirthFields W position tag sites edges ports copies dB
  intro tile
  have physical := bankRecords_le (a).pack.layout pr (fields true) true
    (fun v => ⟨(pr v).program.publicNodes_le_staticNodes,Nat.le_add_right _ _⟩)
    (fun v => reduceMove (depth S (d+1) 0) ((a).route.origin v) = tile)
  exact (Nat.add_le_add_left physical 1).trans (hcap tile)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
