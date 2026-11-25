import OAI.Computability.BorderVNP.PackedFrozenSeedExecute
import OAI.Computability.BorderVNP.PackedFrozenNativePort
import OAI.Computability.BorderVNP.PackedInheritedWorkSeedBank

/-! # True terminal geometry, widths and immutable rows from the signed seed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Shortening.PreparedBins
open Packing.PhysicalEpochs
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {teams time pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {σ : Type} [Fintype σ] {g : ℕ} {len : Fin n} {state : Fin g}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K) (x : σ → Bool)

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "w" => 60*logWidth r n
local notation "mass" => initialMass (D:=D) n r d copies headerFactor
local notation "V" => CoverScale.sites (Cube D) (d+1)
local notation "extent" => copies*GridHosts.inputBlockWidth r n axes d
local notation "header" => WorkWords.grouped V extent
local notation "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation "cap" => seedBoxCapacity n r axes d (Fintype.card (Direction axes))
local notation "dB" => seedDescriptionWidth n r axes d (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)
local notation3 (prettyPrint := false) "geom" => (plan.execute G order position σ).choose.eval x
local notation3 (prettyPrint := false) "a₀" => Boundary.seedState S G d order position copies table geom
local notation3 (prettyPrint := false) "old₀" => Boundary.seedBirthPrograms S order position W tag sites edges ports table geom
local notation3 "fmt" => Boundary.seedFormat G order position copies
local notation3 "source" => plan.frozenStart G order position σ

/-- The same admissible physical leaf chosen by the geometry execution.
The new public record and width wires use precisely its geometry inputs. -/
noncomputable def frozenLeaf :
    Admissible (Boundary.Good (S:=S) (start:=d+1) («w»:=w) (shape:=boundaryShape S (d+1))
      (bits:=fun _ : Fin tiles => extent) (boundaryBudget S mass)) 0 :=
  ⟨a₀,((plan.execute G order position σ).choose_spec.2.2 W tag sites edges ports table x).choose⟩

local notation3 (prettyPrint := false) "seed₀" => plan.frozenLeaf G order position W tag sites edges ports table x

/-- Full expanded cap of the genuine seeded programs bounds the public-history
width loads, including all true copy slabs at the original tile. -/
theorem frozenLeaf_bankCap : SiteCap (a₀).route (old₀).bankFields true mass := by
  have expanded := ((plan.execute G order position σ).choose_spec.2.2 W tag sites edges ports table x).choose_spec.2.1
  exact Boundary.seedBirthPrograms_bankCap S order position W tag sites edges ports table geom dB expanded

/-- The schedule's actual grouped port rectangle uses the same tile numbers
as the physical seed, even when its cardinality proof casts the finite type. -/
theorem frozenLeaf_ports : (PortTable.mk _ key header).Widths (fun _ : Fin tiles => extent) w ∧
    (header).Reads (a₀).pack.layout (a₀).rows.site key := by
  have allKeys : ∀ i : Fin V, i ∈ Set.range key := fun i => (finCongr (seedPortCount (D:=D) d)).surjective i
  have reads := WorkWords.seed_header_reads S G order position table geom
  have fits := WorkWords.seed_widths S plan
  exact ⟨⟨fun _ => rfl,fun i hi => (hi (allKeys i)).elim,fun i => fits.fit ((finCongr (seedPortCount (D:=D) d)).symm i)⟩,
    ⟨fun a => reads.attach a,fun _ => rfl,fun i hi => (hi (allKeys i)).elim⟩⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
