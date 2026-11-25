import OAI.Computability.BorderVNP.PackedFrozenSeedInitial
import OAI.Computability.BorderVNP.PackedInheritedWorkBottomPrepSeed

/-! # Readback of the augmented initial public frame on the private grouped grid -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace
open TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar SelectedSchedule TeamScales
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2600000
set_option maxRecDepth 7500

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {teams time pins link inner : ℕ} {Edge : Type} (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "w" => 60*logWidth r n
local notation "B" => boundary S (d+1)
local notation "O" => Pins S (d+1) B w 0
local notation "cap" => seedBoxCapacity n r axes d (Fintype.card (Direction axes))
local notation3 "channels" => (groupedGridRows G axes d order position copies).edge
local notation3 "groups" => (Equiv.refl (Fin tiles)).toEmbedding
local notation3 "rs₀" => FrozenTape.Seed.rows n r order position channels groups copies
local notation3 "key₀" => order.symm.toEmbedding.trans (Fin.castLEEmb plan.fits)

variable {σ : Type} [Fintype σ] (base : Frame σ (Pins S (d+1) (boundary S (d+1)) (60*logWidth r n) 0))
local notation3 "fmt" => seedFormat G order position copies

variable [Fintype Edge] {g : ℕ} {len : Fin n} {state : Fin g} (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np) (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K)

/-- On one and the same true initial state, the two work-width columns and
the entire opaque-box reference directory are exactly the installed private
programs' widths and chronological records. -/
theorem seedTapeFrame_reads (x : σ → Bool) (budget : ℕ → ℕ)
    (good : Good budget 0 (seedState S G d order position copies table (base.eval x)))
    (room : copies*(2*cap) < 2^w) (scalar : FrozenTape.Seed.scalarCap n r axes d copies < 2^w) :
    let a := seedState S G d order position copies table (base.eval x)
    let programs := seedBirthPrograms S order position W tag sites edges ports table (base.eval x)
    let publicBits := (seedTapeFrame S plan G order position base).eval x
    WidthReads a programs (publicBits ∘ Sum.inl) ∧
      (fmt).schema.Image (publicBits ∘ Sum.inr) (a.rows.site.trans Fin.valEmbedding)
        (fun v => (programs v).program) := by
  intro a programs publicBits
  have reads := seedWidthFrame_reads S plan base order position W tag sites edges ports table x budget good room
  have geom : publicBits ∘ Sum.inl = (seedWidthFrame S plan base).eval x := by
    funext j
    exact parallelFrame_eval_inl ..
  have tape : publicBits ∘ Sum.inr = (Bottom.frame rs₀ 0 w key₀).eval x := by
    funext j
    exact parallelFrame_eval_inr ..
  refine ⟨(congrArg (WidthReads a programs) geom).mpr reads.1,?_⟩
  have ids : a.rows.site.trans Fin.valEmbedding = (key₀).trans Fin.valEmbedding := by
    apply DFunLike.ext
    intro v
    have idAt := (seedState_rows S G d order position copies table (base.eval x)).1 (order.symm v)
    change (a.rows.site (order (order.symm v))).val = (order.symm v).val at idAt
    change (a.rows.site v).val = (order.symm v).val
    exact (congrArg (fun u => (a.rows.site u).val) (order.apply_symm_apply v)).symm.trans idAt
  have exactTape := W.seedBorn_frozen_image_at_width position tag sites edges ports channels groups copies key₀ 0 x scalar
  let sitesAt := fun v => (programs v).program
  exact (congrArg (fun z => (fmt).schema.Image z (a.rows.site.trans Fin.valEmbedding) sitesAt) tape).mpr
    ((congrArg (fun id => (fmt).schema.Image ((Bottom.frame rs₀ 0 w key₀).eval x) id sitesAt) ids).mpr exactTape)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
