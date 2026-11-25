import OAI.Computability.BorderVNP.PackedInheritedWorkSeedFrame
import OAI.Computability.BorderVNP.PackedHistoryNormalizedGridBirth

/-! # Width words of the true routed verifier at the grouped seed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.WorkWords Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace
open Shortening.PreparedBins TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar SelectedSchedule
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
open private endPin seedFit from OAI.Computability.BorderVNP.PackedInheritedWorkSeedFrame
set_option maxHeartbeats 500000
set_option maxRecDepth 3000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {teams time pins link inner : ℕ} {Edge : Type} {G : Wiring teams r time pins link inner n Edge}

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "w" => 60*TeamScales.logWidth r n
local notation "B" => boundary S (d+1)
local notation "O" => Pins S (d+1) B w 0
local notation "size₀" => seedSiteCapacity n r axes d
local notation "cap" => seedBoxCapacity n r axes d (Fintype.card (Direction axes))
local notation "extent" => copies*GridHosts.inputBlockWidth r n axes d
local notation "data₀" => AddressCircuit.ProductSlots axes (depth S (d+1) 0+1)
local notation "header" => WorkWords.grouped tiles extent

variable {σ : Type} [Fintype σ] (base : Frame σ (Pins S (d+1) (boundary S (d+1)) (60*TeamScales.logWidth r n) 0))

variable (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    [Fintype Edge] {g : ℕ} {len : Fin n} {state : Fin g} (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np) (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "channels" => (groupedGridRows G axes d order position copies).edge
local notation "groups" => Equiv.toEmbedding (Equiv.refl (Fin tiles))
local notation3 (prettyPrint := false) "birth" v => W.seedBorn position tag sites edges ports channels groups v copies

/-- The actual private program at each grouped original row, presented in the finite port
enumeration of the outer machine at its initial epoch. -/
noncomputable def seedBirthPrograms (words : O → Bool) :
    Site.Programs (seedState S G d order position copies table words).pack.layout :=
  fun v => Site.Lineage.start (birth v) (incoming_instances (seedBundle G axes d order position copies) v
    (f := Fin.fintype tiles) (g := portFintype (k := fan S) (b := 0) (P := Fin tiles)))

/-- The actual one-copy stride and incidence area are both paid by the seed's box capacity. -/
theorem seedBirthPrograms_fit (words : O → Bool) (room : copies*(2*cap) < 2^w) (v : Fin axes → Deck (d+2)) :
    ((seedBirthPrograms S order position W tag sites edges ports table words v).program).size < 2^w := by
  let N := W.seedGrouped position
  let stride := BottomReports.bottomStride (3*size₀+incoming N v) size₀
  have cap₀ : stride ≤ cap := (Nat.le_add_left _ _).trans (W.seedBorn_room position v)
  have hi : incoming N v ≤ stride := by unfold stride BottomReports.bottomStride; omega
  change copies*stride + incoming (BottomRepeat.wide N copies) v < _
  rw [incoming_wide,← Nat.mul_add]
  exact (Nat.mul_le_mul_left copies (show stride + incoming N v ≤ 2*cap by omega)).trans_lt room

/-- Starting at a ready geometric seed, the augmented frame reads its real routed birth
programs and the grouped exterior header simultaneously, on every private input. -/
theorem seedWidthFrame_reads (x : σ → Bool) (budget : ℕ → ℕ)
    (good : Good (S := S) (start := d+1) (shape := B) («w» := w) (bits := fun _ : Fin tiles => extent) budget 0
      (seedState S G d order position copies table (base.eval x)))
    (room : copies*(2*cap) < 2^w) :
    let a := seedState S G d order position copies table (base.eval x)
    WidthReads (S := S) (start := d+1) (shape := B) («w» := w) (t := 0) (bits := fun _ : Fin tiles => extent) a
      (seedBirthPrograms S order position W tag sites edges ports table (base.eval x))
        ((seedWidthFrame S plan base).eval x) ∧
      (header).Reads a.pack.layout a.rows.site (Function.Embedding.refl _) := by
  intro a
  let N := W.seedGrouped position
  let boxes := fun v => W.seedStored position tag sites edges ports channels groups v
  have hp := seed_header_reads (d := d) (copies := copies) S G order position table (base.eval x)
  have wf := (seed_widths S plan).fit
  have full (j : Fin (B 0).sites) : j ∈ Set.range a.rows.site := by
    let u := Fin.cast (congrArg Shape.sites (gridShape_zero S d)) j
    exact ⟨a.pack.layout.attach u, Fin.ext ((seedState_rows S G d order position copies table (base.eval x)).1 u)⟩
  have geo := BottomPrep.frame_geometry (Geo := O) (Data := data₀) (V := (B 0).sites) (E := (B 0).edges)
    («w» := w) (n := tiles) base (endPin (n := n) (r := r) (d := d) S) header (seedFit S plan)
    (fun _ => true) copies (3*size₀) size₀ x
  refine ⟨⟨geo,fun b => ?_⟩,hp⟩
  let stride (v : N.Site) := BottomReports.bottomStride (3*size₀+incoming N v) size₀
  let amount (v : N.Site) := if b then copies*stride v+incoming (BottomRepeat.wide N copies) v else copies*stride v
  have fitted (v : N.Site) : copies*stride v + incoming (BottomRepeat.wide N copies) v < 2^w :=
    seedBirthPrograms_fit S order position W tag sites edges ports table (base.eval x) room v
  have h := BottomPrep.frame_covers (Geo := O) (Data := data₀) (V := (B 0).sites) (E := (B 0).edges)
    («w» := w) (n := tiles) base (endPin (n := n) (r := r) (d := d) S) header (seedFit S plan)
    (fun _ => true) copies (3*size₀) size₀
    N a.rows.site a.rows.edge a.dummy (Function.Embedding.refl _) boxes x good.ready.names hp wf
    (fun j => iff_of_true rfl (full j))
    fitted b
  change Covers a.rows.site amount (assignedColumn b) ((seedWidthFrame S plan base).eval x) at h ⊢
  exact h

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
