import OAI.Computability.BorderVNP.PackedGridSidecar
import OAI.Computability.BorderVNP.PackedBottomReportInventory

/-! # Exact inventory and distinct native tags of the prewired bottom grid

The actual routed original vertex is retained for each parameter and exponent
position. Copies of a bottom bundle consume one bit for each such original
position; subdivision and grouping do not create additional uses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse BottomReports GridBoxes GridPlacement Cover TeamContraction TallySidecar
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open private keyProperties labelKey from OAI.Computability.BorderVNP.PackedGridSidecar
open scoped Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p : ℕ} (siteID : (W.routedFine position).Site ↪ Fin s) (edgeID : (W.routedFine position).Edge ↪ Fin m)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p)
local notation "V" => Fin q → Deck (depth+2)
local notation "rules₀" => W.routedRules position (sidecarReport code)
/-- True original one-copy factors at this routed cell, with the published
parameter and bit-position source names. -/
noncomputable abbrev nativeFactors (c : V) :=
  factors (W.routedFine position) (cell position W.route) c siteID edgeID portID
    (fun v => (rules₀) v.val)
local notation "rows₀" => W.nativeFactors position code siteID edgeID portID

/-- Both immutable scalar labels are retained by the three-field native source tag. -/
theorem sidecarReport_injective : Function.Injective (sidecarReport code (r := r) (d := d)) := by
  intro j k h
  exact Prod.ext (code.injective (congrArg Port.base h)) (Fin.ext (congrArg Port.copyStride h))

/-- One-copy source tags in the original factor order are distinct as typed
ports, before conversion to the private three-field positions. -/
theorem sidecar_tags_nodup (c : V) (next : ℕ) :
    ((sidecar next (rows₀ c)).map Prod.fst).Nodup := by
  apply List.Nodup.of_map (fun p : Port => (p.base,p.copyStride))
  have h := (keyProperties W position code siteID edgeID portID c next).1
  simpa only [sidecarPositions,positions,List.map_map,Function.comp_def,labelKey] using h

set_option maxHeartbeats 1000000 in
/-- The complete native tag at a physical row decodes to the real owned
parameter and exponent index; its remaining field is the fixed zero. -/
theorem sidecar_tag_at (c : V) (next : ℕ) (i : Fin (sidecar next (rows₀ c)).length) :
    ((sidecar next (rows₀ c)).get i).1 = sidecarReport code
      (W.sidecarEquiv position code siteID edgeID portID c next ⟨i.val,by simpa [sidecarPositions,positions] using i.isLt⟩).val := by
  let pos : Fin (W.sidecarPositions position code siteID edgeID portID c next).length :=
    ⟨i.val,by simpa [sidecarPositions,positions] using i.isLt⟩
  let j := W.sidecarEquiv position code siteID edgeID portID c next pos
  let tag := ((sidecar next (rows₀ c)).get i).1
  have hm : tag ∈ (sidecar next (rows₀ c)).map Prod.fst := List.mem_map.mpr ⟨_,List.get_mem _ i,rfl⟩
  rw [sidecar_tags] at hm
  obtain ⟨f,hf,htag⟩ := List.mem_filterMap.mp hm
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hf
  rw [factorTag_rule] at htag
  obtain ⟨k,_,hk⟩ := (W.routed_ruleTag_iff position (sidecarReport code) u.val tag).mp htag
  have prop := W.sidecarEquiv_fields position code siteID edgeID portID c next pos
  have hfield : tag.base = code j.val.1 ∧ tag.copyStride = j.val.2.val := by
    simpa only [tag,j,sidecarPositions,positions,pos,List.get_eq_getElem,List.getElem_map] using
      And.intro prop.1 prop.2.1
  have hj : k = j.val := Prod.ext (code.injective ((congrArg Port.base hk).trans hfield.1))
    (Fin.ext ((congrArg Port.copyStride hk).trans hfield.2))
  exact hk.symm.trans (congrArg (sidecarReport code) hj)

/-- The exact one-copy use count over all cells is the number of parameter and
exponent pairs in the prewired query. -/
theorem sidecar_total_count :
    (∑ c : V, count (rows₀ c)) = Fintype.card (WeightSites n g r d) := by
  let w : WeightSites n g r d ↪ (W.routedFine position).Site :=
    (BooleanLayout.weightSite (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d)).trans Function.Embedding.inl
  apply total_grid_count (W.routedFine position) (cell position W.route) siteID edgeID portID
    (rules₀) w
  intro v
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨tag,ht⟩
    obtain ⟨j,hj,_⟩ := (W.routed_ruleTag_iff position (sidecarReport code) v tag).mp ht
    exact ⟨j,hj⟩
  · rintro ⟨j,hj⟩
    exact ⟨_,(W.routed_ruleTag_iff position (sidecarReport code) v _).mpr ⟨j,hj,rfl⟩⟩

/-- Across any number of bottom bundles with the prescribed copy count, the
native weighted-use entries are exactly one per parameter, bit place and copy. -/
theorem sidecar_total_copies (bundles copies : ℕ) (next : Fin bundles → V → ℕ) :
    (∑ z : Fin bundles, ∑ c : V,
      (W.sidecarPositions position code siteID edgeID portID c (next z c)).length*copies) =
      bundles*Fintype.card (GrammarLabel (Fin n × Bool) (Fin g) n)*Nat.clog 2 (r*(2*d.val+1)+1)*copies := by
  change (∑ z : Fin bundles, ∑ c : V, (positions (next z c) (rows₀ c)).length*copies) = _
  simp only [positions_length,← Finset.sum_mul]
  rw [W.sidecar_total_count position code siteID edgeID portID]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,
    WeightSites,Fintype.card_prod,Nat.mul_assoc]

/-- Independent private placement choices in distinct bottom bundles have the
same exact source count. The native rows may have different names and orders. -/
theorem sidecar_total_witnesses (bundles copies : ℕ) (wits : Fin bundles → WiredWitness G d D q depth order state)
    (sites : ∀ b, ((wits b).routedFine position).Site ↪ Fin s)
    (edges : ∀ b, ((wits b).routedFine position).Edge ↪ Fin m) (next : Fin bundles → V → ℕ) :
    (∑ b : Fin bundles, ∑ c : V,
      ((wits b).sidecarPositions position code (sites b) (edges b) portID c (next b c)).length*copies) =
      bundles*Fintype.card (GrammarLabel (Fin n × Bool) (Fin g) n)*Nat.clog 2 (r*(2*d.val+1)+1)*copies := by
  have hb (b : Fin bundles) : (∑ c : V,
      ((wits b).sidecarPositions position code (sites b) (edges b) portID c (next b c)).length*copies) =
      Fintype.card (WeightSites n g r d)*copies := by
    change (∑ c : V, (positions (next b c) ((wits b).nativeFactors position code (sites b) (edges b) portID c)).length*copies) = _
    simp only [positions_length,← Finset.sum_mul]
    rw [(wits b).sidecar_total_count position code (sites b) (edges b) portID]
  simp only [hb,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,
    WeightSites,Fintype.card_prod,Nat.mul_assoc]

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
