import OAI.Computability.BorderVNP.CoverLorentzPolygon
import OAI.Computability.BorderVNP.CoverLorentzTile
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-!
# Exact Borel Dirichlet tiles

Ties are resolved by the lexicographically least point of the orbit in the
closed tile. This choice uses only position, hence pulling the tile back to frames
retains every direction at the selected positions. The seams of the resulting
Borel tile lie on the same finite collection of geodesic lines.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Matrix Set UpperHalfPlane MeasureTheory
open scoped Pointwise MatrixGroups

/-- The Borel σ-algebra on the real frame group. -/
local instance positionFrameMeasurableSpace : MeasurableSpace SL(2,ℝ) := borel _
/-- The frame-group measurable structure is its topological Borel structure. -/
local instance positionFrameBorelSpace : BorelSpace SL(2,ℝ) := ⟨rfl⟩

private def pointRank (z : ℍ) : ℝ ×ₗ ℝ := toLex (z.re,z.im)

private theorem pointRank_injective : Function.Injective pointRank := by
  intro z w h
  have e : (z.re,z.im) = (w.re,w.im) := h
  exact UpperHalfPlane.ext (Complex.ext (congrArg Prod.fst e) (congrArg Prod.snd e))

/-- The canonical position tile at positive depth, using a fixed choice on boundary ties. -/
noncomputable def planeTile (l : ℕ) : Set ℍ :=
  {z | z ∈ dirichlet (l+1) ∧ ∀ u : gamma (l+1), gammaSL (l+1) u • z ∈ dirichlet (l+1) →
    pointRank z ≤ pointRank (gammaSL (l+1) u • z)}

/-- Borel measurability of the position tile with all ties resolved. -/
theorem planeTile_measurable (l : ℕ) : MeasurableSet (planeTile l) := by
  have hD := (dirichlet_compact (l+1)).isClosed.measurableSet
  change MeasurableSet (dirichlet (l+1) ∩ {z : ℍ | ∀ u : gamma (l+1),
    gammaSL (l+1) u • z ∈ dirichlet (l+1) → pointRank z ≤ pointRank (gammaSL (l+1) u • z)})
  apply hD.inter
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro u
  let f : ℍ → ℍ := fun z => gammaSL (l+1) u • z
  have hf : Continuous f := continuous_const_smul _
  change MeasurableSet {z : ℍ | f z ∈ dirichlet (l+1) → pointRank z ≤ pointRank (f z)}
  simp only [imp_iff_not_or,pointRank,Prod.Lex.toLex_le_toLex]
  exact ((hf.measurable hD).compl).union ((isOpen_lt continuous_re (continuous_re.comp hf)).measurableSet.union
    ((isClosed_eq continuous_re (continuous_re.comp hf)).measurableSet.inter
    (isClosed_le continuous_im (continuous_im.comp hf)).measurableSet))

/-- Every point has exactly one group element taking it into the chosen position tile. -/
theorem existsUnique_mem_planeTile (l : ℕ) (z : ℍ) :
    ∃! u : gamma (l+1), gammaSL (l+1) u • z ∈ planeTile l := by
  classical
  have hs := finite_movers (l+1) (isCompact_singleton (x := z)) (dirichlet_compact (l+1))
  let s := hs.toFinset
  have hmem (u : gamma (l+1)) : u ∈ s ↔ gammaSL (l+1) u • z ∈ dirichlet (l+1) := by
    rw [hs.mem_toFinset]
    simp [movers]
  obtain ⟨j,hj⟩ := exists_mem_dirichlet (l+1) z
  obtain ⟨u,hu,hmin⟩ := s.exists_min_image (fun v => pointRank (gammaSL (l+1) v • z)) ⟨j,(hmem _).2 hj⟩
  have htile : gammaSL (l+1) u • z ∈ planeTile l := by
    refine ⟨(hmem _).1 hu,?_⟩
    intro v hv
    rw [← mul_smul,← map_mul] at hv ⊢
    exact hmin (v*u) ((hmem _).2 hv)
  refine ⟨u,htile,?_⟩
  intro v hv
  have huv := htile.2 (v*u⁻¹)
  have hvu := hv.2 (u*v⁻¹)
  simp only [map_mul,map_inv,mul_smul,inv_smul_smul] at huv hvu
  have hpos := pointRank_injective (le_antisymm (hvu htile.1) (huv hv.1))
  have he := eq_one_of_fix (u⁻¹*v) z (by rw [map_mul,map_inv,mul_smul,hpos,inv_smul_smul])
  exact eq_of_inv_mul_eq_one he |>.symm

/-- The exact frame tile over the Borel position tile, with every angle included. -/
theorem exact_position_frame_tile (l : ℕ) :
    MeasurableSet ((fun g : SL(2,ℝ) => g • I) ⁻¹' planeTile l) ∧
    BorderVNP.Hecke.ExactTile (frameGroup (l+1)) ((fun g : SL(2,ℝ) => g • I) ⁻¹' planeTile l) := by
  refine ⟨(show Continuous (fun g : SL(2,ℝ) => g • I) by fun_prop).measurable (planeTile_measurable l),?_⟩
  intro g
  obtain ⟨u,hu,huniq⟩ := existsUnique_mem_planeTile l (g • I)
  refine ⟨⟨gammaSL (l+1) u,u,rfl⟩,?_,?_⟩
  · change ((gammaSL (l+1) u)*g) • I ∈ planeTile l
    rwa [mul_smul]
  · rintro ⟨_,v,rfl⟩ hv
    change (gammaSL (l+1) v * g) • I ∈ planeTile l at hv
    rw [mul_smul] at hv
    exact Subtype.ext (congrArg (gammaSL (l+1)) (huniq v hv))

/-- Every tie removed from the closed tile belongs to a nontrivial site bisector. -/
theorem removed_point_bisector {l : ℕ} {z : ℍ} (h : z ∈ dirichlet (l+1))
    (hz : z ∉ planeTile l) : ∃ u : gamma (l+1), u ≠ 1 ∧ dist z I = dist z (gammaSL (l+1) u • I) := by
  classical
  have h' : ¬ ∀ u : gamma (l+1), gammaSL (l+1) u • z ∈ dirichlet (l+1) →
      pointRank z ≤ pointRank (gammaSL (l+1) u • z) := fun hu => hz ⟨h,hu⟩
  push Not at h'
  obtain ⟨v,hv,hlt⟩ := h'
  have hn : v ≠ 1 := fun h => by simp [h] at hlt
  refine ⟨v⁻¹,inv_ne_one.mpr hn,le_antisymm (h _) ?_⟩
  have he := hv v
  rw [dist_smul] at he
  rw [← dist_smul (gammaSL (l+1) v) z,map_inv,smul_inv_smul]
  exact he

/-- Boundary ties preserve the finite geodesic seam description of the exact Borel tile. -/
theorem planeTile_frontier_bisectors (l : ℕ) :
    ∃ s : Finset (gamma (l+1)), (∀ u ∈ s, u ≠ 1) ∧ ∀ z ∈ frontier (planeTile l),
      ∃ u ∈ s, dist z I = dist z (gammaSL (l+1) u • I) := by
  classical
  obtain ⟨a,ha,had⟩ := dirichlet_frontier_bisectors l
  obtain ⟨R,_,hR⟩ := dirichlet_bounded (l+1)
  have hf := finite_sites (l+1) (ProperSpace.isCompact_closedBall I (2*R))
  let b := hf.toFinset.erase 1
  let s := a ∪ b
  let S : Set ℍ := ⋃ u ∈ s, {z | dist z I = dist z (gammaSL (l+1) u • I)}
  have hS : IsClosed S := s.finite_toSet.isClosed_biUnion
    (fun _ _ => isClosed_eq (by fun_prop) (by fun_prop))
  have hsubset : planeTile l ⊆ dirichlet (l+1) := fun _ hz => hz.1
  have hremoved (z : ℍ) (hz : z ∈ dirichlet (l+1)) (hn : z ∉ planeTile l) : z ∈ S := by
    obtain ⟨u,hu,he⟩ := removed_point_bisector hz hn
    have hd := dist_triangle (gammaSL (l+1) u • I) z I
    rw [dist_comm (gammaSL (l+1) u • I) z, ← he] at hd
    have hr : dist z I ≤ R := hR hz
    have hb : u ∈ b := Finset.mem_erase.mpr ⟨hu,hf.mem_toFinset.mpr (by
      change dist (gammaSL (l+1) u • I) I ≤ 2*R; linarith)⟩
    exact mem_iUnion₂.mpr ⟨u,Finset.mem_union_right _ hb,he⟩
  refine ⟨s,?_,?_⟩
  · intro u hu
    rcases Finset.mem_union.mp hu with h|h
    exacts [ha u h,(Finset.mem_erase.mp h).1]
  · intro z hz
    suffices hzS : z ∈ S by
      obtain ⟨u,hu,he⟩ := mem_iUnion₂.mp hzS
      exact ⟨u,hu,he⟩
    by_contra h
    have hD : z ∈ dirichlet (l+1) := closure_minimal hsubset (dirichlet_compact _).isClosed hz.1
    have hI : z ∈ interior (dirichlet (l+1)) := by
      by_contra hn
      obtain ⟨u,hu,he⟩ := had z ((mem_frontier_iff_notMem_interior hD).2 hn)
      exact h (mem_iUnion₂.mpr ⟨u,Finset.mem_union_left _ hu,he⟩)
    have hU : interior (dirichlet (l+1)) ∩ Sᶜ ⊆ planeTile l := by
      intro x hx
      by_contra hn
      exact hx.2 (hremoved x (interior_subset hx.1) hn)
    exact hz.2 (interior_maximal hU (isOpen_interior.inter hS.isOpen_compl) ⟨hI,h⟩)

end Cover

end BorderVNP
end Computability
end OAI
