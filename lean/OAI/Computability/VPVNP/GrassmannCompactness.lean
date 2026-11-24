import OAI.Computability.VPVNP.GrassmannFourPoint
import OAI.Computability.VPVNP.GrassmannMeanBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.Compact

/-!
# Uniformity of the strict Grassmann inequality

The last paragraph of Lemma 5.3 in *VP and VNP differ over every field*
passes from rigidity of an extremal marked configuration to a strict uniform
bound. The relevant topology is the product topology on real arrays. Restricting
to a specified set of marks and taking square roots are continuous, so a cube
in a limiting squared-distance array violates uniform cube exclusion for the
original distances.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open Set

variable {κ V J : Type*} (X : κ → Type*) [∀ k, PseudoMetricSpace (X k)]

/-- The rescaled marked distances whose closure defines uniform exclusion. -/
def markedDistances (V : Type*) : Set (V → V → ℝ) :=
  {D | ∃ (k : κ) (s : ℝ), 0 < s ∧ ∃ x : V → X k, D = fun i j => s * dist (x i) (x j)}

/-- Rescaled squared distances. The parameter is the square of the distance scale. -/
def markedSquares (V : Type*) : Set (V → V → ℝ) :=
  {D | ∃ (k : κ) (s : ℝ), 0 < s ∧ ∃ x : V → X k, D = fun i j => s * dist (x i) (x j) ^ 2}

theorem smul_mem_markedSquares {D : V → V → ℝ} (hD : D ∈ markedSquares X V)
    {t : ℝ} (ht : 0 < t) : t • D ∈ markedSquares X V := by
  obtain ⟨k, s, hs, x, rfl⟩ := hD
  refine ⟨k, t * s, mul_pos ht hs, x, ?_⟩
  ext i j
  exact (mul_assoc _ _ _).symm

/-- Restricting a limiting squared-distance array to marked vertices yields
an ordinary distance array in the closure for those marks. -/
theorem restrict_sqrt_mem_closure_markedDistances {D : V → V → ℝ}
    (hD : D ∈ closure (markedSquares X V)) (e : J → V) :
    (fun i j => Real.sqrt (D (e i) (e j))) ∈ closure (markedDistances X J) := by
  let f := fun (A : V → V → ℝ) (i j : J) => Real.sqrt (A (e i) (e j))
  have hf : MapsTo f (markedSquares X V) (markedDistances X J) := by
    rintro _ ⟨k, s, hs, x, rfl⟩
    refine ⟨k, Real.sqrt s, Real.sqrt_pos.mpr hs, x ∘ e, ?_⟩
    ext i j
    simp [f, Real.sqrt_mul hs.le, Real.sqrt_sq dist_nonneg]
  have hc : Continuous f := by dsimp [f]; fun_prop
  exact hf.closure hc hD

/-- Uniform exclusion prevents a prescribed ordinary distance array from
appearing on any set of marks in a limiting squared-distance array. -/
theorem excluded_of_mem_closure_markedSquares {Q : J → J → ℝ}
    (hQ : Q ∉ closure (markedDistances X J)) {D : V → V → ℝ}
    (hD : D ∈ closure (markedSquares X V)) :
    ¬ ∃ e : J → V, ∀ i j, Real.sqrt (D (e i) (e j)) = Q i j := by
  rintro ⟨e, he⟩
  exact hQ ((funext fun i => funext (he i)) ▸ restrict_sqrt_mem_closure_markedDistances X hD e)

/-- On bounded normalizations of marked squared distances, a strict bound at
every point of the closure yields a common positive improvement. The case of
zero normalizing energy is handled by the non-strict homogeneous bound. -/
theorem uniform_gap_of_normalized_strict
    (adj comp : (V → V → ℝ) → ℝ) (m K : ℝ) (ha : Continuous adj) (hc : Continuous comp)
    (ha_scale : ∀ (s : ℝ) D, adj (s • D) = s * adj D)
    (hc_scale : ∀ (s : ℝ) D, comp (s • D) = s * comp D)
    (ha_nonneg : ∀ D ∈ markedSquares X V, 0 ≤ adj D)
    (hzero : ∀ D ∈ markedSquares X V, adj D = 0 → comp D ≤ 0)
    (hbounded : ∀ D ∈ markedSquares X V, adj D = 1 → ∀ i j, D i j ≤ K)
    (hstrict : ∀ D ∈ closure (markedSquares X V), adj D = 1 → comp D < m) :
    ∃ η > 0, ∀ D ∈ markedSquares X V, comp D ≤ (m - η) * adj D := by
  let S := markedSquares X V ∩ {D | adj D = 1}
  let box : Set (V → V → ℝ) := Icc 0 (fun _ _ => K)
  have hbox : IsCompact box := isCompact_Icc
  have hsub : S ⊆ box := by
    rintro D ⟨hD, hA⟩
    refine ⟨?_, hbounded D hD hA⟩
    obtain ⟨k, s, hs, x, rfl⟩ := hD
    exact fun i j => mul_nonneg hs.le (sq_nonneg _)
  have hcompact : IsCompact (closure S) :=
    hbox.of_isClosed_subset isClosed_closure (closure_minimal hsub hbox.isClosed)
  have hadj : closure S ⊆ {D | adj D = 1} :=
    closure_minimal inter_subset_right (isClosed_eq ha continuous_const)
  have hsrc : closure S ⊆ closure (markedSquares X V) := closure_mono inter_subset_left
  have hlt (D) (hD : D ∈ closure S) : comp D < m := hstrict D (hsrc hD) (hadj hD)
  obtain ⟨c, hcm, hbound⟩ : ∃ c : ℝ, c < m ∧ ∀ D ∈ closure S, comp D ≤ c :=
    hcompact.exists_forall_le' (α := ℝᵒᵈ) hc.continuousOn hlt
  refine ⟨m - c, sub_pos.mpr hcm, ?_⟩
  intro D hD
  rw [sub_sub_cancel]
  rcases (ha_nonneg D hD).eq_or_lt with h | h
  · rw [← h, mul_zero]
    exact hzero D hD h.symm
  · let t := (adj D)⁻¹
    have ht : 0 < t := inv_pos.mpr h
    have hnorm : adj (t • D) = 1 := by rw [ha_scale]; exact inv_mul_cancel₀ h.ne'
    have hnormS : t • D ∈ S := ⟨smul_mem_markedSquares X hD ht, hnorm⟩
    have hcomp := hbound _ (subset_closure hnormS)
    rw [hc_scale] at hcomp
    calc
      comp D = (t * comp D) * adj D := by dsimp [t]; field_simp
      _ ≤ c * adj D := mul_le_mul_of_nonneg_right hcomp h.le

/-- Every limiting marked array retains the four-point inequality and its
opposite-side equality case, even when the target spaces vary. -/
theorem quadBounds_of_mem_closure_markedSquares
    (hcat : ∀ k, SpectralGeometry.HasCATZeroSegments (X k)) {D : V → V → ℝ}
    (hD : D ∈ closure (markedSquares X V)) : QuadBounds D := by
  apply quadBounds_of_mem_catZeroArrays
  apply closure_minimal (t := catZeroArrays V) _ (isClosed_catZeroArrays V) hD
  rintro _ ⟨k, s, hs, x, rfl⟩
  exact scaledDistSq_mem_catZeroArrays (hcat k) x hs.le

/-- The compactness implication in Lemma 5.3 for the actual binary Grassmannian.
The inputs from the Grassmann combinatorics are the non-strict bounds on the
pair means and rigidity at equality. Uniform exclusion concerns the ordinary
distance array of the cube, while rigidity yields its squared distances. -/
theorem strict_grassmann_bound_of_rigidity (m : ℕ) (Q : J → J → ℝ)
    (hcat : ∀ k, SpectralGeometry.HasCATZeroSegments (X k))
    (hexclude : (fun i j => Real.sqrt (Q i j)) ∉ closure (markedDistances X J))
    (hB : ∀ D : Plane m → Plane m → ℝ, QuadBounds D →
      ∀ r ≤ m, mean D r ≤ (r : ℝ) * mean D 1)
    (hrigid : ∀ D : Plane m → Plane m → ℝ, QuadBounds D →
      mean D 1 = 1 → mean D m = (m : ℝ) → ∃ e : J → Plane m, ∀ i j, D (e i) (e j) = Q i j) :
    ∃ η > 0, ∀ (k : κ) (x : Plane m → X k),
      mean (fun i j => dist (x i) (x j) ^ 2) m ≤
        ((m : ℝ) - η) * mean (fun i j => dist (x i) (x j) ^ 2) 1 := by
  obtain ⟨K, hK⟩ := exists_coordinate_bound m
  have hquad {D : Plane m → Plane m → ℝ} (hD : D ∈ markedSquares X (Plane m)) :=
    quadBounds_of_mem_closure_markedSquares X hcat (subset_closure hD)
  have hstrict (D : Plane m → Plane m → ℝ) (hD : D ∈ closure (markedSquares X (Plane m)))
      (h1 : mean D 1 = 1) : mean D m < (m : ℝ) := by
    have hq := quadBounds_of_mem_closure_markedSquares X hcat hD
    have hm : mean D m ≤ (m : ℝ) := by simpa [h1] using hB D hq m le_rfl
    refine lt_of_le_of_ne hm (fun he => ?_)
    obtain ⟨e, he'⟩ := hrigid D hq h1 he
    exact excluded_of_mem_closure_markedSquares X hexclude hD
      ⟨e, fun i j => congrArg Real.sqrt (he' i j)⟩
  obtain ⟨η, hη, hgap⟩ := uniform_gap_of_normalized_strict X
    (fun D => mean D 1) (fun D => mean D m) m K (continuous_mean m 1) (continuous_mean m m)
    (fun s D => mean_smul D 1 s) (fun s D => mean_smul D m s)
    (fun _ hD => mean_nonneg (hquad hD).nonneg 1)
    (fun D hD hz => by simpa [hz] using hB D (hquad hD) m le_rfl)
    (fun D hD h1 => hK D (hquad hD).nonneg fun r hr => by simpa [h1] using hB D (hquad hD) r hr)
    hstrict
  refine ⟨η, hη, fun k x => hgap _ ⟨k, 1, one_pos, x, ?_⟩⟩
  simp

end Grassmann

end VPVNP
end Computability
end OAI
