import OAI.LinearAlgebra.SpectralBooks.CurvatureBlowup.Blowup

/-!
# Geodesics in the space of limiting rays

Coordinate segments between bounded representatives give constant-speed
segments between arbitrary points of the pointed metric ultralimit.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace CurvatureBlowup

open HyperbolicObstruction MetricLimit Filter Topology Set

variable {X : Type*} [MetricSpace X]

private theorem scaled_isGeodesic (g : IsGeodesic X) {r : ℝ} (hr : 0 < r) :
    IsGeodesic (MetricScale.Space r hr X) := by
  intro x y
  obtain ⟨γ, hγ⟩ := g x.val y.val
  refine ⟨fun t ↦ ⟨γ t⟩, MetricScale.Space.ext hγ.1, MetricScale.Space.ext hγ.2.1, ?_⟩
  intro s hs t ht
  change r * dist (γ s) (γ t) = |s - t| * (r * dist x.val y.val)
  rw [hγ.2.2 _ hs _ ht]
  ring

private theorem limit_isGeodesic {Z : ℕ → Type*} [∀ n, MetricSpace (Z n)]
    {o : ∀ n, Z n} {ω : Ultrafilter ℕ} (g : ∀ n, IsGeodesic (Z n)) :
    IsGeodesic (MetricLimit.Space (U := ω) (X := Z) (o := o)) := by
  intro x y
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk y
  choose γ hγ using fun n ↦ g n (x.val n) (y.val n)
  let sec (t : ℝ) : Bounded ω Z o := if ht : t ∈ Icc (0 : ℝ) 1 then
    ⟨fun n ↦ γ n t, by
      obtain ⟨R, hR⟩ := x.bound
      obtain ⟨S, hS⟩ := bounded_dist x y
      refine ⟨R + S, fun n ↦ (dist_triangle _ (x.val n) _).trans ?_⟩
      rw [(hγ n).dist_from_source ht]
      exact add_le_add (hR n) ((mul_le_of_le_one_left dist_nonneg ht.2).trans (hS n).2)⟩
    else x
  have hsec {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (n : ℕ) : (sec t).val n = γ n t := by
    simp only [sec, dite_eq_left ht]
  refine ⟨fun t ↦ point (sec t), ?_, ?_, ?_⟩
  · apply congrArg SeparationQuotient.mk
    exact Bounded.ext (funext fun n ↦ (hsec (by norm_num) n).trans (hγ n).1)
  · apply congrArg SeparationQuotient.mk
    exact Bounded.ext (funext fun n ↦ (hsec (by norm_num) n).trans (hγ n).2.1)
  · intro s hs t ht
    apply tendsto_nhds_unique (tendsto_point_dist _ _)
    apply ((tendsto_point_dist x y).const_mul |s-t|).congr
    intro n
    simp only [hsec hs, hsec ht, (hγ n).2.2 s hs t ht]

/-- The common ambient space of all limiting rays is geodesic. -/
theorem isGeodesic (g : IsGeodesic X) (o : X) : IsGeodesic (Space o) :=
  limit_isGeodesic (fun n ↦ scaled_isGeodesic g (inv_pos.mpr (scale_pos n)))

end CurvatureBlowup

end

end SpectralBooks
end LinearAlgebra
end OAI
