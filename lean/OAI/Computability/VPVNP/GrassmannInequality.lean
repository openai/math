import OAI.Computability.VPVNP.CubeExclusion
import OAI.Computability.VPVNP.GrassmannEnergy
import OAI.Computability.VPVNP.GrassmannPlaneRigidity
import OAI.Computability.VPVNP.GrassmannPresentation

/-!
# The strict Grassmann inequality

Lemma 5.3 of *VP and VNP differ over every field* gives a strict, uniform
improvement over the bound by the Grassmann plane dimension `m` when all
target spaces exclude a Euclidean cube of some dimension less than `m`.
The proof here identifies the extremal distances on all pairs of type
`r < m`, exhibits the cube on the coordinate planes, and uses compactness
of normalized finite distance arrays to obtain the uniform gap.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open scoped symmDiff

variable {m r : ℕ}

private theorem equal_on_type {D : Plane m → Plane m → ℝ} (hr : r < m)
    (opp : ∀ a b c d, IsSquare r 1 a b c d → D a b = D d c)
    {a b a' b' : Plane m} (hab : HasType r a b) (hab' : HasType r a' b') :
    D a b = D a' b' := by
  obtain ⟨v, w, hind, hl, hu⟩ := hab.exists_frame hr.le
  obtain ⟨v', w', hind', hl', hu'⟩ := hab'.exists_frame hr.le
  let hm := Nat.sub_add_cancel hr.le
  rw [show a = leftPlane v w hm hind from Subtype.ext hl,
    show b = rightPlane v w hm hind from Subtype.ext hu,
    show a' = leftPlane v' w' hm hind' from Subtype.ext hl',
    show b' = rightPlane v' w' hm hind' from Subtype.ext hu']
  exact frame_planes_rigid hr hm D opp hind hind'

/-- At a saturated normalized array every ordered pair of type `r < m`
has squared distance exactly `r`. -/
theorem value_eq_type_of_saturated {D : Plane m → Plane m → ℝ} (hq : QuadBounds D)
    (h1 : mean D 1 = 1) (hm : mean D m = (m : ℝ)) (hr : r < m)
    {a b : Plane m} (hab : HasType r a b) : D a b = (r : ℝ) := by
  have hs (k : ℕ) (hk : k ≤ m) : mean D k = (k : ℝ) := by
    simpa only [h1, mul_one] using mean_eq_mul_one hq.quad hq.diag
      (by simpa only [h1, mul_one] using hm) hk
  have hopp (a b c d : Plane m) (sq : IsSquare r 1 a b c d) : D a b = D d c := by
    have he := sq.eq_of_mean_eq_add hq.quad (by
      rw [hs (r+1) hr, hs r hr.le, h1, Nat.cast_add, Nat.cast_one])
    exact (hq.opposite a b c d he).1.trans (hq.symm c d)
  have hc (p : Pair m r) : D p.val.1 p.val.2 = D a b :=
    equal_on_type hr hopp p.property hab
  let : Nonempty (Pair m r) := ⟨⟨(a,b), hab⟩⟩
  have hmean : mean D r = D a b := by
    simp only [mean, hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  exact hmean.symm.trans (hs r hr.le)

/-- The equality case of Lemma 5.3 gives the marked Euclidean cube, with
Hamming distance as its squared distance. -/
theorem cube_of_saturated {ℓ : ℕ} (hℓ : ℓ < m) {D : Plane m → Plane m → ℝ}
    (hq : QuadBounds D) (h1 : mean D 1 = 1) (hm : mean D m = (m : ℝ)) :
    ∃ e : Finset (Fin ℓ) → Plane m, ∀ i j, D (e i) (e j) = ((i ∆ j).card : ℝ) := by
  obtain ⟨e, he⟩ := exists_cube_face hℓ.le
  refine ⟨e, fun i j => value_eq_type_of_saturated hq h1 hm ?_ (he i j)⟩
  exact lt_of_le_of_lt (by simpa using Finset.card_le_univ (i ∆ j)) hℓ

/-- Lemma 5.3. The improvement over the factor `m` is uniform in both the
target space and the configuration of its Grassmannian points. -/
theorem strict_grassmann_bound {κ : Type*} (X : κ → Type*) [∀ k, PseudoMetricSpace (X k)]
    {ℓ m : ℕ} (hℓ : ℓ < m) (hcat : ∀ k, SpectralGeometry.HasCATZeroSegments (X k))
    (hexclude : cubeDistances ℓ ∉ closure (markedDistances X (Finset (Fin ℓ)))) :
    ∃ η > 0, ∀ (k : κ) (x : Plane m → X k), energy x m ≤ ((m : ℝ) - η) * energy x 1 :=
  strict_grassmann_bound_of_rigidity X m (fun i j : Finset (Fin ℓ) => ((i ∆ j).card : ℝ))
    hcat hexclude (fun _ hq _ hr => mean_le_mul_one hq.quad hq.diag hr)
    (fun _ hq h1 hm => cube_of_saturated hℓ hq h1 hm)

end Grassmann

end VPVNP
end Computability
end OAI
