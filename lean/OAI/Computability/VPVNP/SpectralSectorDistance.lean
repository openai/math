import OAI.Computability.VPVNP.SpectralSectorMap
import OAI.Computability.VPVNP.SpectralSectorSeminorm
import OAI.Computability.VPVNP.SpectralSectorQuadratic

/-!
# Euclidean coordinates on a spectral sector

The pullback seminorm from Section 4.1 has a quadratic square on the coordinate
plane. Its three coefficients are determined by the two unit axis lengths and
the length of the chord between their endpoints. The calculation includes
boundary points and degenerate sectors.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open Set

private theorem sectorDomain_interior {S : Set ℝ} (hS : Convex ℝ S) (h0 : 0 ∈ S) (h1 : 1 ∈ S) :
    ((1/4, 1/4) : ℝ × ℝ) ∈ interior (sectorDomain S) := by
  let U : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
  have hopen : IsOpen U :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd).inter
       (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
  have hsub : U ⊆ sectorDomain S := by
    intro p hp
    have hr₀ : 0 ≤ p.1 + p.2 := add_nonneg hp.1.le hp.2.1.le
    have hr₁ : p.1 + p.2 ≤ 1 := hp.2.2.le
    refine ⟨hp.1.le, hp.2.1.le, ?_⟩
    simpa only [smul_eq_mul, mul_zero, mul_one, zero_add] using
      hS h0 h1 (sub_nonneg.mpr hr₁) hr₀ (show 1-(p.1+p.2)+(p.1+p.2)=1 by ring)
  apply interior_maximal hsub hopen
  change 0 < (1/4 : ℝ) ∧ 0 < (1/4 : ℝ) ∧ (1/4 : ℝ) + 1/4 < 1
  norm_num

private theorem dist_congr_zero {X : Type*} [PseudoMetricSpace X] {x y x' y' : X}
    (hx : dist x x' = 0) (hy : dist y y' = 0) : dist x y = dist x' y' := by
  rw [dist_comm x y, PseudoMetricSpace.dist_eq_of_dist_zero y hx, dist_comm y x',
    PseudoMetricSpace.dist_eq_of_dist_zero x' hy]

/-- The sector of two rays or segments with a linear equal-parameter distance
has exactly the Euclidean squared distances determined by its three side lengths. -/
theorem sectorPoint_dist_sq {X : Type*} [PseudoMetricSpace X]
    (k : Type*) [Field k] (hf : HasFractions X) (hT : FractionTransport X)
    (hX : RealizableConfigurations k X)
    {a b : ℝ → X} {A B c : ℝ} {S : Set ℝ}
    (hS : Convex ℝ S) (h0 : 0 ∈ S) (h1 : 1 ∈ S)
    (ha : ∀ r ∈ S, ∀ s ∈ S, dist (a r) (a s) = A * |r-s|)
    (hb : ∀ r ∈ S, ∀ s ∈ S, dist (b r) (b s) = B * |r-s|)
    (hc : ∀ r ∈ S, dist (a r) (b r) = c * r)
    {p q : ℝ × ℝ} (hp : p ∈ sectorDomain S) (hq : q ∈ sectorDomain S) :
    dist (sectorPoint hf a b p) (sectorPoint hf a b q)^2 =
      (p.1-q.1)^2*A^2 + (p.2-q.2)^2*B^2 + (p.1-q.1)*(p.2-q.2)*(A^2+B^2-c^2) := by
  let H := sectorPoint hf a b
  let D := sectorDomain S
  have hbase := sectorDomain_interior hS h0 h1
  obtain ⟨P, hP⟩ := exists_sector_seminorm (H := H) (sectorDomain_convex hS) hT
    (fun {x y} hx hy {t} ht ht' => sectorPoint_atFraction hf hT hS ha hb hc hx hy ht ht') hbase
  have hr (f : Fin 8 → ℝ × ℝ) (hf' : ∀ i, f i ∈ interior D) :
      WireTensor.RealizableUpToScale k (fun i j => P (f i - f j)) := by
    have hdist (i j : Fin 8) : dist (H (f i)) (H (f j)) = P (f i - f j) :=
      (dist_comm _ _).trans (hP _ (interior_subset (hf' j)) _ (interior_subset (hf' i)))
    simpa only [hdist] using hX 8 (fun i => H (f i))
  obtain ⟨L, W, C, hquad⟩ :=
    SpectralGeometry.sectorSeminorm_quadratic P isOpen_interior ⟨_, hbase⟩ hr
  have hdist (s t : ℝ × ℝ) (hs : s ∈ D) (ht : t ∈ D) :
      dist (H s) (H t)^2 = (s.1-t.1)^2*L + (s.2-t.2)^2*W + (s.1-t.1)*(s.2-t.2)*C := by
    rw [dist_comm, hP t ht s hs, hquad]
    rfl
  have ho : (0, 0) ∈ D := ⟨le_rfl, le_rfl, by simpa using h0⟩
  have he : (1, 0) ∈ D := ⟨zero_le_one, le_rfl, by simpa using h1⟩
  have hg : (0, 1) ∈ D := ⟨le_rfl, zero_le_one, by simpa using h1⟩
  obtain ⟨ho₁, ho₂⟩ := sectorPoint_boundary_distances hf a b hc ho
  obtain ⟨he₁, _⟩ := sectorPoint_boundary_distances hf a b hc he
  obtain ⟨_, hg₂⟩ := sectorPoint_boundary_distances hf a b hc hg
  have o₁ : dist (H (0,0)) (a 0) = 0 := by simpa [H, dist_comm] using ho₁
  have o₂ : dist (H (0,0)) (b 0) = 0 := by simpa [H] using ho₂
  have e₁ : dist (H (1,0)) (a 1) = 0 := by simpa [H, dist_comm] using he₁
  have g₂ : dist (H (0,1)) (b 1) = 0 := by simpa [H] using hg₂
  have hL := hdist _ _ ho he
  rw [dist_congr_zero o₁ e₁, ha 0 h0 1 h1] at hL
  norm_num at hL
  have hW := hdist _ _ ho hg
  rw [dist_congr_zero o₂ g₂, hb 0 h0 1 h1] at hW
  norm_num at hW
  have hC := hdist _ _ he hg
  rw [dist_congr_zero e₁ g₂, hc 1 h1] at hC
  norm_num at hC
  have heq : C = A^2+B^2-c^2 := by linarith only [hC, hL, hW]
  rw [← hL, ← hW, heq] at hdist
  exact hdist p q hp hq

end WireGeometry

end VPVNP
end Computability
end OAI
