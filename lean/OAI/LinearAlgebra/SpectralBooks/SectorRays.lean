import OAI.LinearAlgebra.SpectralBooks.Comparison
import OAI.LinearAlgebra.SpectralBooks.Sector
import OAI.LinearAlgebra.SpectralBooks.SectorSeminorm
import OAI.LinearAlgebra.SpectralBooks.SectorQuadratic

/-! # Euclidean sectors spanned by rays of linear separation -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction Set

variable {X : Type*} [MetricSpace X]

/-- The pullback of ambient distance between points of the ray sector is a seminorm. -/
theorem sectorMap_ray_seminorm (g : IsGeodesic X) (hB : SectorBusemann X)
    {a b : ℝ → X} {A B c : ℝ}
    (ha : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → dist (a r) (a s) = |r-s| * A)
    (hb : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → dist (b r) (b s) = |r-s| * B)
    (hsep : ∀ r : ℝ, 0 ≤ r → dist (a r) (b r) = r*c) :
    ∃ N : Seminorm ℝ (ℝ × ℝ), ∀ p q, 0 ≤ p → 0 ≤ q →
      dist (sectorMap g a b p) (sectorMap g a b q) = N (p - q) := by
  let H := sectorMap g a b
  have hdom {p : ℝ × ℝ} (hp : 0 ≤ p) : p ∈ sectorDomain (Ici 0) :=
    ⟨hp.1, hp.2, add_nonneg hp.1 hp.2⟩
  have hfrac (p q : ℝ × ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) {t : ℝ} (ht : t ∈ Icc 0 1) :
      SectorFraction (H p) (H q) (H ((1-t) • p + t • q)) t := by
    change SectorFraction _ _ (sectorMap g a b _) _
    rw [sectorMap_affine g hB (convex_Ici (0 : ℝ))
      (fun r hr s hs ↦ ha r s hr hs) (fun r hr s hs ↦ hb r s hr hs)
      (fun r hr ↦ (hsep r hr).trans (mul_comm r c)) (hdom hp) (hdom hq) ht]
    exact sectorSegment_fraction g _ _ ht
  apply quadrant_seminorm_of_affine H
  · exact fun p q hp hq _ ht ↦ (hfrac p q hp hq ht).1
  · intro z p q hz hp hq t ht
    simpa using hB _ _ _ _ _ _ t ht (hfrac z p hz hp ht) (hfrac z q hz hq ht)

/-- Linear separation of two Busemann rays gives the Euclidean law of cosines
when every finitely realized normed space obeys spectral norm rigidity. -/
theorem quadraticRaySectors_of_normRigidity (g : IsGeodesic X)
    (hB : SectorBusemann X) (hX : SectorNormRigidity X) : QuadraticRaySectors X := by
  intro a b A B c ho ha hb hsep t ht
  let H := sectorMap g a b
  obtain ⟨N, hN⟩ := sectorMap_ray_seminorm g hB ha hb hsep
  change ∀ p q, 0 ≤ p → 0 ≤ q → dist (H p) (H q) = N (p-q) at hN
  have haxes (r : ℝ) (hr : 0 ≤ r) : H (r,0) = a r ∧ H (0,r) = b r :=
    sectorMap_axes g (D := Ici 0) (fun s hs ↦ (hsep s hs).trans (mul_comm s c)) hr hr
  have hzero : H 0 = a 0 := (haxes 0 le_rfl).1
  let e : ℝ × ℝ := (1,0)
  let f : ℝ × ℝ := (0,1)
  have he : 0 ≤ e := ⟨zero_le_one, le_rfl⟩
  have hf : 0 ≤ f := ⟨le_rfl, zero_le_one⟩
  have ha₁ : N e = A := by
    have hh := hN e 0 he le_rfl
    rw [sub_zero] at hh
    rw [←hh, (haxes 1 zero_le_one).1, hzero, ha 1 0 zero_le_one le_rfl]
    norm_num
  have hb₁ : N f = B := by
    have hh := hN f 0 hf le_rfl
    rw [sub_zero] at hh
    rw [←hh, (haxes 1 zero_le_one).2, hzero, ho, hb 1 0 zero_le_one le_rfl]
    norm_num
  have hc₁ : N (e-f) = c := by
    rw [← hN _ _ he hf, (haxes 1 zero_le_one).1, (haxes 1 zero_le_one).2, hsep 1 zero_le_one,
      one_mul]
  have hte : t • e = (t,0) := by simp [e]
  have hdiag := quadrant_seminorm_sq_of_rigidity hX H N hN e f t 1
  simp only [one_smul, one_pow, one_mul, mul_one] at hdiag
  rw [←hN _ _ (smul_nonneg ht.le he) hf, hte, (haxes t ht.le).1, (haxes 1 zero_le_one).2,
    ha₁, hb₁, hc₁] at hdiag
  simpa only [mul_pow] using hdiag

end SpectralBooks
end LinearAlgebra
end OAI
