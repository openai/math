import OAI.LinearAlgebra.SpectralBooks.SectorChord
import OAI.LinearAlgebra.SpectralBooks.SectorBoundary

/-!
# A seminorm from parallel chords of a convex domain

An interior neighborhood contains a homothetic copy of each finite
configuration. Proportionality for parallel chords makes the rescaled distance
independent of the copy and turns the triangle inequality into subadditivity.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set Topology

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace X]

private theorem seminorm_of_interior_chords {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    (H : E → X)
    (hchord : ∀ {p q r s : E}, p ∈ U → q ∈ U → r ∈ U → s ∈ U →
      ∀ {c : ℝ}, 0 < c → q - p = c • (s - r) → dist (H p) (H q) = c * dist (H r) (H s)) :
    ∃ N : Seminorm ℝ E, ∀ p ∈ U, ∀ q ∈ U, dist (H p) (H q) = N (p - q) := by
  classical
  obtain ⟨o, ho⟩ := hne
  have shrink (v : E) : ∀ᶠ t : ℝ in 𝓝[>] 0, o + t • v ∈ U := by
    have hlim : Tendsto (fun t : ℝ ↦ o + t • v) (𝓝[>] 0) (𝓝 o) := by
      simpa using ((tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).smul_const v).const_add o
    exact hlim (hU.mem_nhds ho)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  choose k hk hkU using fun v ↦ (hpos.and (shrink v)).exists
  let f (v : E) := dist (H o) (H (o + k v • v)) / k v
  have rep {p q : E} (hp : p ∈ U) (hq : q ∈ U) {c : ℝ} (hc : 0 < c) (v : E)
      (he : q - p = c • v) : dist (H p) (H q) = c * f v := by
    calc
      _ = (c / k v) * dist (H o) (H (o + k v • v)) := by
        apply hchord hp hq ho (hkU v) (div_pos hc (hk v))
        rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ (hk v).ne', he]
      _ = _ := by dsimp [f]; ring
  have fzero : f 0 = 0 := by simp [f]
  have fneg (v : E) : f (-v) = f v := by
    have h := rep (hkU v) ho (hk v) (-v) (by simp)
    rw [dist_comm, rep ho (hkU v) (hk v) v (by simp)] at h
    exact (mul_left_cancel₀ (hk v).ne' h).symm
  have fpos (a : ℝ) (ha : 0 < a) (v : E) : f (a • v) = a * f v := by
    let t := k (a • v)
    have ht : 0 < t := hk _
    have h : o + t • (a • v) ∈ U := hkU _
    have hd := rep ho h ht (a • v) (by simp)
    rw [rep ho h (mul_pos ht ha) v (by rw [add_sub_cancel_left, smul_smul]), mul_assoc] at hd
    exact (mul_left_cancel₀ ht.ne' hd).symm
  have fadd (v w : E) : f (v + w) ≤ f v + f w := by
    obtain ⟨t, ht, hv, hvw⟩ := (hpos.and ((shrink v).and (shrink (v+w)))).exists
    have hd := dist_triangle (H o) (H (o+t • v)) (H (o+t • (v+w)))
    rw [rep ho hvw ht (v+w) (by simp), rep ho hv ht v (by simp),
      rep hv hvw ht w (by simp [smul_add]), ← mul_add] at hd
    exact le_of_mul_le_mul_left hd ht
  refine ⟨Seminorm.of f fadd (fun a v ↦ ?_), fun p hp q hq ↦ ?_⟩
  · rcases lt_trichotomy a 0 with ha | rfl | ha
    · have h := fpos (-a) (neg_pos.mpr ha) v
      rw [neg_smul, fneg] at h
      simpa [Real.norm_eq_abs, abs_of_neg ha] using h
    · simp [fzero]
    · rw [Real.norm_of_nonneg ha.le, fpos a ha]
  · change dist (H p) (H q) = f (p-q)
    rw [dist_comm]
    simpa using rep hq hp zero_lt_one (p-q) (by simp)

/-- A constant-speed affine parametrization of a convex domain with nonempty
interior in a Busemann convex space induces a seminorm on its difference space. -/
theorem convex_seminorm_of_affine {C : Set E} (hC : Convex ℝ C)
    (hI : (interior C).Nonempty) (H : E → X)
    (hseg : ∀ p ∈ C, ∀ q ∈ C, ∀ t : ℝ, t ∈ Icc 0 1 →
      dist (H p) (H ((1 - t) • p + t • q)) = t * dist (H p) (H q))
    (hcon : ∀ z ∈ C, ∀ p ∈ C, ∀ q ∈ C, ∀ t : ℝ, t ∈ Icc 0 1 →
      dist (H ((1-t) • z + t • p)) (H ((1-t) • z + t • q)) ≤ t * dist (H p) (H q)) :
    ∃ N : Seminorm ℝ E, ∀ p ∈ C, ∀ q ∈ C, dist (H p) (H q) = N (p-q) := by
  obtain ⟨N, hN⟩ := seminorm_of_interior_chords isOpen_interior hI H
    (fun {_ _ _ _} hp hq hr hs {_} hc he ↦ convex_chord_dist_eq H hseg hcon hp (interior_subset hq)
      hr (interior_subset hs) hc he)
  exact ⟨N, convex_chord_dist_boundary hC hI H hseg N hN⟩

end SpectralBooks
end LinearAlgebra
end OAI
