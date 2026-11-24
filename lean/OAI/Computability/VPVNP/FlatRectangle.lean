import OAI.Computability.VPVNP.CATZeroEquality
import OAI.Computability.VPVNP.FlatTriangleVariation
import OAI.Computability.VPVNP.GrassmannGeometry

/-!
# Interpolating the sides of a flat rectangle

A four-point configuration with the distances of a Euclidean rectangle
extends across each pair of parallel sides with exactly the Euclidean
cross distances. The proof uses the midpoint inequality on a saturated
diagonal and the first variation of squared distance to exchange the two
sides of a flat triangle. This gives the rectangle-filling step in
Sections 4.2 and 5.4 directly from the squared CAT(0) segment inequality.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {X : Type*} [MetricSpace X]

private theorem comparison_lower {a b c z : X} (h : HasCATZeroSegments X) {s : ℝ}
    (hs : 0 ≤ s) (haz : dist a z = s * dist a b) (hbz : dist b z = (1 - s) * dist a b)
    (hflat : ∀ t : Set.Icc (0 : ℝ) 1, dist b (catPoint h a c t) ^ 2 =
      (1 - t.val) * dist b a ^ 2 + t.val * dist b c ^ 2 - t.val * (1 - t.val) * dist a c ^ 2) :
    (1 - s) * dist c a ^ 2 + s * dist c b ^ 2 - s * (1 - s) * dist a b ^ 2 ≤ dist c z ^ 2 := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · have : a = z := dist_eq_zero.mp (by simpa using haz)
    simp [this]
  rcases eq_or_lt_of_le (dist_nonneg (x := a) (y := b)) with hL | hL
  · have hab := dist_eq_zero.mp hL.symm
    have haz' := dist_eq_zero.mp (by simpa [hL.symm] using haz)
    subst b
    subst z
    simp
    linarith
  let L := dist a b
  let H := dist a c ^ 2
  let k := dist b c ^ 2 - L ^ 2 - H
  let k' := dist z c ^ 2 - (s * L) ^ 2 - H
  have hv : s * k ≤ k' := flatTriangle_firstVariation (L := L) (H2 := H) hL hs (by
    intro t ht ht'
    let u : Set.Icc (0 : ℝ) 1 := ⟨t, ht.le, ht'⟩
    let p := catPoint h a c u
    refine ⟨dist b p, dist z p, dist_nonneg, dist_nonneg, ?_, ?_, ?_⟩
    · have he := hflat u
      rw [dist_comm b a] at he
      dsimp only [L, k, H, p, u] at *
      linarith only [he]
    · have he := catPoint_bound h a c u z
      rw [dist_comm z a, haz] at he
      dsimp only [L, k', H, p, u] at *
      linarith only [he]
    · simpa only [hbz, L] using dist_triangle b z p)
  rw [dist_comm c z, dist_comm c b, dist_comm c a]
  dsimp only [k, k', L, H] at hv
  linarith only [hv]

private theorem diagonal_flat (h : HasCATZeroSegments X) (a b c d : X)
    (heq : dist a c ^ 2 + dist b d ^ 2 =
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2)
    (t : Set.Icc (0 : ℝ) 1) :
    dist b (catPoint h a c t) ^ 2 =
      (1 - t.val) * dist b a ^ 2 + t.val * dist b c ^ 2 - t.val * (1 - t.val) * dist a c ^ 2 := by
  let u : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  let p := catPoint h a c u
  have hb := catPoint_bound h a c u b
  have hd := catPoint_bound h a c u d
  have htri : dist b d ^ 2 ≤ (dist b p + dist d p) ^ 2 := by
    apply (sq_le_sq₀ dist_nonneg (add_nonneg dist_nonneg dist_nonneg)).mpr
    simpa only [dist_comm p d] using dist_triangle b p d
  have hmid : dist b p ^ 2 = (1 - u.val) * dist b a ^ 2 + u.val * dist b c ^ 2 -
      u.val * (1 - u.val) * dist a c ^ 2 := by
    rw [dist_comm c d, dist_comm a b] at heq
    dsimp only [p, u] at *
    nlinarith only [heq, hb, hd, htri, sq_nonneg (dist b (catPoint h a c u) - dist d (catPoint h a c u))]
  exact catPoint_bound_eq_of_interior h a c b u (by norm_num [u]) (by norm_num [u]) hmid t

private theorem rectangle_vertex (h : HasCATZeroSegments X) {a b d c : X} {L W : ℝ}
    (hab : dist a b ^ 2 = L) (hdc : dist d c ^ 2 = L)
    (had : dist a d ^ 2 = W) (hbc : dist b c ^ 2 = W)
    (hac : dist a c ^ 2 = L + W) (hbd : dist b d ^ 2 = L + W)
    (s : Set.Icc (0 : ℝ) 1) :
    dist c (catPoint h a b s) ^ 2 = L * (1 - s.val) ^ 2 + W ∧
    dist d (catPoint h a b s) ^ 2 = L * s.val ^ 2 + W := by
  have hab' : dist b a ^ 2 = L := (congrArg (· ^ 2) (dist_comm b a)).trans hab
  have hdc' : dist c d ^ 2 = L := (congrArg (· ^ 2) (dist_comm c d)).trans hdc
  have had' : dist d a ^ 2 = W := (congrArg (· ^ 2) (dist_comm d a)).trans had
  have hbc' : dist c b ^ 2 = W := (congrArg (· ^ 2) (dist_comm c b)).trans hbc
  have hac' : dist c a ^ 2 = L + W := (congrArg (· ^ 2) (dist_comm c a)).trans hac
  have hbd' : dist d b ^ 2 = L + W := (congrArg (· ^ 2) (dist_comm d b)).trans hbd
  have hL := dist_left_catPoint h a b s
  have hR := dist_right_catPoint h a b s
  have hlow₁ := comparison_lower h s.property.1 hL hR
    (diagonal_flat h a b c d (by linarith only [hab, hbc, hdc', had', hac, hbd]))
  have hlow₂ := comparison_lower (a := b) (b := a) (s := 1 - s.val) h (sub_nonneg.mpr s.property.2)
    (by simpa only [dist_comm b a] using hR)
    (by simpa only [sub_sub_cancel, dist_comm b a] using hL)
    (diagonal_flat h b a d c (by linarith only [hab', had, hdc, hbc', hbd, hac]))
  have hup₁ := catPoint_bound h a b s c
  have hup₂ := catPoint_bound h a b s d
  rw [hac', hbc', hab] at hlow₁ hup₁
  rw [hbd', had', hab'] at hlow₂
  rw [had', hbd', hab] at hup₂
  constructor <;> linarith only [hlow₁, hlow₂, hup₁, hup₂]

/-- Euclidean cross distances on the two interpolated parallel sides of a
rectangle, including rectangles of zero width or length. -/
theorem rectangle_interpolate (h : HasCATZeroSegments X) {a b d c : X} {L W : ℝ}
    (hab : dist a b ^ 2 = L) (hdc : dist d c ^ 2 = L)
    (had : dist a d ^ 2 = W) (hbc : dist b c ^ 2 = W)
    (hac : dist a c ^ 2 = L + W) (hbd : dist b d ^ 2 = L + W)
    (s t : Set.Icc (0 : ℝ) 1) :
    dist (catPoint h a b s) (catPoint h d c t) ^ 2 = L * (s.val - t.val) ^ 2 + W := by
  let e := catPoint h a b s
  let f := catPoint h d c s
  have had' : dist d a ^ 2 = W := (congrArg (· ^ 2) (dist_comm d a)).trans had
  have hbc' : dist c b ^ 2 = W := (congrArg (· ^ 2) (dist_comm c b)).trans hbc
  have hac' : dist c a ^ 2 = L + W := (congrArg (· ^ 2) (dist_comm c a)).trans hac
  have hbd' : dist d b ^ 2 = L + W := (congrArg (· ^ 2) (dist_comm d b)).trans hbd
  have rev (u : Set.Icc (0 : ℝ) 1) := rectangle_vertex h hdc hab had' hbc' hbd' hac' u
  rcases eq_or_lt_of_le s.property.1 with hs | hs
  · have heq : s = 0 := Subtype.ext hs.symm
    rw [heq, catPoint_zero]
    simpa using (rev t).2
  rcases eq_or_lt_of_le s.property.2 with hs' | hs'
  · have heq : s = 1 := Subtype.ext hs'
    rw [heq, catPoint_one]
    simpa using (rev t).1
  obtain ⟨hc, hd⟩ := rectangle_vertex h hab hdc had hbc hac hbd s
  change dist c e ^ 2 = _ at hc
  change dist d e ^ 2 = _ at hd
  rw [dist_comm c e] at hc
  rw [dist_comm d e] at hd
  have hf : dist a f ^ 2 = L * s.val ^ 2 + W := (rev s).2
  have he' : dist a e ^ 2 = s.val ^ 2 * L := by
    rw [dist_left_catPoint, mul_pow, hab]
  have hf' : dist f d ^ 2 = s.val ^ 2 * L := by
    rw [dist_comm f d, dist_left_catPoint, mul_pow, hdc]
  have hquad := quadrilateral_sq h a e f d
  rw [hf, hd, he', hf', had'] at hquad
  have hup := catPoint_bound h d c s e
  change dist e f ^ 2 ≤ _ at hup
  rw [hc, hd, hdc] at hup
  have heq : dist e f ^ 2 = W := by linarith only [hquad, hup]
  have hmid : dist e f ^ 2 = (1 - s.val) * dist e d ^ 2 + s.val * dist e c ^ 2 -
      s.val * (1 - s.val) * dist d c ^ 2 := by rw [heq, hc, hd, hdc]; ring
  have ht := catPoint_bound_eq_of_interior h d c e s hs hs' hmid t
  rw [hd, hc, hdc] at ht
  change dist e (catPoint h d c t) ^ 2 = _
  linarith only [ht]

end SpectralGeometry

end VPVNP
end Computability
end OAI
