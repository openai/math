import OAI.LinearAlgebra.SpectralBooks.TriangleSpan
import OAI.LinearAlgebra.SpectralBooks.TriangleWidth
import OAI.LinearAlgebra.SpectralBooks.PriceContinuity
import OAI.LinearAlgebra.SpectralBooks.TriangleAdditivity

/-! # From triangle support density to the homogeneous flat diagonal law

Subtracting Gaussian mean width from the price leaves a function unchanged by
addition of triangles. Every linear combination of triangle support functions is
the difference of support functions of two finite Minkowski sums of triangles.
The Lipschitz bound in the support norm then determines the price on every
polytope.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Metric MeasureTheory ProbabilityTheory Filter
open scoped Pointwise Classical Topology

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def InvariantUnder (D : (S : Finset E) → S.Nonempty → ℝ)
    (P : Finset E) (hP : P.Nonempty) : Prop :=
  ∀ (S : Finset E) (hS : S.Nonempty), D (S + P) (hS.add hP) = D S hS

omit [InnerProductSpace ℝ E] in
private theorem invariantUnder_zero (D : (S : Finset E) → S.Nonempty → ℝ) :
    InvariantUnder D {0} (Finset.singleton_nonempty _) := by
  intro S hS
  simp [show ({0} : Finset E) = 0 from rfl]

omit [InnerProductSpace ℝ E] in
private theorem invariantUnder_add {D : (S : Finset E) → S.Nonempty → ℝ}
    {P Q : Finset E} {hP : P.Nonempty} {hQ : Q.Nonempty}
    (hp : InvariantUnder D P hP) (hq : InvariantUnder D Q hQ) :
    InvariantUnder D (P + Q) (hP.add hQ) := by
  intro S hS
  simpa only [add_assoc] using (hq (S + P) (hS.add hP)).trans (hp S hS)

private theorem span_difference_of_triangles (D : (S : Finset E) → S.Nonempty → ℝ)
    (htri : ∀ a b c : E, InvariantUnder D {a, b, c} (Finset.insert_nonempty _ _))
    {f : C(sphere (0 : E) 1, ℝ)} (hf : f ∈ Submodule.span ℝ (triangleSupports E)) :
    ∃ (P M : Finset E) (hP : P.Nonempty) (hM : M.Nonempty),
      InvariantUnder D P hP ∧ InvariantUnder D M hM ∧
        f = sphereSupport P hP - sphereSupport M hM := by
  induction hf using Submodule.closure_induction with
  | zero =>
    refine ⟨{0}, {0}, _, _, invariantUnder_zero D, invariantUnder_zero D, ?_⟩
    simp
  | add x y _ _ hx hy =>
    obtain ⟨P, M, hP, hM, p, m, rfl⟩ := hx
    obtain ⟨Q, N, hQ, hN, q, n, rfl⟩ := hy
    refine ⟨P + Q, M + N, hP.add hQ, hM.add hN, invariantUnder_add p q, invariantUnder_add m n, ?_⟩
    rw [sphereSupport_add P Q hP hQ, sphereSupport_add M N hM hN]
    abel
  | smul_mem r g hg =>
    obtain ⟨a, b, c, rfl⟩ := hg
    let T : Finset E := {a, b, c}
    have hT : T.Nonempty := Finset.insert_nonempty _ _
    have scaled (s : ℝ) (hs : 0 ≤ s) :
        s • sphereSupport T hT =
          sphereSupport {s • a, s • b, s • c} (Finset.insert_nonempty _ _) := by
      ext u
      have h := support_smul T hT (u : E) hs
      change s * support T hT (u : E) = support {s • a, s • b, s • c} (Finset.insert_nonempty _ _) (u : E)
      simpa [T, Finset.image_insert] using h.symm
    by_cases hr : 0 ≤ r
    · refine ⟨{r • a, r • b, r • c}, {0}, _, _, htri _ _ _, invariantUnder_zero D, ?_⟩
      rw [sphereSupport_zero, sub_zero]
      exact scaled r hr
    · refine ⟨{0}, {-r • a, -r • b, -r • c}, _, _, invariantUnder_zero D, htri _ _ _, ?_⟩
      rw [sphereSupport_zero, zero_sub, ← scaled (-r) (by linarith)]
      simp [T]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Triangle additivity identifies a support-Lipschitz price on the homogeneous
flat once the continuous triangle supports have dense linear span. -/
theorem price_eq_meanWidth_of_dense_triangleSupports
    (hdense : Dense (Submodule.span ℝ (triangleSupports E) : Set C(sphere (0 : E) 1, ℝ)))
    (δ : Finset E → ℝ)
    (htriangle : ∀ a b c : E, δ {a, b, c} = (dist a b + dist b c + dist c a) / 2)
    (hadd : ∀ (S : Finset E), S.Nonempty → ∀ a b c : E,
      δ (S + {a, b, c}) = δ S + δ {a, b, c})
    (hL : ∃ C : ℝ, ∀ ε > 0, ∀ S T : Finset E, ∀ hS : S.Nonempty, ∀ hT : T.Nonempty,
      (∀ u ∈ sphere (0 : E) 1, |support S hS u - support T hT u| ≤ ε) →
        |δ S - δ T| ≤ C * ε)
    (S : Finset E) (hS : S.Nonempty) :
    δ S = meanWidth S hS := by
  let D (P : Finset E) (hP : P.Nonempty) := δ P - meanWidth P hP
  have tri (a b c : E) : InvariantUnder D {a, b, c} (Finset.insert_nonempty _ _) := by
    intro Q hQ
    simp only [D, hadd Q hQ, htriangle, meanWidth_add Q _ hQ (Finset.insert_nonempty _ _),
      meanWidth_triangle]
    ring
  have h0 : D {0} (Finset.singleton_nonempty _) = 0 := by
    have hp := htriangle (0 : E) 0 0
    have hw := meanWidth_triangle (0 : E) 0 0
    simp at hp hw
    simp [D, hp, hw]
  obtain ⟨C, hC⟩ := hL
  let A := Real.sqrt (2 * Real.pi) * ∫ u : E, ‖u‖ ∂stdGaussian E
  have hbound (ε : ℝ) (hε : 0 < ε) : |D S hS| ≤ (C + A) * ε := by
    obtain ⟨g, hg, hd⟩ := Metric.mem_closure_iff.mp (hdense (sphereSupport S hS)) ε hε
    obtain ⟨P, M, hP, hM, p, m, rfl⟩ := span_difference_of_triangles D tri hg
    have hclose (u : E) (hu : u ∈ sphere (0 : E) 1) :
        |support (S + M) (hS.add hM) u - support P hP u| ≤ ε := by
      let v : sphere (0 : E) 1 := ⟨u, hu⟩
      rw [dist_eq_norm] at hd
      have h := ((sphereSupport S hS - (sphereSupport P hP - sphereSupport M hM)).norm_coe_le_norm v).trans hd.le
      change |support S hS u - (support P hP u - support M hM u)| ≤ ε at h
      rw [support_add S M hS hM]
      convert h using 2
      ring
    have hp : D P hP = 0 := by
      have h := (p {0} (Finset.singleton_nonempty _)).trans h0
      simpa only [show ({0} : Finset E) = 0 from rfl, zero_add] using h
    have hm := m S hS
    have hpclose := hC ε hε (S + M) P (hS.add hM) hP hclose
    have hwclose := abs_meanWidth_sub_le (S + M) P (hS.add hM) hP hclose
    calc
      |D S hS| = |(δ (S + M) - δ P) -
          (meanWidth (S + M) (hS.add hM) - meanWidth P hP)| := by
        rw [← hm]
        unfold D at hp ⊢
        congr 1
        linarith
      _ ≤ _ := by
        rw [add_mul]
        exact (abs_sub _ _).trans (add_le_add hpclose hwclose)
  have hz : |D S hS| ≤ 0 := by
    apply ge_of_tendsto (x := 𝓝[>] (0 : ℝ)) (f := fun ε ↦ (C + A) * ε)
    · simpa using (tendsto_const_nhds (x := C + A)).mul
        (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
    · exact Filter.Eventually.mono self_mem_nhdsWithin fun ε hε ↦ hbound ε hε
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

/-- For a homogeneous price, wire normalization and the half-perimeter upper
bound suffice for the flat diagonal law. The three edge segments of a triangle
sum to its difference body, forcing the upper bound to be attained. -/
theorem homogeneousFlatLaw_of_triangle_le
    (δ : Finset E → ℝ) (hjoint : JointlyConvexPrice δ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsubmod : IntersectingSubmodular δ)
    (hscale : ∀ (S : Finset E), S.Nonempty → ∀ r : ℝ, 0 < r →
      δ (S.image (r • ·)) = r * δ S)
    (hpair : ∀ a b : E, δ {a, b} = dist a b)
    (hupper : ∀ a b c : E, δ {a, b, c} ≤ (dist a b + dist b c + dist c a) / 2)
    (S : Finset E) (hS : S.Nonempty) :
    δ S = meanWidth S hS := by
  have hsingle (x : E) : δ {x} = 0 := by simpa using hpair x x
  have hsum := price_add_le_of_jointConvex δ hjoint hscale
  have htrans := price_translate_of_add_le δ hsum hsingle
  have hseg := price_add_segment δ hmono htrans hsubmod hsum hpair
  have htriangle (a b c : E) : δ {a, b, c} = (dist a b + dist b c + dist c a) / 2 := by
    apply le_antisymm (hupper a b c)
    have hab : ({0, b - a} : Finset E).Nonempty := Finset.insert_nonempty _ _
    have hbc : ({0, c - b} : Finset E).Nonempty := Finset.insert_nonempty _ _
    have hbody : δ (({a, b, c} : Finset E) + {-a, -b, -c}) =
        dist a b + dist b c + dist c a := by
      rw [triangle_add_neg_eq_segments, hseg _ (hab.add hbc), hseg _ hab, hpair]
      simp [dist_eq_norm']
    have hbound := hsum {a, b, c} {-a, -b, -c} (Finset.insert_nonempty _ _) (Finset.insert_nonempty _ _)
    rw [hbody] at hbound
    have hneg := hupper (-a) (-b) (-c)
    simp only [dist_neg_neg] at hneg
    linarith
  exact price_eq_meanWidth_of_dense_triangleSupports dense_span_triangleSupports δ htriangle
    (price_add_triangle δ hsum hseg htriangle)
    (exists_price_lipschitz_of_jointConvex δ hjoint hmono hscale) S hS

/-- The homogeneous case of the flat diagonal law follows from triangle density,
joint convexity, monotonicity, intersecting submodularity and the planar law. -/
theorem homogeneousFlatLaw
    (δ : Finset E → ℝ) (hjoint : JointlyConvexPrice δ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsubmod : IntersectingSubmodular δ)
    (hscale : ∀ (S : Finset E), S.Nonempty → ∀ r : ℝ, 0 < r →
      δ (S.image (r • ·)) = r * δ S)
    (htriangle : ∀ a b c : E, δ {a, b, c} = (dist a b + dist b c + dist c a) / 2)
    (S : Finset E) (hS : S.Nonempty) :
    δ S = meanWidth S hS := by
  apply homogeneousFlatLaw_of_triangle_le δ hjoint hmono hsubmod hscale _ _ S hS
  · intro a b
    simpa [dist_comm b a] using htriangle a b b
  · exact fun a b c ↦ (htriangle a b c).le

end

end SpectralBooks
end LinearAlgebra
end OAI
