import OAI.Computability.BorderVNP.BranchRationalDegree
import OAI.Computability.BorderVNP.BranchCurveGraphDimension
import OAI.Computability.BorderVNP.BranchFiberPins

/-!
# A finite cut of the graph fiber with short coefficients

The rational graph chart has a common denominator of degree one. Effective separation
therefore defines its fiber above the prescribed coefficients by equations of bounded
degree in the homogeneous parameter coordinates alone. Noetherianity lets us use a finite
subset of these equations without increasing their degree. Short coordinate pins in a
finite subfield then give a finite, nonempty fiber by the one-parameter Macaulay test.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP.RadicalCertificate VPVNP.SliceGeometry

variable {h : ℕ} {ι K : Type*} [Field K] [IsAlgClosed K] [Fintype ι]

/-- An effective degree cutoff for all graph fiber equations. -/
def graphFiberDegree (h d : ℕ) : ℕ := max 3 (2 * perronSimplexBound (h + 2) (d + 3))

/-- The fiber in standard chart `k`, listing the homogeneous parameters in finite order. -/
def graphFiber (Y : ι → MvPolynomial (Fin h) K) (c : ι → K) (k : Option (Fin h)) :
    Set (Fin (h+1) → K) :=
  {z | Sum.elim (z ∘ (_root_.finSuccEquiv h).symm) c ∈ zeroLocus K (RingHom.ker (graphChartMap Y k))}

private theorem bounded_chart_equations (Y : ι → MvPolynomial (Fin h) K) (d : ℕ)
    (hY : ∀ i, (Y i).totalDegree ≤ d) (k : Option (Fin h))
    (hk : homogeneousParameters (Fin h) K k ≠ 0) (w : Option (Fin h) ⊕ ι → K)
    (hw : w ∉ zeroLocus K (RingHom.ker (graphChartMap Y k))) :
    ∃ p : MvPolynomial (Option (Fin h) ⊕ ι) K, p.totalDegree ≤ graphFiberDegree h d ∧
      graphChartMap Y k p = 0 ∧ eval w p = 1 := by
  let inc := algebraMap (MvPolynomial (Fin h) K) (ParameterField (Fin h) K)
  let u : Option (Fin h) → MvPolynomial (Fin h) K := fun i => i.elim 1 X
  have ui (j : Option (Fin h)) : inc (u j) = homogeneousParameters (Fin h) K j := by
    cases j <;> simp [u, homogeneousParameters, inc]
  let b := u k
  let a : Option (Fin h) ⊕ ι → MvPolynomial (Fin h) K := Sum.elim u (fun i => Y i * b)
  have hden : inc b ≠ 0 := (ui k) ▸ hk
  have hb : b ≠ 0 := fun e => hden (by rw [e, map_zero])
  have hud (j : Option (Fin h)) : (u j).totalDegree ≤ 1 := by cases j <;> simp [u]
  have had (j) : (a j).totalDegree ≤ d+1 := by
    cases j with
    | inl j => exact (hud j).trans (by omega)
    | inr i => exact (totalDegree_mul ..).trans (Nat.add_le_add (hY i) (hud k))
  have eq (p : MvPolynomial (Option (Fin h) ⊕ ι) K) :
      aeval (fun j => inc (a j) / inc b) p = graphChartMap Y k p := by
    rw [← graphChartAlgHom_toRingHom]
    change aeval _ p = aeval _ p
    congr 2
    funext j
    cases j with
    | inl j => exact congrArg₂ (· / ·) (ui j) (ui k)
    | inr i =>
      change inc (Y i * b) / inc b = inc (eval₂Hom C Y (X i))
      rw [map_mul, mul_div_cancel_right₀ _ hden, eval₂Hom_X']
  rw [mem_zeroLocus_iff] at hw
  push Not at hw
  obtain ⟨q, hq, hqw⟩ := hw
  obtain ⟨p, hp, hz, he⟩ := bounded_rational_separator b a w hb ((hud k).trans (by omega)) had q
    (by rw [eq]; exact hq) (by simpa using hqw)
  exact ⟨p, hp.trans (le_max_right ..), (eq p) ▸ hz, he⟩

/-- The geometric fiber has bounded-degree defining equations in the chart coordinates
only. The number of outputs affects neither the degree cutoff nor the number of
variables in the returned polynomials. -/
theorem graphFiber_equations (Y : ι → MvPolynomial (Fin h) K) (c : ι → K) (d : ℕ)
    (hY : ∀ i, (Y i).totalDegree ≤ d) (k : Option (Fin h))
    (hk : homogeneousParameters (Fin h) K k ≠ 0) :
    ∃ S : Finset (MvPolynomial (Fin (h+1)) K),
      (∀ q ∈ S, q.totalDegree ≤ graphFiberDegree h d) ∧
      graphFiber Y c k = {z | ∀ q ∈ S, eval z q = 0} := by
  classical
  let g : Option (Fin h) ⊕ ι → MvPolynomial (Fin (h+1)) K :=
    Sum.elim (fun j => X ((_root_.finSuccEquiv h).symm j)) (fun i => C (c i))
  let P := {p : MvPolynomial (Option (Fin h) ⊕ ι) K |
    p.totalDegree ≤ graphFiberDegree h d ∧ graphChartMap Y k p = 0}
  let U := aeval g '' P
  have evalg (z : Fin (h+1) → K) (p : MvPolynomial (Option (Fin h) ⊕ ι) K) :
      eval z (aeval g p) = eval (Sum.elim (z ∘ (_root_.finSuccEquiv h).symm) c) p := by
    rw [map_aeval]
    have idc : (eval z).comp (algebraMap K (MvPolynomial (Fin (h+1)) K)) = RingHom.id K := by
      ext x; simp
    rw [idc]
    change eval₂Hom (RingHom.id K) _ p = eval₂Hom (RingHom.id K) _ p
    congr 2
    funext j; cases j <;> simp [g]
  have hu : graphFiber Y c k = zeroLocus K (Ideal.span U) := by
    ext z
    rw [zeroLocus_span]
    change (_ ∈ zeroLocus K _) ↔ ∀ q ∈ U, aeval z q = 0
    constructor
    · intro hz q hq
      obtain ⟨p, hp, rfl⟩ := hq
      simpa only [aeval_eq_eval, evalg] using hz p hp.2
    · intro hall
      by_contra hz
      obtain ⟨p, hp, he, h1⟩ := bounded_chart_equations Y d hY k hk _ hz
      have := hall (aeval g p) ⟨p, ⟨hp, he⟩, rfl⟩
      rw [aeval_eq_eval, evalg, h1] at this
      exact one_ne_zero this
  obtain ⟨S, hsub, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset U).mp
    (IsNoetherian.noetherian (Ideal.span U))
  refine ⟨S, fun q hq => ?_, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := hsub hq
    exact (totalDegree_affine_substitution p g (fun i => by cases i <;> simp [g])).trans hp.1
  · rw [hu, show Ideal.span U = Ideal.span (↑S : Set _) from hs, zeroLocus_span]
    simp [aeval_eq_eval]

/-- A genuine image-closure point has a finite nonempty chart fiber after coordinate
pinning. All added hyperplane constants belong to a finite extension of the displayed
size, even when the output vector has exponentially many coordinates. -/
theorem exists_short_pinned_graphFiber (E₀ : Type*) [Field E₀] [Fintype E₀] [Algebra E₀ K]
    (Y : ι → MvPolynomial (Fin h) K) (c : ι → K) (d : ℕ) (hY : ∀ i, (Y i).totalDegree ≤ d)
    (hc : c ∈ imageClosure (Set.range (fun a : Fin h → K => fun i => eval a (Y i)))) :
    ∃ (k : Option (Fin h)) (E : IntermediateField E₀ K),
      homogeneousParameters (Fin h) K k ≠ 0 ∧ Finite E ∧
      Nat.card E ≤ Fintype.card E₀ * max (fiberPinBound (h+1) (graphFiberDegree h d)) 1 ∧
      ∃ (s : Finset (Fin (h+1))) (a : Fin (h+1) → E),
        let V := pinnedPoints (graphFiber Y c k) s a
        V.Nonempty ∧ V.Finite ∧ V.ncard ≤ fiberPinBound (h+1) (graphFiberDegree h d) ^ (h+1) := by
  classical
  obtain ⟨k, z, hk, _, hz⟩ := exists_graphChart_point Y c hc
  obtain ⟨S, hS, he⟩ := graphFiber_equations Y c d hY k hk
  have hmem : z ∘ (_root_.finSuccEquiv h) ∈ graphFiber Y c k := by
    change Sum.elim ((z ∘ (_root_.finSuccEquiv h)) ∘ (_root_.finSuccEquiv h).symm) c ∈ zeroLocus K (RingHom.ker (graphChartMap Y k))
    simpa [Function.comp_assoc] using hz
  have hv : graphFiber Y c k = {x | ∀ q : S, eval x q.val = 0} := by simp [he]
  rw [hv] at hmem
  obtain ⟨E, hf, hbound, hcut⟩ := exists_small_fiber_pins E₀ K (d := graphFiberDegree h d)
    (le_max_left ..) (fun q : S => q.val) (fun q => hS _ q.property) ⟨_, hmem⟩
  exact ⟨k, E, hk, hf, hbound, hv ▸ hcut⟩

end Branch

end BorderVNP
end Computability
end OAI
