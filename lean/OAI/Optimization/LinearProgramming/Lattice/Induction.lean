import OAI.Optimization.LinearProgramming.Lattice.Radix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The dimension descent for Appendix A. At each step the first nonvanishing
integer test must have the correct sign; zero tests descend to a larger span. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open SignType WithLp

variable {p : ℕ}

private def formMap (a : Fin p → ℤ) : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] ℝ where
  toFun x := dotProduct (fun i => (a i : ℝ)) x.ofLp
  map_add' x y := dotProduct_add _ x.ofLp y.ofLp
  map_smul' r x := dotProduct_smul r _ x.ofLp

/-- A short test vanishing on the current span and the new integer direction
vanishes on their enlarged span. -/
theorem annihilates_span_extension (S : Submodule ℝ (EuclideanSpace ℝ (Fin p)))
    (a z : Fin p → ℤ) (hS : ∀ y ∈ S, dotProduct (fun i => (a i : ℝ)) y.ofLp = 0)
    (hz : dotProduct a z = 0) :
    ∀ y ∈ S ⊔ Submodule.span ℝ {toLp 2 (fun i => (z i : ℝ))},
      dotProduct (fun i => (a i : ℝ)) y.ofLp = 0 := by
  have hKer : S ⊔ Submodule.span ℝ {toLp 2 (fun i => (z i : ℝ))} ≤ LinearMap.ker (formMap a) := by
    apply sup_le (fun y hy => hS y hy)
    apply Submodule.span_le.mpr
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    change (∑ i, (a i : ℝ) * (z i : ℝ)) = 0
    exact_mod_cast hz
  exact fun y hy => hKer hy

/-- Build at most `p` bounded integer directions from strict span growth and the
one-step comparison guarantee. The proof handles forms that vanish at every step. -/
theorem exists_comparison_directions (v : Fin p → ℝ) (M D : ℤ)
    (step : ∀ S : Submodule ℝ (EuclideanSpace ℝ (Fin p)), toLp 2 v ∉ S →
      ∃ z : Fin p → ℤ, (∀ i, |z i| ≤ D) ∧ (toLp 2 (fun i => (z i : ℝ)) ∉ S) ∧
        ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ M →
          (∀ y ∈ S, dotProduct (fun i => (a i : ℝ)) y.ofLp = 0) →
          dotProduct a z ≠ 0 →
            sign (dotProduct a z) = sign (dotProduct (fun i => (a i : ℝ)) v)) :
    ∃ zs : List (Fin p → ℤ), zs.length ≤ p ∧ (∀ z ∈ zs, ∀ i, |z i| ≤ D) ∧
      ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ M →
        leadingSign (zs.map (dotProduct a)) = sign (dotProduct (fun i => (a i : ℝ)) v) := by
  classical
  have go (k : ℕ) (S : Submodule ℝ (EuclideanSpace ℝ (Fin p)))
      (hk : p ≤ Module.finrank ℝ S + k) :
      ∃ zs : List (Fin p → ℤ), zs.length ≤ k ∧ (∀ z ∈ zs, ∀ i, |z i| ≤ D) ∧
        ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ M →
          (∀ y ∈ S, dotProduct (fun i => (a i : ℝ)) y.ofLp = 0) →
          leadingSign (zs.map (dotProduct a)) = sign (dotProduct (fun i => (a i : ℝ)) v) := by
    induction k generalizing S with
    | zero =>
      have hle := S.finrank_le
      have heq : Module.finrank ℝ S = Module.finrank ℝ (EuclideanSpace ℝ (Fin p)) := by
        rw [finrank_euclideanSpace_fin] at hle ⊢
        omega
      have ht := Submodule.eq_top_of_finrank_eq heq
      refine ⟨[], by simp, by simp, ?_⟩
      intro a _ ha
      have hv : toLp 2 v ∈ S := ht ▸ Submodule.mem_top
      have he := ha (toLp 2 v) hv
      simp only [List.map_nil, leadingSign, he, sign_zero]
    | succ k ih =>
      by_cases hv : toLp 2 v ∈ S
      · refine ⟨[], by simp, by simp, ?_⟩
        intro a _ ha
        have he := ha (toLp 2 v) hv
        simp only [List.map_nil, leadingSign, he, sign_zero]
      obtain ⟨z, hz, hnew, htest⟩ := step S hv
      let w : EuclideanSpace ℝ (Fin p) := toLp 2 (fun i => (z i : ℝ))
      let T := S ⊔ Submodule.span ℝ {w}
      have hw : w ∈ T := (show Submodule.span ℝ {w} ≤ T from le_sup_right)
        (Submodule.subset_span (Set.mem_singleton w))
      have hlt : S < T := lt_of_le_of_ne le_sup_left (fun h => hnew (h ▸ hw))
      have hdim := Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨zs, hlen, hbound, hall⟩ := ih T (by omega)
      refine ⟨z :: zs, by simpa using hlen, ?_, ?_⟩
      · intro z' hz'
        rcases List.mem_cons.mp hz' with rfl | hz'
        · exact hz
        · exact hbound z' hz'
      · intro a ha hS
        simp only [List.map_cons, leadingSign]
        split_ifs with hzero
        · apply hall a ha
          exact annihilates_span_extension S a z hS hzero
        · exact htest a ha hS hzero
  obtain ⟨zs, hlen, hb, hall⟩ := go p ⊥ (by simp)
  refine ⟨zs, hlen, hb, fun a ha => hall a ha ?_⟩
  intro y hy
  simp only [Submodule.mem_bot] at hy
  simp [hy]

end Lattice
end LinearProgramming
end Optimization
end OAI
