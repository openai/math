import OAI.Combinatorics.Sunflower.Comparison
import OAI.Combinatorics.Sunflower.Copy
import OAI.Combinatorics.Sunflower.Placement.Rules
import OAI.Combinatorics.Sunflower.PositiveFilter

/-! # Uniform controlled tests for the planar anchor rules

The local matrices read the control at their own site. Under a violated implication
the selected antecedent sites have one common symbol and the target sites another.
The same device preserves its return tensor when all controls agree.
-/

open scoped Classical
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace RuleDevices

open Comparison Placement

noncomputable section

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

/-- A width-preserving copy to a single target gives an equality test. The extra
unused symbol lets every finite alphabet, including the empty one, embed in the
positive-sized label set of the copying construction. -/
private theorem copyFilter
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} S ℂ → _ → Prop))
    (P : Finset S) (s : S) (hP : P.Nonempty)
    (hw : maskDiagonalPrice φ 1 (insert s P) = maskDiagonalPrice φ 1 P) :
    ∃ B : ℝ, ∀ m : ℕ, ∃ R Q : Raw.{0} S ℂ,
      R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧ rawLogPrice φ 1 R - rawLogPrice φ 1 Q ≤ B ∧
      EqualityMaps P {s} (Fin m) R Q := by
  obtain ⟨t, ht⟩ := hP
  refine ⟨maskDiagonalPrice φ 1 P, fun m =>
    ⟨Copy.input P s m, Copy.returned P m,
      Raw.maskDiagonal_ne_zero _ (Finset.insert_nonempty ..) _,
      Raw.maskDiagonal_ne_zero _ ⟨t, ht⟩ _,
      (Copy.cost_eq φ ⟨t, ht⟩ 1 hw m).le, ?_⟩⟩
  refine ⟨fun j u => Copy.matrix P s t m j u.castSucc, ?_⟩
  intro x y c hL hT o
  have hc : c s = y := hT s (Finset.mem_singleton_self s)
  have h := Copy.matrix_apply (z := s) ht (fun j => (c j).castSucc) x.castSucc
    (fun j hj => congrArg Fin.castSucc (hL j hj)) o
  refine h.trans ?_
  by_cases he : x = y <;> simp [hc, he]

variable {n : ℕ} {q : Rule (Fin (n+2))}
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Site n) ℂ → _ → Prop))

/-- Uniform price and behavior of a single implication test. -/
def UniformRule (q : Rule (Fin (n+2))) : Prop :=
  ∃ B : ℝ, ∀ m : ℕ, ∃ D : Comparison.Device (Site n) (Fin m), D.cost φ ≤ B ∧
    (∀ u, D.out (fun _ => u) = D.Q.coeff) ∧
    ∀ f : Fin (n+2) → Fin m, ¬ q.Holds f → D.out (f ∘ group) = 0

theorem exists_rule_device (hq : q ∈ anchorRules 0 1) (d : RuleSites q)
    (hw : d.Works (maskDiagonalPrice φ 1)) : UniformRule φ q := by
  classical
  have hP := d.hL.mono (Finset.subset_union_left (s₂ := d.R))
  have hd := (mem_anchorRules.mp hq).distinct (Fin.zero_ne_one : (0 : Fin (n+2)) ≠ 1)
  have hex : ∃ B : ℝ, ∀ m : ℕ, ∃ R Q : Raw.{0} (Site n) ℂ,
      R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧ rawLogPrice φ 1 R - rawLogPrice φ 1 Q ≤ B ∧
      EqualityMaps (d.L ∪ d.R) d.T (Fin m) R Q := by
    rcases hw with hgap | ⟨s, hT, he⟩
    · exact exists_equality_filter φ _ _ hP d.hT (d.disjoint hd.2.1 hd.2.2) hgap
    · rw [hT]
      exact copyFilter φ _ _ hP he
  obtain ⟨B, hB⟩ := hex
  refine ⟨B, fun m => ?_⟩
  obtain ⟨R, Q, hR, hQ, hcost, M, hM⟩ := hB m
  let D : Comparison.Device (Site n) (Fin m) := ⟨R, Q, hR, hQ, M⟩
  refine ⟨D, hcost, ?_, ?_⟩
  · intro u
    funext o
    exact (hM u u (fun _ => u) (fun _ _ => rfl) (fun _ _ => rfl) o).trans (by simp [D])
  · intro f hv
    obtain ⟨he, hne⟩ := (q.not_holds_iff f).mp hv
    funext o
    exact (hM _ _ (f ∘ group) (d.antecedent_const f he) (d.target_const f) o).trans
      (by simp [hne])

/-- One spectral point supplies positive group deficit and all rule tests with
bounds chosen before the alphabet size. -/
theorem exists_devices (n : ℕ) :
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Site n) ℂ → _ → Prop),
      0 < 1 - ∑ g, maskDiagonalPrice φ 1 (Placement.fiber g) ∧
        ∀ q ∈ anchorRules (0 : Fin (n+2)) 1, UniformRule φ q := by
  obtain ⟨φ, hdef, hgeo⟩ := exists_priced_placement n
  refine ⟨φ, hdef, fun q hq => ?_⟩
  obtain ⟨d, hw⟩ := hgeo q hq
  exact exists_rule_device φ hq d hw

end

end RuleDevices
end Sunflower
end Combinatorics
end OAI
