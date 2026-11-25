import OAI.LinearAlgebra.MatrixExponent.FieldFormula
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Lower
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Upper

/-!
# Sharp public-randomness bounds for matrix verification

Each infimum is attained. The upper bounds use witness-free
division-free sketches, while the lower bounds allow a separate
existential witness for each seed. Entropy budgets allow countable
support.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

variable (F : Type*) [Field F] [CharZero F] [IsAlgClosed F]

theorem optimal_support
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 2) :
    treeSupportExponent F ρ = max 2 ((3 / 2 - ρ / 4) ^ 2) ∧
      IsLeast {v : ℝ | TreeSupportPossible F ρ v} (max 2 ((3 / 2 - ρ / 4) ^ 2)) := by
  have h : IsLeast {v : ℝ | TreeSupportPossible F ρ v} (max 2 ((3 / 2 - ρ / 4) ^ 2)) :=
    ⟨(support_upper F hρ hρ').tree_possible, fun _ hv =>
      SupportPossible.lower (TreeSupportPossible.possible hv) (omega_eq_and_rigidity F).2
        (omega_eq F) hρ hρ'⟩
  exact ⟨h.csInf_eq, h⟩

theorem optimal_entropy
    {η : ℝ} (hη : 0 ≤ η) :
    treeEntropyExponent F η = max 2 ((3 / 2 - min (3 * η) 2 / 4) ^ 2) ∧
      IsLeast {v : ℝ | TreeEntropyPossible F η v} (max 2 ((3 / 2 - min (3 * η) 2 / 4) ^ 2)) := by
  have h : IsLeast {v : ℝ | TreeEntropyPossible F η v} (max 2 ((3 / 2 - min (3 * η) 2 / 4) ^ 2)) :=
    ⟨(entropy_upper F hη).tree_possible, fun _ hv =>
      EntropyPossible.lower (TreeEntropyPossible.possible hv) (omega_eq_and_rigidity F).2
        (omega_eq F) hη⟩
  exact ⟨h.csInf_eq, h⟩

theorem support_iff
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 2) :
    TreeSupportPossible F ρ 2 ↔ 6 - 4 * Real.sqrt 2 ≤ ρ := by
  have h := (optimal_support F hρ hρ').2
  rw [← support_threshold hρ']
  exact ⟨fun hp => le_antisymm (h.2 hp) (le_max_left _ _), fun he => he ▸ h.1⟩

theorem entropy_iff
    {η : ℝ} (hη : 0 ≤ η) : TreeEntropyPossible F η 2 ↔ (6 - 4 * Real.sqrt 2) / 3 ≤ η := by
  have h := (optimal_entropy F hη).2
  rw [← entropy_threshold]
  exact ⟨fun hp => le_antisymm (h.2 hp) (le_max_left _ _), fun he => he ▸ h.1⟩

theorem minimum_support :
    IsLeast {ρ : ℝ | 0 ≤ ρ ∧ TreeSupportPossible F ρ 2} (6 - 4 * Real.sqrt 2) := by
  have h := (least_support (omega_eq_and_rigidity F).2 (omega_eq F)).1.1
  refine ⟨⟨h.1, (critical_support F).tree_possible⟩, fun ρ ⟨hρ, hp⟩ => ?_⟩
  rcases le_total ρ 2 with hρ' | hρ'
  · exact (support_iff F hρ hρ').mp hp
  · exact h.2.trans hρ'

theorem minimum_entropy :
    IsLeast {η : ℝ | 0 ≤ η ∧ TreeEntropyPossible F η 2} ((6 - 4 * Real.sqrt 2) / 3) :=
  ⟨⟨(least_entropy (omega_eq_and_rigidity F).2 (omega_eq F)).1.1, (critical_entropy F).tree_possible⟩,
    fun _ h => (entropy_iff F h.1).mp h.2⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
