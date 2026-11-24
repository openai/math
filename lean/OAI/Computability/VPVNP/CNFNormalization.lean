import OAI.Computability.VPVNP.ExactOneOccurrences
import OAI.Computability.VPVNP.HardnessWeights

/-!
# Bounding the number of clauses by the number of literals

A single empty clause rejects every assignment. Replacing an inconsistent
formula containing an empty clause by that clause alone controls its clause
count even when the input length bound counts only literal occurrences.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessCNF

variable {k : ℕ}

/-- Keep a single empty clause when the input contains one. -/
def normalizeClauses (φ : CNF k) : CNF k :=
  if [] ∈ φ then [[]] else φ

@[simp] theorem satisfies_normalizeClauses (φ : CNF k) (x : Fin k → Bool) :
    Satisfies (normalizeClauses φ) x ↔ Satisfies φ x := by
  by_cases h : [] ∈ φ
  · have hfalse : ¬ Satisfies φ x := fun hs => by simpa using hs [] h
    rw [iff_false_intro hfalse, normalizeClauses, ite_eq_left h]
    simp [Satisfies]
  · simp [normalizeClauses, h]

@[simp] theorem weightedCNF_normalizeClauses {R : Type*} [CommSemiring R] (φ : CNF k)
    (w : Fin k → R) : weightedCNF (normalizeClauses φ) w = weightedCNF φ w := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Satisfies φ x
  · rw [ite_eq_left ((satisfies_normalizeClauses φ x).mpr hx), ite_eq_left hx]
  · rw [ite_eq_right (fun h => hx ((satisfies_normalizeClauses φ x).mp h)), ite_eq_right hx]

theorem literalCount_normalizeClauses_le (φ : CNF k) :
    literalCount (normalizeClauses φ) ≤ literalCount φ := by
  by_cases h : [] ∈ φ <;> simp [normalizeClauses, h, literalCount]

theorem length_normalizeClauses_le (φ : CNF k) :
    (normalizeClauses φ).length ≤ literalCount φ + 1 := by
  by_cases h : [] ∈ φ
  · simp [normalizeClauses, h]
  · simpa [normalizeClauses, h] using (ExactOne.length_le_literalCount_of_nil_notMem h).trans (Nat.le_succ _)

/-- For a family bounded in literal occurrences, both normalized size measures
are polynomially bounded. -/
theorem normalizeClauses_polynomial_bounds {k : ℕ → ℕ} (φ : ∀ n, CNF (k n))
    (h : PolynomiallyBounded fun n => literalCount (φ n)) :
    PolynomiallyBounded (fun n => literalCount (normalizeClauses (φ n))) ∧
      PolynomiallyBounded (fun n => (normalizeClauses (φ n)).length) :=
  ⟨h.of_le (fun n => literalCount_normalizeClauses_le (φ n)),
    (h.add (.const 1)).of_le (fun n => length_normalizeClauses_le (φ n))⟩

end HardnessCNF

end VPVNP
end Computability
end OAI
