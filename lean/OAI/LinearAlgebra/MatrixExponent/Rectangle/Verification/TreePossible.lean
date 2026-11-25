import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Gaps


/-!
# Verification by arithmetic and equality-test trees

Each seed has its own finite tree and number of witness coordinates.
The witness is chosen after the seed is known. The size bound counts
the maximum number of arithmetic operations and tests on a path.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Filter
variable (F : Type*) [Field F]

def TreeSupportPossible (ρ v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (t : ι → ℕ) (A : ∀ i, Tree F n (t i)),
      (Fintype.card ι : ℝ) ≤ (n : ℝ) ^ (ρ + ε) ∧ (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧
      (∀ i, ((A i).depth : ℝ) ≤ (n : ℝ) ^ (v + ε)) ∧ Accurate w (fun i => (A i).accept) Correct

def TreeEntropyPossible (η v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ (ι : Type) (_ : Countable ι) (w : ι → ℝ) (t : ι → ℕ) (A : ∀ i, Tree F n (t i)),
      (∃ E, HasSum (fun i => -w i * Real.log (w i)) E ∧ E ≤ (η + ε) * Real.log n) ∧
      (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧ (∀ i, ((A i).depth : ℝ) ≤ (n : ℝ) ^ (v + ε)) ∧
      Accurate w (fun i => (A i).accept) Correct

def treeSupportExponent (ρ : ℝ) := sInf {v : ℝ | TreeSupportPossible F ρ v}
def treeEntropyExponent (η : ℝ) := sInf {v : ℝ | TreeEntropyPossible F η v}

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
