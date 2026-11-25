import OAI.Optimization.LinearProgramming.PrimalDual.Basic
import OAI.Optimization.LinearProgramming.Farkas.Basic
import OAI.Optimization.LinearProgramming.Specification
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NormNum

/-! Fin-indexed data for the two feasibility calls, with the order of every block fixed. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Prepend a finite block to an ordinal-indexed family. -/
def consFinEquiv {S : Type} {m n : ℕ} (e : S ≃ Fin n) : Fin m ⊕ S ≃ Fin (m+n) :=
  (Equiv.sumCongr (Equiv.refl _) e).trans finSumFinEquiv

/-- Enumerate the rows in the proof's five-block order. Each application is executable
through sums and offsets, including the last row when a preceding block is empty. -/
def jointRowEquiv (m d : ℕ) : JointRow (Fin m) (Fin d) ≃ Fin (m+(m+(d+(d+1)))) :=
  consFinEquiv (consFinEquiv (consFinEquiv (consFinEquiv finOneEquiv.symm)))

def finJointMatrix {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (c : Fin d → K) :
    Matrix (Fin (m+(m+(d+(d+1))))) (Fin (d+m)) K :=
  (jointMatrix A b c).submatrix (jointRowEquiv m d).symm finSumFinEquiv.symm

def finJointRhs {m d : ℕ} (b : Fin m → K) (c : Fin d → K) : Fin (m+(m+(d+(d+1)))) → K :=
  jointRhs b c ∘ (jointRowEquiv m d).symm

omit [IsStrictOrderedRing K] in
private theorem support_card_comp {I R : Type*} [Fintype I] [Fintype R] (e : I ≃ R) (y : R → K) :
    (Finset.univ.filter fun i => (y ∘ e) i ≠ 0).card = (Finset.univ.filter fun i => y i ≠ 0).card := by
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi; simpa using hi
  · intro _ _ _ _ h; exact e.injective h
  · intro r hr; exact ⟨e.symm r, by simpa using hr, e.apply_symm_apply r⟩

private def pullReply {I J R C : Type} [Fintype I] [Fintype J] [Fintype R] [Fintype C]
    (A : Matrix I J K) (b : I → K) (er : I ≃ R) (ec : J ≃ C) :
    FeasibilityReply (A.submatrix er.symm ec.symm) (b ∘ er.symm) → FeasibilityReply A b
  | .feasible x hx => .feasible (x ∘ ec) (fun i => by
      simpa [submatrix_mulVec_equiv] using hx (er i))
  | .infeasible y hy => .infeasible (y ∘ er) (by
      refine ⟨fun i => hy.nonnegative (er i), ?_, ?_, ?_⟩
      · have h := hy.annihilates
        change Aᵀ.submatrix ec.symm er.symm *ᵥ y = 0 at h
        rw [submatrix_mulVec_equiv] at h
        funext j
        simpa using congrFun h (ec j)
      · simpa using hy.negative
      · rw [support_card_comp]
        simpa only [rank_submatrix] using hy.sparse)

/-- Decode the ordinary Fin-indexed joint system without changing any coordinates. -/
def finishFinite {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (c x₀ : Fin d → K)
    (hx₀ : A *ᵥ x₀ ≤ b) (answer : FeasibilityReply (finJointMatrix A b c) (finJointRhs b c)) :
    OptimizationReply A b c := finish A b c x₀ hx₀ (pullReply _ _ _ _ answer)

/-- The outcome of one original feasibility call and, if the primal is feasible,
one call on the concrete finite joint matrix. -/
def optimizeFinite {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (c : Fin d → K)
    (solver : ∀ {r s : ℕ} (M : Matrix (Fin r) (Fin s) K) (rhs : Fin r → K), FeasibilityReply M rhs) :
    OptimizationReply A b c × ℕ :=
  match solver A b with
  | .infeasible y hy => (.infeasible y hy, 1)
  | .feasible x₀ hx₀ =>
    let answer := solver (finJointMatrix A b c) (finJointRhs b c)
    (finishFinite A b c x₀ hx₀ answer, 2)

theorem optimizeFinite_calls_le_two {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K)
    (c : Fin d → K) (solver : ∀ {r s : ℕ} (M : Matrix (Fin r) (Fin s) K) (rhs : Fin r → K),
      FeasibilityReply M rhs) : (optimizeFinite A b c solver).2 ≤ 2 := by
  unfold optimizeFinite
  split <;> norm_num

/-- Existence of a certified finite reply follows over every ordered field.
This theorem is used for output existence, separately from algorithmic complexity. -/
theorem feasibilityReply_nonempty {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) :
    Nonempty (FeasibilityReply A b) := by
  rcases Farkas.sparse_alternative A b with ⟨x, hx⟩ | ⟨y, hy, hA, hb, hs⟩
  · exact ⟨.feasible x hx⟩
  · exact ⟨.infeasible y ⟨hy, hA, by rw [hb]; exact neg_lt_zero.mpr zero_lt_one, hs⟩⟩

/-- The three mathematically correct alternatives exist for every finite LP over an
ordered field, even in zero dimensions. No numerical complexity conclusion is needed here. -/
theorem optimizationReply_nonempty {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K)
    (c : Fin d → K) : Nonempty (OptimizationReply A b c) := by
  obtain ⟨first⟩ := feasibilityReply_nonempty A b
  cases first with
  | infeasible y hy => exact ⟨.infeasible y hy⟩
  | feasible x₀ hx₀ =>
    obtain ⟨answer⟩ := feasibilityReply_nonempty (finJointMatrix A b c) (finJointRhs b c)
    exact ⟨finishFinite A b c x₀ hx₀ answer⟩

end PrimalDual
end LinearProgramming
end Optimization
end OAI
