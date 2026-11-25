import OAI.Optimization.LinearProgramming.PrimalDual.Matrix
import OAI.Optimization.LinearProgramming.PrimalDual.Ray
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Positivity

/-! The two-feasibility-query reduction from LP optimization (Corollary 1.2).
The input and query matrices are concrete. The query tree is interpreted by a
feasibility algorithm, and the output carries the properties needed by its caller. -/

universe u v

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open Matrix
open scoped BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {I J : Type} [Fintype I] [Fintype J]

/-- The inequality witness returned by the feasibility algorithm on a NO instance. -/
structure SparseCertificate (A : Matrix I J K) (b y : I → K) : Prop where
  nonnegative : 0 ≤ y
  annihilates : Aᵀ *ᵥ y = 0
  negative : b ⬝ᵥ y < 0
  sparse : (Finset.univ.filter fun i => y i ≠ 0).card ≤ A.rank + 1

theorem SparseCertificate.excludes {A : Matrix I J K} {b y : I → K}
    (h : SparseCertificate A b y) (x : J → K) : ¬ A *ᵥ x ≤ b := by
  intro hx
  have hbound := weak_duality hx h.nonnegative h.annihilates
  rw [zero_dotProduct] at hbound
  exact (not_le_of_gt h.negative) hbound

/-- Both possible answers include verifiable data in the field of the input. -/
inductive FeasibilityReply (A : Matrix I J K) (b : I → K)
  | feasible (x : J → K) (hx : A *ᵥ x ≤ b)
  | infeasible (y : I → K) (hy : SparseCertificate A b y)

/-- The distinction between a finite attained optimum and a normalized improving ray. -/
inductive OptimizationReply (A : Matrix I J K) (b : I → K) (c : J → K)
  | infeasible (y : I → K) (hy : SparseCertificate A b y)
  | optimal (x : J → K) (y : I → K) (value : K)
      (primal : A *ᵥ x ≤ b) (nonnegative : 0 ≤ y) (dual : Aᵀ *ᵥ y = c)
      (primalValue : c ⬝ᵥ x = value) (dualValue : b ⬝ᵥ y = value)
      (maximal : ∀ x', A *ᵥ x' ≤ b → c ⬝ᵥ x' ≤ value)
      (minimal : ∀ y', 0 ≤ y' → Aᵀ *ᵥ y' = c → value ≤ b ⬝ᵥ y')
  | unbounded (x₀ v : J → K) (base : A *ᵥ x₀ ≤ b)
      (ray : A *ᵥ v ≤ 0) (unitGain : c ⬝ᵥ v = 1)

/-- A decision tree whose index bounds its number of adaptive feasibility calls.
Every branch receives a reply for the particular matrix at its parent. -/
inductive FeasibilityTree (K : Type u) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (α : Type v) : ℕ → Type (max 1 u v)
  | done {n : ℕ} (a : α) : FeasibilityTree K α n
  | query {n : ℕ} {R C : Type} [Fintype R] [Fintype C] (A : Matrix R C K) (b : R → K)
      (next : FeasibilityReply A b → FeasibilityTree K α n) : FeasibilityTree K α (n+1)

/-- Decode the second call using the feasible base point from the first. -/
def finish [DecidableEq I] (A : Matrix I J K) (b : I → K) (c x₀ : J → K)
    (hx₀ : A *ᵥ x₀ ≤ b) :
    FeasibilityReply (jointMatrix A b c) (jointRhs b c) → OptimizationReply A b c
  | .feasible z hz => by
    obtain ⟨hx, hy, hdual, hgap⟩ := (joint_feasible_iff A b c z).1 hz
    have heq := le_antisymm hgap (weak_duality hx hy hdual)
    exact .optimal _ _ _ hx hy hdual rfl heq
      (fun x' hx' => (weak_duality hx' hy hdual).trans_eq heq)
      (fun y' hy' hd' => weak_duality hx hy' hd')
  | .infeasible s hs => by
    obtain ⟨hdual, hprimal, hneg⟩ := joint_certificate A b c s hs.annihilates hs.negative
    obtain ⟨hray, hgain⟩ := ray_of_multipliers hx₀
      (fun i => hs.nonnegative (.inl i)) (fun i => hs.nonnegative (.inr (.inl i)))
      (hs.nonnegative (.inr (.inr (.inr (.inr ()))))) hdual hprimal hneg
    exact .unbounded x₀ _ hx₀ hray hgain

/-- First test primal feasibility. A primal witness triggers just the joint system,
whose positive and negative answers yield respectively an optimum and a ray. -/
def optimize [DecidableEq I] (A : Matrix I J K) (b : I → K) (c : J → K) :
    FeasibilityTree K (OptimizationReply A b c) 2 :=
  .query A b fun
    | .infeasible y hy => .done (.infeasible y hy)
    | .feasible x₀ hx₀ => .query (jointMatrix A b c) (jointRhs b c)
        (fun answer => .done (finish A b c x₀ hx₀ answer))

variable {α : Type*}

/-- Interpret the query tree with one uniform feasibility solver. Returns the output
and the number of oracle calls actually performed along the observed branch. -/
def FeasibilityTree.run
    (solver : ∀ {R C : Type} [Fintype R] [Fintype C] (A : Matrix R C K) (b : R → K),
      FeasibilityReply A b) :
    {n : ℕ} → FeasibilityTree K α n → α × ℕ
  | _, .done a => (a, 0)
  | _, @FeasibilityTree.query _ _ _ _ _ _ R C iR iC A b next =>
      let answer := (next (@solver R C iR iC A b)).run solver
      (answer.1, answer.2 + 1)

theorem FeasibilityTree.run_calls_le
    (solver : ∀ {R C : Type} [Fintype R] [Fintype C] (A : Matrix R C K) (b : R → K),
      FeasibilityReply A b) {n : ℕ} (p : FeasibilityTree K α n) : (p.run solver).2 ≤ n := by
  induction p with
  | done => exact Nat.zero_le _
  | query A b next ih => exact Nat.succ_le_succ (ih (solver A b))

/-- The oracle-call bound includes the call that decides initial feasibility. -/
theorem optimize_calls_le_two [DecidableEq I] (A : Matrix I J K) (b : I → K) (c : J → K)
    (solver : ∀ {R C : Type} [Fintype R] [Fintype C] (M : Matrix R C K) (r : R → K),
      FeasibilityReply M r) :
    ((optimize A b c).run solver).2 ≤ 2 :=
  (optimize A b c).run_calls_le solver

omit [Fintype I] in
/-- The ray answer permits a feasible objective value above any given threshold. -/
theorem ray_exceeds (A : Matrix I J K) (b : I → K) (c x₀ v : J → K)
    (hx : A *ᵥ x₀ ≤ b) (hv : A *ᵥ v ≤ 0) (hg : c ⬝ᵥ v = 1) (target : K) :
    ∃ x, A *ᵥ x ≤ b ∧ target < c ⬝ᵥ x := by
  let t := max 0 (target - c ⬝ᵥ x₀) + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  refine ⟨x₀ + t • v, ?_, ?_⟩
  · rw [mulVec_add, mulVec_smul]
    intro i
    change (A *ᵥ x₀) i + t * (A *ᵥ v) i ≤ b i
    have := mul_nonpos_of_nonneg_of_nonpos ht (hv i)
    linarith [hx i]
  · rw [dotProduct_add, dotProduct_smul, hg, smul_eq_mul, mul_one]
    dsimp [t]
    linarith [le_max_right (0 : K) (target - c ⬝ᵥ x₀)]

end PrimalDual
end LinearProgramming
end Optimization
end OAI
