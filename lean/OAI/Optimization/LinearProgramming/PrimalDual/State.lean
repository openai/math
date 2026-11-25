import OAI.Optimization.LinearProgramming.PrimalDual.Basic
import OAI.Optimization.LinearProgramming.Specification

/-! Convert feasibility machine output to checked data, and serialize all three kinds
of optimization answer in the public RAM layout. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open OAI.Optimization.LinearProgramming.RAM
open Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {m d : ℕ}

/-- The actual halt tag selects the answer. Proofs certify the data read from the tape. -/
def decodeFeasibility (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (s : RAM.State K)
    (h : FeasibilityOutput A b s) : FeasibilityReply A b :=
  if htag : s.output = some 0 then .feasible (readVector s 0 d) (by
    rcases h with ⟨_, hx⟩ | ⟨hother, _⟩
    · exact hx
    · simp [htag] at hother)
  else .infeasible (readVector s 0 m) (by
    rcases h with ⟨heq, _⟩ | ⟨_, hcert⟩
    · exact (htag heq).elim
    · exact ⟨hcert.1, hcert.2.1, hcert.2.2.1, hcert.2.2.2⟩)

private def putPrefix {n : ℕ} (v : Fin n → ℚ) (tail : Nat → ℚ) (i : Nat) : ℚ :=
  if h : i < n then v ⟨i,h⟩ else tail (i-n)

private def terminal (tag : Nat) (data : Nat → ℚ) : RAM.State ℚ :=
  ⟨0, data, fun _ => 0, some tag⟩

/-- The corresponding canonical terminal state. Tags 0, 1 and 2 distinguish
infeasibility, a primal/dual optimum with its value, and unboundedness. -/
def encodeOptimization {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {c : Fin d → ℚ} :
    OptimizationReply A b c → RAM.State ℚ
  | .infeasible y _ => terminal 0 (putPrefix y (fun _ => 0))
  | .optimal x y value _ _ _ _ _ _ _ =>
    terminal 1 (putPrefix x (putPrefix y (fun j => if j = 0 then value else 0)))
  | .unbounded x v _ _ _ => terminal 2 (putPrefix x (putPrefix v (fun _ => 0)))

private theorem read_head {n} (tag : Nat) (v : Fin n → ℚ) (tail : Nat → ℚ) :
    readVector (terminal tag (putPrefix v tail)) 0 n = v := by
  funext i; simp [readVector, terminal, putPrefix]

private theorem read_next {n m} (tag : Nat) (v : Fin n → ℚ) (w : Fin m → ℚ) (tail : Nat → ℚ) :
    readVector (terminal tag (putPrefix v (putPrefix w tail))) n m = w := by
  funext i; simp [readVector, terminal, putPrefix]

private theorem read_value {n m} (tag : Nat) (v : Fin n → ℚ) (w : Fin m → ℚ) (val : ℚ) :
    (terminal tag (putPrefix v (putPrefix w (fun j => if j = 0 then val else 0)))).data (n+m) = val := by
  simp [terminal, putPrefix]

/-- The serialized certified answer satisfies the same output contract as the target RAM. -/
theorem encodeOptimization_correct {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {c : Fin d → ℚ}
    (answer : OptimizationReply A b c) : OptimizationOutput A b c (encodeOptimization answer) := by
  cases answer with
  | infeasible y hy =>
    left
    refine ⟨rfl, ?_⟩
    simpa [encodeOptimization, read_head, Certificate] using
      (show 0 ≤ y ∧ Aᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y < 0 ∧ _ from
        ⟨hy.nonnegative, hy.annihilates, hy.negative, hy.sparse⟩)
  | optimal x y value hx hy heq hcx hby hmax _ =>
    right; left
    refine ⟨rfl, ?_⟩
    simpa [encodeOptimization, read_head, read_next, Feasible, read_value] using
      (show A *ᵥ x ≤ b ∧ 0 ≤ y ∧ Aᵀ *ᵥ y = c ∧ c ⬝ᵥ x = value ∧ b ⬝ᵥ y = value ∧
        ∀ z, A *ᵥ z ≤ b → c ⬝ᵥ z ≤ value from ⟨hx, hy, heq, hcx, hby, hmax⟩)
  | unbounded x v hx hv hg =>
    right; right
    refine ⟨rfl, ?_⟩
    simpa [encodeOptimization, read_head, read_next, Feasible] using
      (show A *ᵥ x ≤ b ∧ A *ᵥ v ≤ 0 ∧ c ⬝ᵥ v = 1 from ⟨hx,hv,hg⟩)

end PrimalDual
end LinearProgramming
end Optimization
end OAI
