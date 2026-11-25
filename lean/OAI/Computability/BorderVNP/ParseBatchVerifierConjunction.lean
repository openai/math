import OAI.Computability.VPVNP.VerifierMachineNetwork

/-! # Conjunctions of independently addressed Boolean checks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchVerifier

open VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin

variable {σ : Type*}

/-- Test every member of a fixed finite list of predicates. -/
def every : {k : ℕ} → (Fin k → Expr σ) → Expr σ
  | 0, _ => .const true
  | _+1, f => .and (f 0) (every (fun i => f i.succ))

/-- The list test is true precisely when all its constituents are true. -/
theorem every_eval {k : ℕ} (f : Fin k → Expr σ) (z : σ → Bool) :
    (every f).eval z = true ↔ ∀ i, (f i).eval z = true := by
  induction k with
  | zero => simp [every, StatementCircuit.Expr.eval]
  | succ k ih =>
    rw [every, StatementCircuit.Expr.eval, Bool.and_eq_true, ih, Fin.forall_fin_succ]

/-- Each check contributes its own expression size and at most one conjunction. -/
theorem every_size {k : ℕ} (f : Fin k → Expr σ) (D : ℕ) (h : ∀ i, (f i).size ≤ D) :
    (every f).size ≤ (D+1)*k + 1 := by
  induction k with
  | zero => simp [every, StatementCircuit.Expr.size]
  | succ k ih =>
    have h' := ih (fun i => f i.succ) (fun i => h i.succ)
    have h₀ := h 0
    simp only [every, StatementCircuit.Expr.size, Nat.mul_succ]
    omega

end ParseBatchVerifier

end BorderVNP
end Computability
end OAI
