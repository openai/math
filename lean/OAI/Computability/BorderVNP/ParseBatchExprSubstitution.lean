import OAI.Computability.BorderVNP.ParseBatchWordArithmetic

/-! # Connecting fixed-width Boolean expressions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchSort

open VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin

variable {ι κ : Type*} {w : ℕ}

/-- Replace each input pin by a supplied Boolean expression. -/
def plugExpr (f : ι → Expr κ) : Expr ι → Expr κ
  | .input i => f i
  | .const b => .const b
  | .not e => .not (plugExpr f e)
  | .and e g => .and (plugExpr f e) (plugExpr f g)
  | .or e g => .or (plugExpr f e) (plugExpr f g)

/-- The interpreted plugged expression is the original expression on the computed inputs. -/
theorem plugExpr_eval (f : ι → Expr κ) (e : Expr ι) (x : κ → Bool) :
    (plugExpr f e).eval x = e.eval (fun i => (f i).eval x) := by
  induction e <;> simp_all [plugExpr, StatementCircuit.Expr.eval]

/-- Replacing input pins by expressions of size at most `D` multiplies total size by at
most `D`, even if every occurrence is copied. -/
theorem plugExpr_size (f : ι → Expr κ) (e : Expr ι) {D : ℕ} (hd : 1 ≤ D)
    (hf : ∀ i, (f i).size ≤ D) : (plugExpr f e).size ≤ e.size * D := by
  induction e <;> simp_all [plugExpr, StatementCircuit.Expr.size, Nat.add_mul] <;> omega

/-- Compare the values of two computed words. -/
def wordLE (a b : Fin w → Expr ι) : Expr ι :=
  plugExpr (Sum.elim a b) (leExpr (fun k => Sum.inl k) (fun k => Sum.inr k))

/-- Comparison tests the mathematical order on the unsigned values. -/
theorem wordLE_eval (a b : Fin w → Expr ι) (x : ι → Bool) :
    (wordLE a b).eval x = decide (wordValue x a ≤ wordValue x b) := by
  rw [wordLE, plugExpr_eval, leExpr_eval]
  rfl

/-- Explicit cost of comparing two computed words with a common per-bit expression bound. -/
theorem wordLE_size (a b : Fin w → Expr ι) {D : ℕ} (hd : 1 ≤ D)
    (ha : ∀ k, (a k).size ≤ D) (hb : ∀ k, (b k).size ≤ D) :
    (wordLE a b).size ≤ (15*w+1)*D := by
  simpa only [wordLE, leExpr_size] using
    plugExpr_size (Sum.elim a b) (leExpr (fun k => Sum.inl k) (fun k => Sum.inr k)) hd
      (fun i => Sum.recOn i ha hb)

end ParseBatchSort

end BorderVNP
end Computability
end OAI
