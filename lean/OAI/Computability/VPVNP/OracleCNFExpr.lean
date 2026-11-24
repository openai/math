import OAI.Computability.VPVNP.VerifierMachineNetwork
import OAI.Computability.VPVNP.HardnessCNF

/-! # Boolean expressions for the coefficient oracle's CNF

Each clause becomes a disjunction of its signed input flags. Negating the
disjunction of failed clauses enforces their conjunction, including the empty
formula and formulas containing empty clauses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace OracleCNFExpr

open HardnessCNF
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

variable {W : Type*} {k : ℕ}

private def lit (wire : Fin k → W) (l : Literal k) : Expr W :=
  if l.2 then .input (wire l.1) else .not (.input (wire l.1))

private def clause (wire : Fin k → W) (c : List (Literal k)) : Expr W :=
  Expr.disjoin (c.map (lit wire))

/-- Expression testing the CNF on the indicated wires of a larger Boolean frame. -/
def formula (wire : Fin k → W) (φ : CNF k) : VerifierNetwork.Expr W :=
  .not (Expr.disjoin (φ.map (fun c => .not (clause wire c))))

private theorem eval_lit (wire : Fin k → W) (x : W → Bool) (l : Literal k) :
    (lit wire l).eval x = true ↔ x (wire l.1) = l.2 := by
  rcases l with ⟨i, b⟩
  cases b <;> simp [lit, Expr.eval]

private theorem eval_clause (wire : Fin k → W) (x : W → Bool) (c : List (Literal k)) :
    (clause wire c).eval x = true ↔ ∃ l ∈ c, x (wire l.1) = l.2 := by
  rw [clause, Expr.eval_disjoin_true]
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
    exact ⟨l, hl, (eval_lit wire x l).mp hv⟩
  · rintro ⟨l, hl, hv⟩
    exact ⟨lit wire l, List.mem_map.mpr ⟨l, hl, rfl⟩, (eval_lit wire x l).mpr hv⟩

private theorem eval_not_true (x : W → Bool) (e : Expr W) :
    (Expr.not e).eval x = true ↔ ¬ e.eval x = true := by
  cases h : e.eval x <;> simp [Expr.eval, h]

theorem formula_eval_iff (wire : Fin k → W) (φ : CNF k) (x : W → Bool) :
    (formula wire φ).eval x = true ↔ Satisfies φ (x ∘ wire) := by
  simp [formula, eval_not_true, Expr.eval_disjoin_true, eval_clause, Satisfies]

private theorem clause_size_le (wire : Fin k → W) (c : List (Literal k)) :
    (clause wire c).size ≤ 3 * c.length + 1 := by
  have h := Expr.size_disjoin_le (c.map (lit wire)) 2 (by
    rintro e he
    obtain ⟨⟨i,b⟩, _, rfl⟩ := List.mem_map.mp he
    cases b <;> simp [lit, Expr.size])
  simpa [clause, Nat.mul_comm] using h

/-- The expression has linear size in the number of literals and clauses. -/
theorem formula_size_le (wire : Fin k → W) (φ : CNF k) :
    (formula wire φ).size ≤ 3 * literalCount φ + 3 * φ.length + 2 := by
  induction φ with
  | nil => simp [formula, Expr.disjoin, Expr.size, literalCount]
  | cons c φ ih =>
    have h := clause_size_le wire c
    simp only [formula, List.map_cons, Expr.disjoin, Expr.size, literalCount, List.sum_cons,
      List.length_cons] at ih ⊢
    omega

end OracleCNFExpr

end VPVNP
end Computability
end OAI
