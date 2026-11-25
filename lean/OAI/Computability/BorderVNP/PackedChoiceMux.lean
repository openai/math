import OAI.Computability.VPVNP.VerifierMachineNetwork
import Mathlib.Data.List.FinRange

/-! # Reading dynamically selected words from finite candidate banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedChoiceMux

open VPVNP.VerifierNetwork (Expr)
open BinPackingGames.Foundations.Complexity.CookLevin

/-- A value selected by one common one-hot flag per candidate. -/
def read {σ : Type*} {m : ℕ} (flag value : Fin m → σ) : Expr σ :=
  StatementCircuit.Expr.disjoin ((List.finRange m).map fun j => .and (.input (flag j)) (.input (value j)))

theorem read_size {σ : Type*} {m : ℕ} (flag value : Fin m → σ) : (read flag value).size ≤ 4*m+1 := by
  apply (StatementCircuit.Expr.size_disjoin_le _ 3 ?_).trans_eq (by simp [Nat.mul_comm])
  intro t ht
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp ht
  rfl

theorem read_eval {σ : Type*} {m : ℕ} (flag value : Fin m → σ) (x : σ → Bool)
    (j : Fin m) (h : ∀ i, x (flag i) = true ↔ i = j) : (read flag value).eval x = x (value j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [read,StatementCircuit.Expr.eval_disjoin_true,List.mem_map,List.mem_finRange,true_and,
    exists_exists_eq_and,StatementCircuit.Expr.eval,Bool.and_eq_true,h,exists_eq_left]

end PackedChoiceMux

end BorderVNP
end Computability
end OAI
