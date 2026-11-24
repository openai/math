import OAI.Computability.BinPacking.CookLevin.ConfigIndex
import OAI.Computability.VPVNP.VerifierMachineSimulation

/-!
# Loading the coefficient machine's Boolean registers

An initial state bit reads the decoder's empty-program flag or its complement.
At a first-tape input position the symbol-two register reads the input bit, and
the symbol-one register reads its complement.
All other cells initially contain the blank symbol.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalMachine

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

variable {ι : Type*} {n r : ℕ}

/-- Initialize each one-hot register using at most a single input and a negation. -/
def initialRegisterExpr (input : Fin n → ι) (empty : ι) : WindowRegister n r → Expr ι
  | .inl q =>
    if 1 = q.val then .input empty else if 2 = q.val then .not (.input empty) else .const false
  | .inr (true, _, s) => .const (decide ((0 : Symbol) = s))
  | .inr (false, i, s) =>
    if h : r ≤ i.val ∧ i.val - r < n then
      let j : Fin n := ⟨i.val - r, h.2⟩
      if (2 : Symbol) = s then .input (input j) else if (1 : Symbol) = s then .not (.input (input j)) else .const false
    else .const (decide ((0 : Symbol) = s))

theorem initialRegisterExpr_eval (input : Fin n → ι) (empty : ι) (v : ι → Bool) (x : Fin n → Bool)
    (p : Program) (hx : ∀ i, v (input i) = x i) (he : v empty = decide (p.extra = 0))
    (j : WindowRegister n r) :
    (initialRegisterExpr input empty j).eval v = registerEncoding (windowInitial p r x) j := by
  cases j with
  | inl q =>
    have hs : (windowInitial p r x).state.val = if p.extra = 0 then 1 else 2 := by
      unfold windowInitial
      split <;> rfl
    simp only [registerEncoding, hs]
    by_cases h : p.extra = 0 <;> by_cases h₁ : 1 = q.val <;> by_cases h₂ : 2 = q.val <;>
      simp [initialRegisterExpr, h, h₁, h₂, Expr.eval, he]
    omega
  | inr reg =>
    rcases reg with ⟨b,i,s⟩
    cases b with
    | true => rfl
    | false =>
      by_cases h : r ≤ i.val ∧ i.val - r < n
      · cases hb : x ⟨i.val - r, h.2⟩ <;> by_cases h₁ : (1 : Symbol) = s <;> by_cases h₂ : (2 : Symbol) = s <;>
          simp [initialRegisterExpr, registerEncoding, windowInitial, h, h₁, h₂, Expr.eval, hx,
            hb]
        exact (by decide : (1 : Symbol) ≠ 2) (h₁.trans h₂.symm)
      · simp [initialRegisterExpr, registerEncoding, windowInitial, h, Expr.eval]

theorem initialRegisterExpr_size_le (input : Fin n → ι) (empty : ι) (j : WindowRegister n r) :
    (initialRegisterExpr input empty j).size ≤ 2 := by
  rcases j with q | ⟨b,i,s⟩
  · simp only [initialRegisterExpr]
    split_ifs <;> simp [Expr.size]
  · cases b <;> simp only [initialRegisterExpr]
    · split_ifs <;> simp [Expr.size]
    · simp [Expr.size]

end UniversalMachine

end VPVNP
end Computability
end OAI
