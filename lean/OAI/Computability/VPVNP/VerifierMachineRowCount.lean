import OAI.Computability.VPVNP.UniversalMachine
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# Counting literal machine rows

Each instruction chooses a target state and four ternary fields. A transition
row contains zero, one, or two ordered instructions, and a repeated instruction
in a two-branch row is allowed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalMachine

private def instructionEquiv (extra : ℕ) :
    Instruction extra ≃ Fin (extra + 2) × Fin 3 × Fin 3 × Fin 3 × Fin 3 where
  toFun a := (a.target, a.firstSymbol, a.firstMove, a.secondSymbol, a.secondMove)
  invFun := fun (q, x, u, y, v) => ⟨q, x, u, y, v⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (extra : ℕ) : Fintype (Instruction extra) :=
  Fintype.ofEquiv _ (instructionEquiv extra).symm

@[simp] theorem card_instruction (extra : ℕ) :
    Fintype.card (Instruction extra) = (extra + 2) * 81 := by
  rw [Fintype.card_congr (instructionEquiv extra)]
  simp

private def branchesEquiv (extra : ℕ) :
    Branches extra ≃ Unit ⊕ Instruction extra ⊕ Instruction extra × Instruction extra where
  toFun
    | .stop => .inl ()
    | .one a => .inr (.inl a)
    | .two a b => .inr (.inr (a, b))
  invFun
    | .inl () => .stop
    | .inr (.inl a) => .one a
    | .inr (.inr (a, b)) => .two a b
  left_inv b := by cases b <;> rfl
  right_inv b := by rcases b with ⟨⟩ | a | ⟨a, c⟩ <;> rfl

instance (extra : ℕ) : Fintype (Branches extra) :=
  Fintype.ofEquiv _ (branchesEquiv extra).symm

@[simp] theorem card_branches (extra : ℕ) :
    Fintype.card (Branches extra) = 1 + (extra + 2) * 81 + ((extra + 2) * 81) ^ 2 := by
  rw [Fintype.card_congr (branchesEquiv extra)]
  simp [pow_two, Nat.add_assoc]

end UniversalMachine

end VPVNP
end Computability
end OAI
