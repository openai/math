import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Defs

/-!
# Typed script for a bank of aligned streams

Every instruction has finite input and output register sets. A table inspects
the finite vector at one address. A route copies a selected register for each
output register and moves its contents by the supplied address permutation.
Instructions may freely change the register set between operations.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.StageScript

/-- The intermediate register types and their enumerations are part of the
finite program, independently of the length of each stream. -/
inductive Program (M E : Type) : Type → Type → Type 1 where
  | table {A B : Type} [Fintype A] [Fintype B] (op : (A → E) → B → E) : Program M E A B
  | route {A B : Type} [Fintype A] [Fintype B] (src : B → A) (move : B → M) : Program M E A B
  | seq {A B C : Type} (before : Program M E A B) (after : Program M E B C) : Program M E A C

variable {M E A B C : Type} {X : Type*}

/-- Forward execution. A route sends a record to its image under the move. -/
def eval (perm : M → Equiv.Perm X) : {A B : Type} → Program M E A B → (A → X → E) → B → X → E
  | _, _, @Program.table _ _ _ _ _ _ op, v, b, x => op (fun a => v a x) b
  | _, _, @Program.route _ _ _ _ _ _ src move, v, b, x => v (src b) ((perm (move b)).symm x)
  | _, _, .seq before after, v, b, x => eval perm after (eval perm before v) b x

/-- Number of recursive field interchanges. The component layout programs
supply their individual prices. Copies and finite tables are local work. -/
def cost (price : M → ℕ) : {A B : Type} → Program M E A B → ℕ
  | _, _, @Program.table _ _ _ _ _ _ _ => 0
  | _, _, @Program.route _ _ _ _ _ fb _ move => @Finset.sum _ ℕ _ (@Finset.univ _ fb) (fun b => price (move b))
  | _, _, .seq before after => cost price before + cost price after

@[simp] theorem eval_table [Fintype A] [Fintype B] (perm : M → Equiv.Perm X)
    (op : (A → E) → B → E) (v : A → X → E) (b : B) (x : X) :
    eval perm (.table op) v b x = op (fun a => v a x) b := rfl

@[simp] theorem eval_route [Fintype A] [Fintype B] (perm : M → Equiv.Perm X)
    (src : B → A) (move : B → M) (v : A → X → E) (b : B) (x : X) :
    eval perm (.route src move) v b x = v (src b) ((perm (move b)).symm x) := rfl

@[simp] theorem eval_seq (perm : M → Equiv.Perm X) (P : Program M E A B)
    (Q : Program M E B C) (v : A → X → E) :
    eval perm (.seq P Q) v = eval perm Q (eval perm P v) := rfl

@[simp] theorem cost_table [Fintype A] [Fintype B] (price : M → ℕ) (op : (A → E) → B → E) :
    cost price (.table op) = 0 := rfl

@[simp] theorem cost_route [Fintype A] [Fintype B] (price : M → ℕ) (src : B → A) (move : B → M) :
    cost price (E := E) (.route src move) = ∑ b, price (move b) := rfl

@[simp] theorem cost_seq (price : M → ℕ) (P : Program M E A B) (Q : Program M E B C) :
    cost price (.seq P Q) = cost price P + cost price Q := rfl

end Interchange.StageScript

end NearSquareRoot
end Computability
end OAI
