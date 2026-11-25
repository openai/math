import OAI.Computability.BorderVNP.PackedCellAddressRead
import OAI.Computability.BorderVNP.CellSparseCompiled

/-! # Private wire guessing with uniquely forced site staging words

The actual sparse bytecode guesses one flat vector. Splitting that vector at
the private wire end realizes a pair of compact vectors. Whenever all the
staging checks force one word at each site, the bytecode therefore sums the
original local table product once for each wire assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddresses

open Crossing CellSparse CellMacro
open scoped Classical

private def splitGuess (m n : ℕ) : (Fin m → Bool) × (Fin n → Bool) ≃ (Fin (m+n) → Bool) where
  toFun p := Fin.append p.1 p.2
  invFun f := (fun i => f (Fin.castAdd n i),fun i => f (Fin.natAdd m i))
  left_inv p := by ext i <;> simp
  right_inv f := by
    funext i
    cases i using Fin.addCases <;> simp

variable {D m n s : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n) (aux : N.Site → ℕ)

/-- Local sparse bytecode sums precisely the product on the true shared wires, provided
its records check the site staging values and evaluate the constituent site tables. -/
theorem program_factor (dir : Directory) (table : N.Tables ℤ)
    (x : Fin (suppliedSize N cell c) → Bool)
    (expected : (Fin (guessedSize N cell c) → Bool) → ∀ v : {v : N.Site // cell v = c}, Fin (aux v.val) → Bool)
    (check : ∀ g a, dir.weight (lookup (bank N cell c aux g a x)) =
      if siteWords N cell c siteID aux a = expected g then factor N cell c edgeID portID table g x else 0)
    (env : List ℕ) :
    value ((dir.program (externalBase N cell c aux)).expand env) ⟨true,false⟩ (List.ofFn x) =
      ∑ g, factor N cell c edgeID portID table g x := by
  rw [Directory.value_program,externalBase,
    ← (splitGuess (guessedSize N cell c) (siteSize N cell c aux)).sum_comp,
    Fintype.sum_prod_type]
  change (∑ g, ∑ a, dir.weight (lookup (List.ofFn (Fin.append g a) ++ List.ofFn x))) = _
  simp only [List.ofFn_fin_append,List.append_assoc]
  change (∑ g, ∑ a, dir.weight (lookup (bank N cell c aux g a x))) = _
  simp only [check]
  exact sum_staged N cell c siteID aux expected _

end Packing.CellAddresses

end BorderVNP
end Computability
end OAI
