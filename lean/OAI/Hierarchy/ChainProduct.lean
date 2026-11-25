import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

namespace OAI
/-! # Endpoint sums for a finite weighted path -/

namespace Hierarchy.ChainProduct

open scoped BigOperators
noncomputable section

variable {Q R : Type*} [Fintype Q] [CommSemiring R]

/-- Weight of paths ending at the supplied state after processing the first `m` transitions. -/
def prefixValue : (m : ℕ) → (Q → R) → (Fin m → Q → Q → R) → Q → R
  | 0, L, _, z => L z
  | n+1, L, T, z => ∑ q : Q, prefixValue n L (fun i => T i.castSucc) q * T (Fin.last n) q z

@[simp] theorem prefixValue_zero (L : Q → R) (T : Fin 0 → Q → Q → R) (z : Q) :
    prefixValue 0 L T z = L z := rfl

theorem prefixValue_succ (n : ℕ) (L : Q → R) (T : Fin (n+1) → Q → Q → R) (z : Q) :
    prefixValue (n+1) L T z =
      ∑ q : Q, prefixValue n L (fun i => T i.castSucc) q * T (Fin.last n) q z := rfl

/-- Summing the products over complete paths agrees with a left-to-right scan
and a final sum over the last state. -/
theorem sum_product_eq (m : ℕ) (L : Q → R) (T : Fin m → Q → Q → R) (Z : Q → R) :
    (∑ a : Fin (m+1) → Q, L (a 0) * (∏ i : Fin m, T i (a i.castSucc) (a i.succ)) *
      Z (a (Fin.last m))) = ∑ z : Q, prefixValue m L T z * Z z := by
  classical
  induction m generalizing Z with
  | zero =>
    simpa using (Fintype.sum_equiv (Equiv.funUnique (Fin 1) Q)
      (fun a => L (a 0) * Z (a 0)) (fun z => L z * Z z) (fun _ => rfl))
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n+2) => Q)).sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    rw [prefixValue_succ, ← ih (fun i => T i.castSucc) (fun q => T (Fin.last n) q z),
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    let path : Fin (n+2) → Q := Fin.snoc (α := fun _ : Fin (n+2) => Q) a z
    change L (path 0) * (∏ i : Fin (n+1), T i (path i.castSucc) (path i.succ)) *
      Z (path (Fin.last (n+1))) = _
    dsimp only [path]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_apply_zero, Fin.snoc_castSucc, Fin.snoc_last,
      show (Fin.last n).succ = Fin.last (n+1) by rfl,
      show ∀ i : Fin n, i.castSucc.succ = i.succ.castSucc from fun _ => rfl, mul_assoc]

end
end Hierarchy.ChainProduct

end OAI
