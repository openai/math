import OAI.Computability.BorderVNP.BranchSlice
import OAI.Computability.VPVNP.GrammarLabels

/-! # Evaluating a weighted branch slice by a shared parse table

Each layer of the arithmetic grammar is materialized as a vector. Products in later
layers refer back to these values, so no parse tree or individual output coefficient
needs to be enumerated.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {R : Type*} [CommRing R] {k h n : ℕ}

/-- Evaluate one degree layer from the previously stored layers. -/
noncomputable def tableRow (G : ParseGrammar R (Fin k) (Fin h) n) (z : Fin k → R)
    (d : Fin n) (previous : Vector (Vector R h) d.val) : Vector R h :=
  Vector.ofFn fun state =>
    if d.val = 0 then ∑ i, G.terminal state i * z i
    else ∑ idx : Fin d.val × Fin h × Fin h,
      G.binary d state idx.1 idx.2.1 idx.2.2 *
        previous[idx.1.val][idx.2.1.val] *
        (previous[d.val - 1 - idx.1.val]'(rightDegree_lt d idx.1))[idx.2.2.val]

/-- Materialize the first `m` degree layers in increasing order. -/
noncomputable def tableRows (G : ParseGrammar R (Fin k) (Fin h) n) (z : Fin k → R) :
    (m : ℕ) → m ≤ n → Vector (Vector R h) m
  | 0, _ => #v[]
  | m + 1, hm =>
    let previous := tableRows G z m (by omega)
    previous.push (tableRow G z ⟨m, hm⟩ previous)

/-- Every stored scalar is exactly the formal-polynomial evaluation of the indicated state. -/
theorem tableRows_correct (G : ParseGrammar R (Fin k) (Fin h) n) (z : Fin k → R)
    (m : ℕ) (hm : m ≤ n) (l : Fin m) (i : Fin h) :
    (tableRows G z m hm)[l.val][i.val] =
      eval z (G.eval ⟨l.val, l.isLt.trans_le hm⟩ i) := by
  induction m generalizing i with
  | zero => exact l.elim0
  | succ m ih =>
    by_cases hl : l.val < m
    · rw [tableRows, Vector.getElem_push_lt hl]
      exact ih (by omega) ⟨l.val, hl⟩ i
    · obtain ⟨l, hlt⟩ := l
      have hval : l = m := Nat.eq_of_lt_succ_of_not_lt hlt hl
      subst l
      simp only [tableRows, Vector.getElem_push_eq, tableRow, Vector.getElem_ofFn]
      split
      next hz =>
        rw [G.eval_terminal hz]
        simp
      next hz =>
        rw [G.eval_binary hz]
        simp only [Fintype.sum_prod_type, map_sum, map_mul, eval_C]
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun u _ ↦
          Finset.sum_congr rfl fun v _ ↦ ?_
        exact congrArg₂ (· * ·) (congrArg (G.binary ⟨m, hm⟩ i j u v * ·)
          (ih (by omega) j u)) (ih (by omega) ⟨m - 1 - j.val, by omega⟩ v)

/-- Computing the weighted output through stored layers agrees with the coefficient sum
of the universal table specialized to the supplied grammar entries. -/
theorem tableRows_weighted (G : ParseGrammar R (Fin k) (Fin h) n)
    (b : ℕ) (a : R) (d : Fin n) (i : Fin h) :
    (tableRows G (fun j ↦ a ^ (b ^ j.val)) n le_rfl)[d.val][i.val] =
      ∑ ν ∈ ((universalGrammar (Fin k) (Fin h) n).eval d i).support,
        G.specializeLabels (((universalGrammar (Fin k) (Fin h) n).eval d i).coeff ν) *
        a ^ digitExponent b ν := by
  rw [tableRows_correct, ← G.specialize_universalGrammar, ← eval₂_eq_eval_map, eval₂_eq']
  simp only [digitExponent_eq_sum, ← pow_mul, Finset.prod_pow_eq_pow_sum]

/-- Per-layer field operations: one multiplication and one addition per terminal, or two
multiplications and one addition per binary term. Each state is evaluated once. -/
def tableRowOps (k h d : ℕ) : ℕ :=
  h * (if d = 0 then 2 * k else 3 * (d * h * h))

/-- The number of field operations for the full stored table is polynomial in its dimensions. -/
theorem tableRows_ops_le (k h n : ℕ) :
    ∑ d : Fin n, tableRowOps k h d.val ≤ n * h * (2 * k + 3 * (n * h * h)) := by
  have per (d : Fin n) : tableRowOps k h d.val ≤ h * (2 * k + 3 * (n * h * h)) := by
    unfold tableRowOps
    gcongr
    split
    · omega
    · apply le_trans _ (Nat.le_add_left _ _)
      gcongr
      exact d.isLt.le
  simpa [mul_assoc] using Finset.sum_le_sum (s := Finset.univ) (fun d _ ↦ per d)

end Branch

end BorderVNP
end Computability
end OAI
