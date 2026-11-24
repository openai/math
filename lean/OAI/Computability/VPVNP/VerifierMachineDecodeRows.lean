import OAI.Computability.VPVNP.VerifierMachineDecodeMatch
import OAI.Computability.VPVNP.VerifierMachineRowCount
import Mathlib.Tactic.Ring

/-!
# One row of the table interpreter

For each possible row ending at a specified input position, the expression
tests its literal encoding and the preceding position's reachability wire.
The row predicate can restrict the transition record for a particular lookup.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace VerifierMachineDecode

open UniversalMachine
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

/-- Concatenated unary fields of one machine row, including the branch count. -/
def rowBits {extra : ℕ} (b : Branches extra) : Word := (branchFields b).flatMap unary

theorem tableBits_rows (p : Program) (h : p.extra ≠ 0) :
    tableBits p = unary (p.extra - 1) ++ p.rows.flatMap rowBits := by
  simp only [tableBits, ite_eq_right h, List.flatMap_cons, List.flatMap_assoc]
  rfl

private def rowStart {n : ℕ} (j : Fin (n + 1)) (len : ℕ) : Fin (n + 1) :=
  ⟨j.val - len, lt_of_le_of_lt (Nat.sub_le ..) j.isLt⟩

private def rowOption {n extra : ℕ} (j : Fin (n + 1)) (keep : Branches extra → Bool)
    (b : Branches extra) : Expr (Fin n ⊕ Fin (n + 1)) :=
  if keep b = true ∧ (rowBits b).length ≤ j.val then
    let i := rowStart j (rowBits b).length
    .and (.input (.inr i)) ((matchAt n i.val (rowBits b)).rename Sum.inl)
  else .const false

private theorem rowOption_eval {n extra : ℕ} (j : Fin (n + 1)) (keep : Branches extra → Bool)
    (b : Branches extra) (x : Fin n → Bool) (prev : Fin (n + 1) → Bool) :
    (rowOption j keep b).eval (Sum.elim x prev) = true ↔
      ∃ i : Fin (n + 1), keep b = true ∧ prev i = true ∧
        i.val + (rowBits b).length = j.val ∧ MatchAt (List.ofFn x) i.val (rowBits b) := by
  by_cases h : keep b = true ∧ (rowBits b).length ≤ j.val
  · simp only [rowOption, ite_eq_left h, Expr.eval, Sum.elim_inr, Expr.eval_rename, Sum.elim_inl,
      Bool.and_eq_true, eval_matchAt]
    constructor
    · rintro ⟨hp, hm⟩
      exact ⟨rowStart j _, h.1, hp, Nat.sub_add_cancel h.2, hm⟩
    · rintro ⟨i, _, hp, hi, hm⟩
      have e : i = rowStart j (rowBits b).length := Fin.ext (by change i.val = j.val - _; omega)
      subst i
      exact ⟨hp, hm⟩
  · simp only [rowOption, ite_eq_right h, Expr.eval, Bool.false_eq_true, false_iff]
    rintro ⟨i, hk, _, hi, _⟩
    exact h ⟨hk, by omega⟩

/-- Reachability of a row endpoint, using the previous layer's start-position wires. -/
noncomputable def rowStep (n extra : ℕ) (j : Fin (n + 1)) (keep : Branches extra → Bool) :
    Expr (Fin n ⊕ Fin (n + 1)) :=
  Expr.disjoin (Finset.univ.toList.map (rowOption j keep))

theorem rowStep_eval (n extra : ℕ) (j : Fin (n + 1)) (keep : Branches extra → Bool)
    (x : Fin n → Bool) (prev : Fin (n + 1) → Bool) :
    (rowStep n extra j keep).eval (Sum.elim x prev) = true ↔
      ∃ (b : Branches extra) (i : Fin (n + 1)), keep b = true ∧ prev i = true ∧
        i.val + (rowBits b).length = j.val ∧ MatchAt (List.ofFn x) i.val (rowBits b) := by
  simp [rowStep, Expr.eval_disjoin_true, rowOption_eval]

private theorem size_rowOption {n extra : ℕ} (j : Fin (n + 1)) (keep : Branches extra → Bool)
    (b : Branches extra) : (rowOption j keep b).size ≤ 3 * n + 3 := by
  unfold rowOption
  split
  · rename_i h
    simp only [Expr.size, Expr.size_rename]
    have := size_matchAt n (rowStart j (rowBits b).length).val (rowBits b)
    have := j.isLt
    omega
  · simp [Expr.size]

/-- The number of possible rows is quadratic in the number of states. Each literal
test costs at most linearly many gates in the input length. -/
theorem rowStep_size_le (n extra : ℕ) (j : Fin (n + 1)) (keep : Branches extra → Bool)
    (h : extra ≤ n) : (rowStep n extra j keep).size ≤ 200000 * (n + 1) ^ 3 := by
  unfold rowStep
  have hb : ∀ e ∈ Finset.univ.toList.map (rowOption j keep), e.size ≤ 3 * n + 3 := by
    intro e he
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp he
    exact size_rowOption j keep b
  have hs := Expr.size_disjoin_le _ _ hb
  simp only [List.length_map, Finset.length_toList, Finset.card_univ, card_branches] at hs
  calc
    _ ≤ _ := hs
    _ ≤ (1 + ((n + 2) * 81) + ((n + 2) * 81)^2) * (3 * n + 3 + 1) + 1 := by gcongr
    _ ≤ _ := by ring_nf; omega

end VerifierMachineDecode

end VPVNP
end Computability
end OAI
