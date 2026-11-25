import OAI.Computability.BorderVNP.ParseBatchExprSubstitution

/-!
# Binary arithmetic for counts between sorted markers

Each key supplies a guessed zero-based marker rank and a count. The first rank must equal
its count. For subsequent keys the rank increases by one marker plus the new count.
Both operands are zero-extended before addition. Even their maximum sum with carry one
fits in the extended width, so the checks use natural-number equality.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchCounts

open BorderVNP.ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {k b : ℕ}

/-- Key, count-selector (false for rank), and MSB-first bit position. -/
abbrev ArithmeticPin (k b : ℕ) := Fin k × Bool × Fin b

/-- Read a rank or a count from the physical input pins. -/
def pinValue (z : ArithmeticPin k b → Bool) (i : Fin k) (count : Bool) : ℕ :=
  value fun j => z (i, count, j)

/-- Previous key, with zero used at the left boundary. -/
def previousKey (i : Fin k) : Fin k := ⟨i.val - 1, by have := i.isLt; omega⟩

/-- Natural-number consistency of all guessed ranks and counts. -/
def RankEquations (rank count : Fin k → ℕ) : Prop :=
  ∀ i, rank i = if i.val = 0 then count i else rank (previousKey i) + 1 + count i

/-- On a nonempty key range the equations split into the first rank and the successive ranks. -/
theorem rankEquations_succ_iff (rank count : Fin (k + 1) → ℕ) :
    RankEquations rank count ↔
      rank 0 = count 0 ∧ ∀ j : Fin k, rank j.succ = rank j.castSucc + 1 + count j.succ := by
  have hp (j : Fin k) : previousKey j.succ = j.castSucc := Fin.ext (by simp [previousKey])
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun j => by simpa [hp] using h j.succ⟩
  · rintro ⟨h₀, hs⟩ i
    exact Fin.cases (by simpa using h₀) (fun j => by simpa [hp] using hs j) i

private def extendedWord (i : Fin k) (count : Bool) : Fin (b + 1) → Expr (ArithmeticPin k b) :=
  Fin.cons (.const false) (fun j => .input (i, count, j))

private theorem extendedWord_value (z : ArithmeticPin k b → Bool) (i : Fin k) (count : Bool) :
    wordValue z (extendedWord i count) = pinValue z i count := by
  simp only [wordValue, extendedWord, value, Fin.cons_zero, Fin.cons_succ, StatementCircuit.Expr.eval,
    Bool.toNat_false, zero_mul, zero_add, pinValue]

private theorem extendedWord_size (i : Fin k) (count : Bool) (j : Fin (b + 1)) :
    (extendedWord i count j).size ≤ 1 :=
  Fin.cases (by rfl) (fun _ => by rfl) j

private def expected (i : Fin k) : Fin (b + 1) → Expr (ArithmeticPin k b) :=
  if i.val = 0 then extendedWord i true
  else sumWord true (extendedWord (previousKey i) false) (extendedWord i true)

private theorem expected_value (z : ArithmeticPin k b → Bool) (i : Fin k) :
    wordValue z (expected i) =
      if i.val = 0 then pinValue z i true else pinValue z (previousKey i) false + 1 + pinValue z i true := by
  unfold expected
  split
  · exact extendedWord_value z i true
  · have ha := value_lt fun j : Fin b => z (previousKey i, false, j)
    have hb := value_lt fun j : Fin b => z (i, true, j)
    change pinValue z (previousKey i) false < 2 ^ b at ha
    change pinValue z i true < 2 ^ b at hb
    have hs := sumWord_value_carry z true (extendedWord (previousKey i) false) (extendedWord i true)
    rw [extendedWord_value, extendedWord_value, Bool.toNat_true, pow_succ] at hs
    cases hc : (carryWord true (extendedWord (previousKey i) false) (extendedWord i true)).eval z <;>
      simp only [hc, Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul, zero_add] at hs <;> omega

private theorem expected_size (i : Fin k) (j : Fin (b + 1)) :
    (expected i j).size ≤ 16 * (b + 1) + 22 := by
  unfold expected
  split
  · exact (extendedWord_size i true j).trans (by omega)
  · exact sumWord_size_le true _ _ 1 (extendedWord_size (previousKey i) false)
      (extendedWord_size i true) j

private def checkKey (i : Fin k) : Expr (ArithmeticPin k b) :=
  .and (wordLE (extendedWord i false) (expected i)) (wordLE (expected i) (extendedWord i false))

private theorem checkKey_eval (z : ArithmeticPin k b → Bool) (i : Fin k) :
    (checkKey i).eval z = true ↔ pinValue z i false =
      if i.val = 0 then pinValue z i true else pinValue z (previousKey i) false + 1 + pinValue z i true := by
  simp only [checkKey, StatementCircuit.Expr.eval, Bool.and_eq_true, wordLE_eval, decide_eq_true_eq,
    extendedWord_value, expected_value]
  exact le_antisymm_iff.symm

private theorem checkKey_size (i : Fin k) :
    (checkKey (b := b) i).size ≤ 1280 * (b + 1) ^ 2 := by
  let D := 16 * (b + 1) + 22
  have hd : 1 ≤ D := by dsimp [D]; omega
  have hr (j : Fin (b + 1)) : (extendedWord i false j).size ≤ D :=
    (extendedWord_size i false j).trans hd
  have h₁ := wordLE_size (extendedWord i false) (expected i) hd hr (expected_size i)
  have h₂ := wordLE_size (expected i) (extendedWord i false) hd (expected_size i) hr
  change _ + _ + 1 ≤ _
  apply (Nat.add_le_add_right (Nat.add_le_add h₁ h₂) 1).trans
  dsimp only [D]
  ring_nf
  omega

private def allKeys (k b : ℕ) : Expr (ArithmeticPin k b) :=
  .not (StatementCircuit.Expr.disjoin (List.ofFn fun i : Fin k => .not (checkKey i)))

private theorem allKeys_eval (z : ArithmeticPin k b → Bool) :
    (allKeys k b).eval z = true ↔ RankEquations (fun i => pinValue z i false) (fun i => pinValue z i true) := by
  rw [allKeys, StatementCircuit.Expr.eval, Bool.not_eq_true', Bool.eq_false_iff]
  change ¬ (_ = true) ↔ _
  rw [StatementCircuit.Expr.eval_disjoin_true]
  simp [List.mem_ofFn, StatementCircuit.Expr.eval, RankEquations, ← checkKey_eval]

private theorem allKeys_size (k b : ℕ) : (allKeys k b).size ≤ 1300 * (k + 1) * (b + 1) ^ 2 := by
  have h := StatementCircuit.Expr.size_disjoin_le (List.ofFn fun i : Fin k =>
    StatementCircuit.Expr.not (checkKey (b := b) i)) (1280 * (b + 1) ^ 2 + 1) (by
      rintro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      exact Nat.add_le_add_right (checkKey_size i) 1)
  simp only [List.length_ofFn] at h
  change _ + 1 ≤ _
  apply (Nat.add_le_add_right h 1).trans
  ring_nf
  omega

/-- Physical verification of the entire binary histogram, with one designated output. -/
noncomputable def countArithmeticFrame (k b : ℕ) : Frame (ArithmeticPin k b) Unit :=
  (Frame.initial id).step fun _ => allKeys k b

/-- The physical output accepts exactly the nonwrapping rank equations. -/
theorem countArithmeticFrame_eval (z : ArithmeticPin k b → Bool) :
    (countArithmeticFrame k b).eval z () = true ↔
      RankEquations (fun i => pinValue z i false) (fun i => pinValue z i true) := by
  have h : (Frame.initial (id : ArithmeticPin k b → ArithmeticPin k b)).eval z = z :=
    funext fun j => Frame.initial_eval id z j
  simpa only [countArithmeticFrame, Frame.step_eval, h] using allKeys_eval z

/-- The gate count is linear in the number of keys and quadratic in the guessed bit width. -/
theorem countArithmeticFrame_size (k b : ℕ) :
    (countArithmeticFrame k b).size ≤ 1300 * (k + 1) * (b + 1) ^ 2 := by
  simpa only [countArithmeticFrame, Frame.initial_size, Fintype.card_unit, one_mul, zero_add] using
    Frame.step_size_le (Frame.initial id) (fun _ : Unit => allKeys k b) _ (fun _ => allKeys_size k b)

end ParseBatchCounts

end BorderVNP
end Computability
end OAI
