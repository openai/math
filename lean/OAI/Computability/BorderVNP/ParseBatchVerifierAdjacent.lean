import OAI.Computability.BorderVNP.ParseBatchLookup

/-! # Boolean gates for adjacent read verification

After the address-major sort in Lemma 2.3, every request must agree with its
predecessor in both the address and the proposed value. The first slot accepts
only table rows. A final conjunction checks every slot, sharing the already
computed sort wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchLookup
open BorderVNP.ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {τ : Type*} {k a w : ℕ}

private def mismatch (u v : τ) : Expr τ :=
  StatementCircuit.Expr.mux (.input u) (.not (.input v)) (.input v)

private theorem mismatch_eval (z : τ → Bool) (u v : τ) :
    (mismatch u v).eval z = true ↔ z u ≠ z v := by
  cases h : z u <;> cases h' : z v <;> simp [mismatch, StatementCircuit.Expr.eval, h, h']

private def sameWord (u v : Fin w → τ) : Expr τ :=
  .not (StatementCircuit.Expr.disjoin (List.ofFn fun i => mismatch (u i) (v i)))

private theorem sameWord_eval (z : τ → Bool) (u v : Fin w → τ) :
    (sameWord u v).eval z = true ↔ z ∘ u = z ∘ v := by
  rw [sameWord, StatementCircuit.Expr.eval, Bool.not_eq_true', Bool.eq_false_iff]
  change ¬ (_ = true) ↔ _
  rw [StatementCircuit.Expr.eval_disjoin_true]
  simp [List.mem_ofFn, mismatch_eval, funext_iff, Function.comp_def]

private theorem sameWord_size (u v : Fin w → τ) : (sameWord u v).size ≤ 10 * w + 2 := by
  have h := StatementCircuit.Expr.size_disjoin_le (List.ofFn fun i => mismatch (u i) (v i)) 9 (by
    rintro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    rfl)
  simp only [List.length_ofFn] at h
  change _ + 1 ≤ _
  omega

private def predecessor (i : Fin k) : Fin k := ⟨i.val - 1, by have := i.isLt; omega⟩

/-- Interpret the indicated live pins as an addressed batch of words. -/
def pinRows (address : Fin k → Fin a → τ) (request : Fin k → τ)
    (payload : Fin k → Fin w → τ) (z : τ → Bool) : Fin k → Row (Fin w → Bool) :=
  fun i => ⟨value (z ∘ address i), z (request i), z ∘ payload i⟩

/-- The local test at one sorted position, including the special first position. -/
def adjacentExpr (address : Fin k → Fin a → τ) (request : Fin k → τ)
    (payload : Fin k → Fin w → τ) (i : Fin k) : Expr τ :=
  let noRead : Expr τ := .not (.input (request i))
  if i.val = 0 then noRead
  else .or noRead (.and (sameWord (address (predecessor i)) (address i))
    (sameWord (payload (predecessor i)) (payload i)))

/-- Each row check implements exactly its local implication in `Adjacent`. -/
theorem adjacentExpr_eval (address : Fin k → Fin a → τ) (request : Fin k → τ)
    (payload : Fin k → Fin w → τ) (i : Fin k) (z : τ → Bool) :
    (adjacentExpr address request payload i).eval z = true ↔
      (pinRows address request payload z i).request = true →
        ∃ j : Fin k, j.val + 1 = i.val ∧
          (pinRows address request payload z j).address = (pinRows address request payload z i).address ∧
          (pinRows address request payload z j).payload = (pinRows address request payload z i).payload := by
  by_cases hi : i.val = 0
  · cases htag : z (request i) <;> simp [adjacentExpr, hi, pinRows, StatementCircuit.Expr.eval, htag]
  · have hpred : (predecessor i).val + 1 = i.val := by dsimp [predecessor]; omega
    cases htag : z (request i) with
    | false => simp [adjacentExpr, hi, pinRows, StatementCircuit.Expr.eval, htag]
    | true =>
      simp only [adjacentExpr, ite_eq_right hi, pinRows, StatementCircuit.Expr.eval, htag,
        Bool.not_true, Bool.false_or, Bool.and_eq_true, sameWord_eval, true_implies]
      constructor
      · rintro ⟨ha, hp⟩
        exact ⟨predecessor i, hpred, congrArg value ha, hp⟩
      · rintro ⟨j, hj, ha, hp⟩
        have hji : j = predecessor i := Fin.ext (by omega)
        subst j
        exact ⟨value_injective a ha, hp⟩

/-- Linear cost of one local adjacency test in the widths of the two compared fields. -/
theorem adjacentExpr_size (address : Fin k → Fin a → τ) (request : Fin k → τ)
    (payload : Fin k → Fin w → τ) (i : Fin k) :
    (adjacentExpr address request payload i).size ≤ 10 * (a + w) + 8 := by
  have ha := sameWord_size (address (predecessor i)) (address i)
  have hp := sameWord_size (payload (predecessor i)) (payload i)
  unfold adjacentExpr
  split <;> simp only [StatementCircuit.Expr.size] <;> omega

private def allRows (k : ℕ) : Expr (Fin k) :=
  .not (StatementCircuit.Expr.disjoin (List.ofFn fun i : Fin k => .not (.input i)))

private theorem allRows_eval (z : Fin k → Bool) :
    (allRows k).eval z = true ↔ ∀ i, z i = true := by
  rw [allRows, StatementCircuit.Expr.eval, Bool.not_eq_true', Bool.eq_false_iff]
  change ¬ (_ = true) ↔ _
  rw [StatementCircuit.Expr.eval_disjoin_true]
  simp [List.mem_ofFn, StatementCircuit.Expr.eval]

private theorem allRows_size (k : ℕ) : (allRows k).size ≤ 3 * k + 2 := by
  have h := StatementCircuit.Expr.size_disjoin_le (List.ofFn fun i : Fin k =>
    StatementCircuit.Expr.not (.input i)) 2 (by
      rintro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      rfl)
  simp only [List.length_ofFn] at h
  change _ + 1 ≤ _
  omega

variable {σ : Type*} [Fintype σ] [Fintype τ]

/-- Append the per-row comparisons and the accepting conjunction to the incoming frame. -/
noncomputable def adjacentFrame (f : Frame σ τ) (address : Fin k → Fin a → τ)
    (request : Fin k → τ) (payload : Fin k → Fin w → τ) : Frame σ Unit :=
  (f.step (adjacentExpr address request payload)).step (fun _ => allRows k)

/-- The physical Boolean frame accepts exactly the sorted batch's adjacent-read predicate. -/
theorem adjacentFrame_eval (f : Frame σ τ) (address : Fin k → Fin a → τ)
    (request : Fin k → τ) (payload : Fin k → Fin w → τ) (x : σ → Bool) :
    (adjacentFrame f address request payload).eval x () = true ↔
      Adjacent (pinRows address request payload (f.eval x)) := by
  simp only [adjacentFrame, Frame.step_eval, allRows_eval, adjacentExpr_eval, Adjacent]

/-- The added gates are linear in the number of rows times their bit width, including
a constant final gate budget for an empty batch. -/
theorem adjacentFrame_size (f : Frame σ τ) (address : Fin k → Fin a → τ)
    (request : Fin k → τ) (payload : Fin k → Fin w → τ) :
    (adjacentFrame f address request payload).size ≤ f.size + k * (10 * (a + w) + 11) + 2 := by
  have h₁ := Frame.step_size_le f (adjacentExpr address request payload) _ (adjacentExpr_size address request payload)
  have h₂ := Frame.step_size_le (f.step (adjacentExpr address request payload))
    (fun _ : Unit => allRows k) _ (fun _ => allRows_size k)
  simp only [Fintype.card_fin, Fintype.card_unit, one_mul] at h₁ h₂
  apply h₂.trans
  nlinarith

end ParseBatchLookup

end BorderVNP
end Computability
end OAI
