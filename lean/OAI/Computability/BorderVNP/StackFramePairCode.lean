import OAI.Computability.BorderVNP.StackBooleanFrame
import OAI.Computability.RationalHitting.ProcedurePairs

/-!
# Framing two bounded serialized words

The first absent slot selects the length of the first field. With that length fixed,
each output wire reads one input bit or a literal. The first field uses a false marker
before each bit and a true terminator, exactly as in the stack language's pair encoding.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackFrame

open RationalHitting.StackLanguage
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open VPVNP.VerifierNetwork (Frame)

private def slotExpr {σ : Type*} {W : ℕ} (wire : Slots W → σ) (i : ℕ) (b : Option Bool) :
    Expr σ :=
  if h : i < W then .input (wire (⟨i, h⟩, b)) else .const (decide (none = b))

private theorem slotExpr_eval {σ : Type*} {W : ℕ} (wire : Slots W → σ) (u : σ → Bool)
    (w : List Bool) (hw : w.length ≤ W) (hu : ∀ j, u (wire j) = padded W w j)
    (i : ℕ) (b : Option Bool) :
    (slotExpr wire i b).eval u = decide (w[i]? = b) := by
  by_cases h : i < W
  · simp [slotExpr, h, Expr.eval, hu, padded]
  · simp [slotExpr, h, Expr.eval, List.getElem?_eq_none (show w.length ≤ i by omega)]

private theorem slotExpr_size {σ : Type*} {W : ℕ} (wire : Slots W → σ) (i : ℕ)
    (b : Option Bool) : (slotExpr wire i b).size = 1 := by
  unfold slotExpr
  split <;> rfl

private abbrev PairInput (W₁ W₂ : ℕ) := Slots W₁ ⊕ Slots W₂

private def atLength {W₁ W₂ : ℕ} (k : ℕ) : Expr (PairInput W₁ W₂) :=
  .and (slotExpr Sum.inl k none)
    (if k = 0 then .const true else .not (slotExpr Sum.inl (k-1) none))

private theorem atLength_eval {W₁ W₂ : ℕ} (x y : List Bool) (hx : x.length ≤ W₁) (k : ℕ) :
    (atLength k).eval (Sum.elim (padded W₁ x) (padded W₂ y)) = decide (k = x.length) := by
  have hs (i : ℕ) := slotExpr_eval (W := W₁) Sum.inl
    (Sum.elim (padded W₁ x) (padded W₂ y)) x hx (fun _ => rfl) i none
  have hs' (i : ℕ) : (slotExpr Sum.inl i none).eval
      (Sum.elim (padded W₁ x) (padded W₂ y)) = decide (x.length ≤ i) := by
    rw [hs]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, List.getElem?_eq_none_iff]
  by_cases h : k = 0
  · subst k
    simp only [atLength, ite_true, Expr.eval, hs', Bool.and_true]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  · rw [atLength, ite_eq_right h]
    apply Bool.eq_iff_iff.mpr
    simp only [Expr.eval, hs', Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not]
    omega

private theorem atLength_size {W₁ W₂ : ℕ} (k : ℕ) : (atLength (W₁ := W₁) (W₂ := W₂) k).size ≤ 4 := by
  unfold atLength
  split_ifs <;> simp [Expr.size, slotExpr_size]

private theorem codeWord_lookup (x : List Bool) (j : ℕ) (hj : j < 2*x.length) :
    (codeWord x)[j]? = if j % 2 = 0 then some false else x[j / 2]? := by
  induction x generalizing j with
  | nil => simp at hj
  | cons b x ih =>
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => rfl
      | succ j =>
        have hj' : j < 2*x.length := by simp only [List.length_cons] at hj; omega
        have hd : (j+1+1)/2 = j/2+1 := by omega
        have hm : (j+1+1)%2 = j%2 := by omega
        simpa [codeWord, hd, hm] using ih j hj'

private theorem codeWord_end (x : List Bool) : (codeWord x)[2*x.length]? = some true := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa [codeWord, Nat.mul_add] using ih

private def pairSlot {W₁ W₂ : ℕ} (k j : ℕ) (b : Option Bool) : Expr (PairInput W₁ W₂) :=
  if j < 2*k then
    if j % 2 = 0 then .const (decide (some false = b)) else slotExpr Sum.inl (j/2) b
  else if j = 2*k then .const (decide (some true = b))
  else slotExpr Sum.inr (j-(2*k+1)) b

private theorem pairSlot_eval {W₁ W₂ : ℕ} (x y : List Bool) (hx : x.length ≤ W₁)
    (hy : y.length ≤ W₂) (j : ℕ) (b : Option Bool) :
    (pairSlot x.length j b).eval (Sum.elim (padded W₁ x) (padded W₂ y)) =
      decide ((codeWord x ++ y)[j]? = b) := by
  have hl := codeWord_length x
  by_cases h : j < 2*x.length
  · rw [List.getElem?_append_left (by omega), codeWord_lookup x j h]
    by_cases hm : j%2 = 0
    · simp [pairSlot, h, hm, Expr.eval]
    · simpa only [pairSlot, ite_eq_left h, ite_eq_right hm] using
        slotExpr_eval Sum.inl _ x hx (fun _ => rfl) (j/2) b
  · by_cases he : j = 2*x.length
    · rw [List.getElem?_append_left (by omega), he, codeWord_end]
      simp [pairSlot, Expr.eval]
    · rw [List.getElem?_append_right (by omega), hl]
      simpa only [pairSlot, ite_eq_right h, ite_eq_right he] using
        slotExpr_eval Sum.inr _ y hy (fun _ => rfl) _ b

private theorem pairSlot_size {W₁ W₂ : ℕ} (k j : ℕ) (b : Option Bool) :
    (pairSlot (W₁ := W₁) (W₂ := W₂) k j b).size = 1 := by
  unfold pairSlot
  split_ifs <;> simp [Expr.size, slotExpr_size]

private def pairOutput {W₁ W₂ Wout : ℕ} (o : Slots Wout) : Expr (PairInput W₁ W₂) :=
  Expr.disjoin (List.ofFn fun k : Fin (W₁+1) =>
    Expr.and (atLength k.val) (pairSlot k.val o.1.val o.2))

/-- Boolean frame for two separately padded fields in the stack language's pair format.
The output may be truncated to any desired width. -/
noncomputable def pairCodeFrame (W₁ W₂ Wout : ℕ) : Frame (Slots W₁ ⊕ Slots W₂) (Slots Wout) :=
  (Frame.initial id).step pairOutput

/-- Framing agrees bit for bit with the actual variable-length serialization. -/
theorem pairCodeFrame_correct {W₁ W₂ Wout : ℕ} (x y : List Bool)
    (hx : x.length ≤ W₁) (hy : y.length ≤ W₂) :
    (pairCodeFrame W₁ W₂ Wout).eval (Sum.elim (padded W₁ x) (padded W₂ y)) =
      padded Wout (pairCode id id (x,y)) := by
  let u := Sum.elim (padded W₁ x) (padded W₂ y)
  have hi : (Frame.initial id).eval u = u := funext fun _ => by simp
  funext o
  change ((Frame.initial id).step pairOutput).eval u o = _
  rw [Frame.step_eval, hi]
  apply Bool.eq_iff_iff.mpr
  simp only [pairOutput, Expr.eval_disjoin_true, List.mem_ofFn, exists_exists_eq_and,
    Expr.eval, Bool.and_eq_true, u, atLength_eval x y hx, decide_eq_true_eq,
    padded, pairCode, id_eq]
  constructor
  · rintro ⟨k,hk,hv⟩
    rw [hk,pairSlot_eval x y hx hy] at hv
    exact hv
  · intro h
    refine ⟨⟨x.length, by omega⟩,rfl,?_⟩
    rw [pairSlot_eval x y hx hy]
    exact h

/-- Each one-hot output slot uses a linear scan of the first-field width. -/
theorem pairCodeFrame_size (W₁ W₂ Wout : ℕ) :
    (pairCodeFrame W₁ W₂ Wout).size ≤ 30 * Wout * (W₁+1) := by
  have h (o : Slots Wout) : (pairOutput (W₁ := W₁) (W₂ := W₂) o).size ≤ 10*(W₁+1) := by
    unfold pairOutput
    apply (Expr.size_disjoin_le _ 6 ?_).trans
    · simp; omega
    · intro e he
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
      simp only [Expr.size, pairSlot_size]
      have h := atLength_size (W₁ := W₁) (W₂ := W₂) k.val
      omega
  apply (Frame.step_size_le (Frame.initial id) _ _ h).trans
  simp [Slots]
  nlinarith

end StackFrame

end BorderVNP
end Computability
end OAI
