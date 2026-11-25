import OAI.Computability.BorderVNP.PackedScanSpec
import OAI.Computability.BorderVNP.ParseBatchWordArithmetic
import OAI.Computability.VPVNP.VerifierMachineSplice

/-! # Boolean circuit for segmented prefix sums of sorted wire records

Each row appends just its new sum bits. The input pins and all old sum pins are
retained by wire selection, so their arithmetic gates are shared by later rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedScan

open ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {σ : Type*} {k w : ℕ}

/-- Read one unsigned, most-significant-bit-first field in the raw table. -/
def read {σ : Type*} {w : ℕ} (x : σ → Bool) (pins : ℕ → Fin w → σ) (i : ℕ) : ℕ :=
  value (x ∘ pins i)

private def equalKey {ι : Type*} (a b : Fin k → ι) : Expr ι := .and (leExpr a b) (leExpr b a)

private theorem equalKey_eval {ι : Type*} (a b : Fin k → ι) (x : ι → Bool) :
    (equalKey a b).eval x = decide (value (x ∘ a) = value (x ∘ b)) := by
  simp only [equalKey, StatementCircuit.Expr.eval, leExpr_eval]
  by_cases h : value (x ∘ a) = value (x ∘ b)
  · simp [h]
  · simp [h]
    omega

private abbrev Previous (σ : Type*) (rows w : ℕ) := σ ⊕ (Fin rows × Fin w)

private def rowExpr (key : ℕ → Fin k → σ) (width : ℕ → Fin w → σ) :
    (t : ℕ) → Fin w → Expr (Previous σ t w)
  | 0, b => .input (.inl (width 0 b))
  | t+1, b =>
    let flag := equalKey (Sum.inl ∘ key (t+1)) (Sum.inl ∘ key t)
    let cur := fun i => StatementCircuit.Expr.input (.inl (width (t+1) i))
    let prev := fun i => StatementCircuit.Expr.input (.inr (Fin.last t, i))
    mux flag (addWord cur prev b) (cur b)

private theorem row_size (key : ℕ → Fin k → σ) (width : ℕ → Fin w → σ) (t : ℕ) (b : Fin w) :
    (rowExpr key width t b).size ≤ 60*k+16*w+33 := by
  cases t with
  | zero => simp [rowExpr, StatementCircuit.Expr.size]
  | succ t =>
    have h := sumWord_size_le false
      (fun i : Fin w => (StatementCircuit.Expr.input (.inl (width (t+1) i)) : Expr (Previous σ (t+1) w)))
      (fun i : Fin w => StatementCircuit.Expr.input (.inr (Fin.last t,i))) 1
      (fun _ => le_rfl) (fun _ => le_rfl) b
    simp only [rowExpr, mux, equalKey, StatementCircuit.Expr.size, leExpr_size, addWord]
    omega

private def retain (t w : ℕ) (row : Fin (t+1) × Fin w) : Previous σ t w ⊕ Fin w :=
  Fin.lastCases (.inr row.2) (fun i => .inl (.inr (i, row.2))) row.1

variable [Fintype σ]

private noncomputable def advance (key : ℕ → Fin k → σ) (width : ℕ → Fin w → σ) (t : ℕ) :
    Frame (Previous σ t w) (Fin (t+1) × Fin w) :=
  (((Frame.initial id).step (rowExpr key width t)).withInput).select (retain t w)

/-- Compile all inclusive per-key prefix totals. Each earlier row remains a live block of wires. -/
noncomputable def scan (key : ℕ → Fin k → σ) (width : ℕ → Fin w → σ) :
    (rows : ℕ) → Frame σ (Fin rows × Fin w)
  | 0 => Frame.initial (fun p => p.1.elim0)
  | t+1 => (advance key width t).subst (scan key width t).withInput

private theorem scan_old (key : ℕ → Fin k → σ) (width : ℕ → Fin w → σ)
    (t : ℕ) (x : σ → Bool) (i : Fin t) (b : Fin w) :
    (scan key width (t+1)).eval x (i.castSucc,b) = (scan key width t).eval x (i,b) := by
  simp only [scan, Frame.subst_eval, advance, Frame.select_eval, retain, Fin.lastCases_castSucc,
    Frame.withInput_eval_inl, Frame.withInput_eval_inr]

private theorem scan_new (key : ℕ → Fin k → σ) (width : ℕ → Fin w → σ)
    (t : ℕ) (x : σ → Bool) (b : Fin w) :
    (scan key width (t+1)).eval x (Fin.last t,b) =
      (rowExpr key width t b).eval ((scan key width t).withInput.eval x) := by
  simp only [scan, Frame.subst_eval, advance, Frame.select_eval, retain, Fin.lastCases_last,
    Frame.withInput_eval_inr, Frame.step_eval]
  congr 1
  funext p
  exact Frame.initial_eval id _ p

/-- A table of `rows` wire records needs only `rows*w*(60*k+16*w+33)` Boolean gates. -/
theorem scan_size (key : ℕ → Fin k → σ) (width : ℕ → Fin w → σ) (rows : ℕ) :
    (scan key width rows).size ≤ rows * (w*(60*k+16*w+33)) := by
  induction rows with
  | zero => simp [scan]
  | succ t ih =>
    have h := Frame.step_size_le (Frame.initial (id : Previous σ t w → _))
      (rowExpr key width t) _ (row_size key width t)
    simp only [Frame.initial_size, zero_add, Fintype.card_fin] at h
    simpa only [scan, Frame.subst_size, Frame.withInput_size, advance, Frame.select_size,
      Nat.succ_mul] using Nat.add_le_add ih h

/-- When run totals fit in the output word, every row gives its exact inclusive run total.
No assumption on sorting is needed for this contiguous-run version. -/
theorem scan_value (key : ℕ → Fin k → σ) (width : ℕ → Fin w → σ) (rows : ℕ)
    (x : σ → Bool) (fits : ∀ j < rows, segmentTotal (read x key) (read x width) j < 2^w)
    (i : Fin rows) : value (fun b => (scan key width rows).eval x (i,b)) =
      segmentTotal (read x key) (read x width) i.val := by
  induction rows with
  | zero => exact i.elim0
  | succ t ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.val_last, scan_new]
      cases t with
      | zero => simp [rowExpr, segmentTotal, StatementCircuit.Expr.eval, read, Function.comp_def]
      | succ t =>
        let f := scan key width (t+1)
        let z := f.withInput.eval x
        let flag : Expr (Previous σ (t+1) w) := equalKey (Sum.inl ∘ key (t+1)) (Sum.inl ∘ key t)
        let cur := fun i : Fin w => (StatementCircuit.Expr.input (.inl (width (t+1) i)) : Expr (Previous σ (t+1) w))
        let prev := fun i : Fin w => (StatementCircuit.Expr.input (.inr (Fin.last t, i)) : Expr (Previous σ (t+1) w))
        have hf : flag.eval z = decide (read x key (t+1) = read x key t) := by
          simp [flag, z, equalKey_eval, read, Function.comp_def]
          rfl
        have hc : wordValue z cur = read x width (t+1) := by
          simp [wordValue, z, cur, StatementCircuit.Expr.eval, read, Function.comp_def]
        have hp : wordValue z prev = segmentTotal (read x key) (read x width) t := by
          simpa [wordValue, z, prev, StatementCircuit.Expr.eval, f] using
            ih (fun j hj => fits j (by omega)) (Fin.last t)
        change value (fun b => (mux flag (addWord cur prev b) (cur b)).eval z) = _
        by_cases he : read x key (t+1) = read x key t
        · simp only [mux_eval, hf, he, decide_true, ite_true, segmentTotal]
          have hfit := fits (t+1) (by omega)
          rw [segmentTotal, ite_eq_left he, ← hc, ← hp] at hfit
          exact (addWord_value z cur prev hfit).trans (congrArg₂ Nat.add hc hp)
        · simp only [mux_eval, hf, he, decide_false, Bool.false_eq_true, ite_false,
            segmentTotal, Nat.add_zero]
          exact hc
    · simpa only [scan_old, Fin.val_castSucc] using ih (fun j hj => fits j (by omega)) j

private def offsetBits (width : ℕ → Fin w → σ) (rows : ℕ) (i : Fin rows × Fin w) :
    Expr (Previous σ rows w) :=
  subWord (fun b => .input (.inr (i.1,b))) (fun b => .input (.inl (width i.1 b))) i.2

/-- Compile the first wire offset of each bundle within its key bucket. -/
noncomputable def offsetScan (key : ℕ → Fin k → σ) (width : ℕ → Fin w → σ) (rows : ℕ) :
    Frame σ (Fin rows × Fin w) :=
  (scan key width rows).withInput.step (offsetBits width rows)

/-- Reading exclusive offsets adds only one subtraction per row. -/
theorem offsetScan_size (key : ℕ → Fin k → σ) (width : ℕ → Fin w → σ) (rows : ℕ) :
    (offsetScan key width rows).size ≤ rows * (w*(60*k+40*w+63)) := by
  have h := Frame.step_size_le (scan key width rows).withInput (offsetBits width rows)
    (24*w+30) (fun i => subWord_size_le _ _ 1 (fun _ => le_rfl) (fun _ => le_rfl) i.2)
  simp only [Frame.withInput_size, Fintype.card_prod, Fintype.card_fin] at h
  have hs := scan_size key width rows
  change (offsetScan key width rows).size ≤ _ at h
  calc
    _ ≤ (scan key width rows).size + rows*w*(24*w+30) := h
    _ ≤ rows*(w*(60*k+16*w+33)) + rows*w*(24*w+30) := Nat.add_le_add_right hs _
    _ = _ := by ring

/-- For a sorted table the exclusive offset sums precisely the widths of earlier rows
in the same bucket. -/
theorem offsetScan_value (key : ℕ → Fin k → σ) (width : ℕ → Fin w → σ) (rows : ℕ)
    (x : σ → Bool) (fits : ∀ j < rows, segmentTotal (read x key) (read x width) j < 2^w)
    (sorted : ∀ i j, i ≤ j → j < rows → read x key i ≤ read x key j) (i : Fin rows) :
    value (fun b => (offsetScan key width rows).eval x (i,b)) =
      ∑ j ∈ Finset.range i.val, if read x key j = read x key i then read x width j else 0 := by
  let z := (scan key width rows).withInput.eval x
  let total := fun b : Fin w => (StatementCircuit.Expr.input (.inr (i,b)) : Expr (Previous σ rows w))
  let cur := fun b : Fin w => (StatementCircuit.Expr.input (.inl (width i b)) : Expr (Previous σ rows w))
  have ht : wordValue z total = segmentTotal (read x key) (read x width) i := by
    simpa [wordValue, z, total, StatementCircuit.Expr.eval] using scan_value key width rows x fits i
  have hc : wordValue z cur = read x width i := by
    simp [wordValue, z, cur, StatementCircuit.Expr.eval, read, Function.comp_def]
  have hle : wordValue z cur ≤ wordValue z total := by
    rw [hc, ht]
    exact width_le_total _ _ _
  simp only [offsetScan, Frame.step_eval, offsetBits]
  change wordValue z (subWord total cur) = _
  rw [subWord_value _ _ _ hle, hc, ht]
  exact total_sub_eq_sum _ _ _ (fun a b hab hbi => sorted a b hab (lt_of_le_of_lt hbi i.isLt))

end PackedScan

end BorderVNP
end Computability
end OAI
