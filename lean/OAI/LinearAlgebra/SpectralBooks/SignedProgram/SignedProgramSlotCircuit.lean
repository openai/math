import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramOrder
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramHotLookup
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramUnaryCircuit

/-! # Unary field signals for the signed program decoder

Fixed slot numbers select a physical table coordinate or the frame-length
header. Gates check whether a field is enabled by the row, tape, and action
counts and read its one-hot value. Every circuit handles input lengths zero and one.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SignedProgram.Hot

open SignedMachine ExactQuantumFactoring BooleanNetwork

variable {n a : ℕ}

private def moveEnabled (read : CellReader n a) : MoveCell n → BooleanNetwork a 1
  | .state | .inputMove => constant true
  | .write j | .direction j => activeBit read .tapes j

private def rowEnabled (read : CellReader n a) (i : Fin n) : RowCell n → BooleanNetwork a 1
  | .state | .input | .kind => constant true
  | .read j => activeBit read .tapes j
  | .out => read (.row i .kind) 0
  | .move b c => (if b then read (.row i .kind) 2 else (read (.row i .kind) 0).bnot).band
    (moveEnabled read c)

/-- Is this coordinate emitted by the unary serialization? -/
def activeNet (read : CellReader n a) : Cell n → BooleanNetwork a 1
  | .tapes | .rows => constant true
  | .row i c => (activeBit read .rows i).band (rowEnabled read i c)

theorem activeNet_correct {read : CellReader n a} {x : Basis a} {t : Table n}
    (h : read.Agrees x t) (c : Cell n) : (activeNet read c).eval x 0 = c.active t := by
  have hT := activeBit_eval h .tapes (Nat.le_of_lt_succ t.tapes.isLt)
  have hR := activeBit_eval h .rows (Nat.le_of_lt_succ t.rows.isLt)
  have hm (m : MoveCell n) : (moveEnabled read m).eval x 0 = m.active t.tapes := by
    cases m with
    | state | inputMove => exact eval_constant _ _ _
    | write j | direction j => exact hT j
  have hk (i : Fin n) (v : Fin 3) :
      (read (.row i .kind) v.val).eval x 0 = decide ((t.row i).kind = v) := by
    rw [h]
    simp only [Cell.value, RowCell.value, Fin.val_inj]
  have hr (i : Fin n) (r : RowCell n) : (rowEnabled read i r).eval x 0 = r.active t.tapes (t.row i).kind := by
    cases r with
    | state | input | kind => exact eval_constant _ _ _
    | read j => exact hT j
    | out => exact hk i 0
    | move b m =>
      cases b with
      | false =>
        change (((read (.row i .kind) 0).bnot).band _).eval x 0 =
          (decide ((t.row i).kind ≠ 0) && m.active t.tapes)
        have hk0 : (read (.row i .kind) 0).eval x 0 = decide ((t.row i).kind = 0) := hk i 0
        rw [eval_band, eval_bnot, hk0, hm]
        simp
      | true =>
        change ((read (.row i .kind) 2).band _).eval x 0 =
          (decide ((t.row i).kind = 2) && m.active t.tapes)
        have hk2 : (read (.row i .kind) 2).eval x 0 = decide ((t.row i).kind = 2) := hk i 2
        rw [eval_band, hk2, hm]
  cases c with
  | tapes | rows => exact eval_constant _ _ _
  | row i r => rw [activeNet, eval_band, hR, hr]; rfl

def activeBudget (n C : ℕ) := 2*((n+1)*(C+4)+1)+C+4

theorem activeNet_count {read : CellReader n a} {C : ℕ} (h : read.Bounded C) (c : Cell n) :
    (activeNet read c).net.count ≤ activeBudget n C := by
  let A := (n+1)*(C+4)+1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hm (m : MoveCell n) : (moveEnabled read m).net.count ≤ A := by
    cases m with
    | state | inputMove => exact hA
    | _ => apply activeBit_count h
  have hr (i : Fin n) (r : RowCell n) : (rowEnabled read i r).net.count ≤ A+C+2 := by
    cases r with
    | state | input | kind => change 1 ≤ _; omega
    | read j => exact (activeBit_count h .tapes j).trans (by change A ≤ _; omega)
    | out => exact (h (.row i .kind) 0).trans (by omega)
    | move b m =>
      have h1 := hm m
      have h2 := h (.row i .kind) 0
      have h3 := h (.row i .kind) 2
      cases b with
      | false =>
        change (((read (.row i .kind) 0).bnot).band (moveEnabled read m)).net.count ≤ _
        rw [count_band, count_bnot]
        omega
      | true =>
        change ((read (.row i .kind) 2).band (moveEnabled read m)).net.count ≤ _
        rw [count_band]
        omega
  cases c with
  | rows | tapes => change 1 ≤ 2*A+C+4; omega
  | row i r =>
    have h1 : (activeBit read .rows i).net.count ≤ A := activeBit_count h _ _
    have h2 := hr i r
    rw [activeNet, count_band]
    change _ ≤ 2*A+C+4
    omega

/-- Out-of-range scalar cell values are clamped in the candidate table's slots.
A separate range test rejects these values on active cells. -/
private def boundedNet (read : CellReader n a) (c : Cell n) (r : Fin (n+1)) :=
  Unary.orOver fun u : Fin (n+3) =>
    if bounded n u.val = r then read c u.val else constant false

private theorem boundedNet_correct {read : CellReader n a} {x : Basis a} {t : Table n}
    (h : read.Agrees x t) (c : Cell n) (r : Fin (n+1)) :
    (boundedNet read c r).eval x 0 = true ↔ r = bounded n (c.value t) := by
  rw [boundedNet, Unary.orOver_eval]
  constructor
  · rintro ⟨j,hj⟩
    by_cases he : bounded n j.val = r
    · rw [ite_eq_left he, h, decide_eq_true_eq] at hj
      rw [hj, he]
    · simp only [ite_eq_right he, eval_constant, Bool.false_eq_true] at hj
  · rintro rfl
    let v : Fin (n+3) := ⟨_, (c.value_lt t).trans_le c.arity_bound⟩
    exact ⟨v, by rw [ite_eq_left (show bounded n v.val = _ from rfl), h]; simp [v]⟩

private theorem boundedNet_count {read : CellReader n a} {C : ℕ} (h : read.Bounded C)
    (c : Cell n) (r : Fin (n+1)) : (boundedNet read c r).net.count ≤ (n+3)*(C+5)+1 := by
  apply (Unary.orOver_count _ (C := C+1) ?_).trans
  · simp [Nat.add_assoc]
  · intro u
    by_cases he : bounded n u.val = r
    · rw [ite_eq_left he]; exact (h _ _).trans (by omega)
    · rw [ite_eq_right he, count_constant]; omega

private def slotCell (read : CellReader n a) (c : Cell n) : Unary.Slot n → BooleanNetwork a 1
  | none => (activeNet read c).bnot
  | some r => (activeNet read c).band (boundedNet read c r)

/-- The one-hot field signals consumed by the cursor checker. -/
def slotNet (read : CellReader n a) (frame : Fin (n+1) → BooleanNetwork a 1)
    (i : Fin (slotsCount n)) (z : Unary.Slot n) : BooleanNetwork a 1 :=
  if h : i.val = 0 then z.elim (constant false) frame
  else slotCell read (cellAt n ⟨i.val-1, by have := i.isLt; omega⟩) z

theorem slotNet_correct {read : CellReader n a} {x : Basis a} {t : Table n}
    (h : read.Agrees x t) (frame : Fin (n+1) → BooleanNetwork a 1) (f : Fin (n+1))
    (hf : ∀ r, (frame r).eval x 0 = true ↔ r = f) (i : Fin (slotsCount n)) (z : Unary.Slot n) :
    (slotNet read frame i z).eval x 0 = true ↔ z = t.slot f i := by
  rw [← slotAt_eq]
  by_cases hi : i.val = 0
  · rw [slotNet, dite_eq_left hi, slotAt, dite_eq_left hi]
    cases z <;> simp [hf]
  · rw [slotNet, dite_eq_right hi, slotAt, dite_eq_right hi]
    let c := cellAt n ⟨i.val-1, by have := i.isLt; omega⟩
    change (slotCell read c z).eval x 0 = true ↔ z = if c.active t then _ else _
    cases z <;> cases ha : c.active t <;> simp [slotCell, activeNet_correct h, ha, boundedNet_correct h]
    rfl

def slotBudget (n C : ℕ) := activeBudget n C + (n+3)*(C+5)+C+3

theorem slotNet_count {read : CellReader n a} {C : ℕ} (h : read.Bounded C)
    (frame : Fin (n+1) → BooleanNetwork a 1) (hf : ∀ j, (frame j).net.count ≤ C)
    (i : Fin (slotsCount n)) (z : Unary.Slot n) : (slotNet read frame i z).net.count ≤ slotBudget n C := by
  by_cases hi : i.val = 0
  · rw [slotNet,dite_eq_left hi]
    cases z with
    | none => change 1 ≤ _; unfold slotBudget; omega
    | some j => exact (hf j).trans (by unfold slotBudget; omega)
  · rw [slotNet,dite_eq_right hi]
    let c := cellAt n ⟨i.val-1,by have := i.isLt; omega⟩
    change (slotCell read c z).net.count ≤ _
    have ha := activeNet_count h c
    cases z with
    | none => rw [slotCell,count_bnot]; unfold slotBudget; omega
    | some r =>
      have hr := boundedNet_count h c r
      rw [slotCell,count_band]; unfold slotBudget; omega

/-- Every active field has a value at most the input length. There are exactly
two possible out-of-range codes below the common `n+3` bound. -/
def fitsNet (read : CellReader n a) : BooleanNetwork a 1 :=
  Unary.andOver fun c : Cell n =>
    ((activeNet read c).band ((read c (n+1)).bor (read c (n+2)))).bnot

theorem fitsNet_correct {read : CellReader n a} {x : Basis a} {t : Table n}
    (h : read.Agrees x t) (f : Fin (n+1)) : (fitsNet read).eval x 0 = true ↔ t.Fits f := by
  rw [fitsNet, Unary.andOver_eval, fits_iff]
  apply forall_congr'
  intro c
  have hlt := (c.value_lt t).trans_le c.arity_bound
  rw [eval_bnot, eval_band, eval_bor, h, h, activeNet_correct h]
  cases ha : c.active t <;> simp
  omega

def fitsBudget (n C : ℕ) := (2+n*(8+5*n))*(activeBudget n C+2*C+7)+1

theorem fitsNet_count {read : CellReader n a} {C : ℕ} (h : read.Bounded C) :
    (fitsNet read).net.count ≤ fitsBudget n C := by
  apply (Unary.andOver_count _ (C := activeBudget n C+2*C+6) ?_).trans
  · unfold fitsBudget
    gcongr
    exact cells_card_le n
  · intro c
    simp only [count_bnot,count_band,count_bor]
    have := activeNet_count h c
    have := h c (n+1)
    have := h c (n+2)
    omega

end SignedProgram.Hot

end

end SpectralBooks
end LinearAlgebra
end OAI
