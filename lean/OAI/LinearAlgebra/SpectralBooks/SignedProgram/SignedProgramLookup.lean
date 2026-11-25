import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramLookupSpec
import OAI.Computability.QuantumFactoring.BooleanFold

/-! # Bounded Boolean networks for transition-table lookup

The key compares state, input symbol, and all active work-head symbols.
A priority multiplexer returns the requested action field of the first active
matching row. The encoded program and the current configuration may both be
inputs to the network.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram
open SignedMachine ExactQuantumFactoring ExactQuantumFactoring.BooleanNetwork

variable {n a : ℕ}

/-- The primitive Boolean tests on encoded rows and the machine configuration. -/
structure LookupSignals (n a : ℕ) where
  rowActive : Fin n → BooleanNetwork a 1
  stateEq : Fin n → BooleanNetwork a 1
  inputEq : Fin n → BooleanNetwork a 1
  tapeActive : Fin n → BooleanNetwork a 1
  workEq : Fin n → Fin n → BooleanNetwork a 1

/-- Meaning of each test on a particular input string. -/
structure LookupSignals.Agrees (W : LookupSignals n a) (x : Fin a → Bool) (t : Table n)
    (q : Fin (n+1)) (s : Symbol) (w : Fin n → Symbol) : Prop where
  row : ∀ i, (W.rowActive i).eval x 0 = decide (i.val < t.rows.val)
  state : ∀ i, (W.stateEq i).eval x 0 = decide ((t.row i).state = q)
  input : ∀ i, (W.inputEq i).eval x 0 = decide ((t.row i).input = s)
  tape : ∀ j, (W.tapeActive j).eval x 0 = decide (j.val < t.tapes.val)
  work : ∀ i j, (W.workEq i j).eval x 0 = decide ((t.row i).reads j = w j)

def rowMatchNet (W : LookupSignals n a) (i : Fin n) : BooleanNetwork a 1 :=
  (((W.rowActive i).band (W.stateEq i)).band (W.inputEq i)).band <|
    all (List.ofFn fun j => (W.tapeActive j).bnot.bor (W.workEq i j))

theorem rowMatchNet_eval (W : LookupSignals n a) (x : Fin a → Bool) (t : Table n)
    (q : Fin (n+1)) (s : Symbol) (w : Fin n → Symbol)
    (h : W.Agrees x t q s w) (i : Fin n) :
    (rowMatchNet W i).eval x 0 = keyMatch t q s w i := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowMatchNet, eval_band, h.row, h.state, h.input, Bool.and_eq_true,
    decide_eq_true_eq, all_eval, keyMatch]
  have hwork :
      (∀ c ∈ List.ofFn (fun j => (W.tapeActive j).bnot.bor (W.workEq i j)), c.eval x 0 = true) ↔
      ∀ j : Fin n, j.val < t.tapes.val → (t.row i).reads j = w j := by
    simp [List.mem_ofFn, h.tape, h.work, or_iff_not_imp_left]
  rw [hwork]
  tauto

/-- Evaluate whichever Boolean field is requested, with the specified fallback bit. -/
private def priority (W : LookupSignals n a) (field : Fin n → BooleanNetwork a 1)
    (fallback : Bool) : List (Fin n) → BooleanNetwork a 1
  | [] => constant fallback
  | i :: rest => mux (rowMatchNet W i) (field i) (priority W field fallback rest)

def lookupBitNet (W : LookupSignals n a) (field : Fin n → BooleanNetwork a 1)
    (fallback : Bool) : BooleanNetwork a 1 :=
  priority W field fallback (List.ofFn id)

theorem lookupBitNet_eval (W : LookupSignals n a) (field : Fin n → BooleanNetwork a 1)
    (fallback : Bool) (x : Fin a → Bool) (t : Table n) (q : Fin (n+1)) (s : Symbol)
    (w : Fin n → Symbol) (h : W.Agrees x t q s w) :
    (lookupBitNet W field fallback).eval x 0 =
      ((firstRow t q s w).map (fun i => (field i).eval x 0)).getD fallback := by
  have selectBit (is : List (Fin n)) :
      (priority W field fallback is).eval x 0 =
      ((is.find? (keyMatch t q s w)).map (fun i => (field i).eval x 0)).getD fallback := by
    induction is with
    | nil => simp [priority]
    | cons i is ih =>
      simp only [priority, eval_mux, rowMatchNet_eval W x t q s w h, List.find?_cons]
      cases hk : keyMatch t q s w i <;> simp [ih]
  exact selectBit (List.ofFn id)

/-- Bound for each of the primitive input tests. -/
structure LookupSignals.Bounded (W : LookupSignals n a) (C : ℕ) : Prop where
  row : ∀ i, (W.rowActive i).net.count ≤ C
  state : ∀ i, (W.stateEq i).net.count ≤ C
  input : ∀ i, (W.inputEq i).net.count ≤ C
  tape : ∀ j, (W.tapeActive j).net.count ≤ C
  work : ∀ i j, (W.workEq i j).net.count ≤ C

def rowMatchBudget (n C : ℕ) := 3 * C + 4 + n * (2 * C + 6)

theorem rowMatchNet_count (W : LookupSignals n a) {C : ℕ} (h : W.Bounded C) (i : Fin n) :
    (rowMatchNet W i).net.count ≤ rowMatchBudget n C := by
  have h₁ := all_count (List.ofFn fun j => (W.tapeActive j).bnot.bor (W.workEq i j))
    (c := 2 * C + 5) (by
      intro c hc
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
      simp only [count_bor, count_bnot]
      have := h.tape j
      have := h.work i j
      omega)
  simp only [List.length_ofFn, Nat.add_assoc, Nat.reduceAdd] at h₁
  simp only [rowMatchNet, count_band, rowMatchBudget]
  have := h.row i
  have := h.state i
  have := h.input i
  omega

def lookupBitBudget (n C F : ℕ) := 1 + n * (2 * rowMatchBudget n C + F + 7)

/-- Every requested field has polynomial gate count in the table width and signal costs. -/
theorem lookupBitNet_count (W : LookupSignals n a) (field : Fin n → BooleanNetwork a 1)
    (fallback : Bool) {C F : ℕ} (h : W.Bounded C) (hf : ∀ i, (field i).net.count ≤ F) :
    (lookupBitNet W field fallback).net.count ≤ lookupBitBudget n C F := by
  have aux (is : List (Fin n)) :
      (priority W field fallback is).net.count ≤ 1 + is.length * (2 * rowMatchBudget n C + F + 7) := by
    induction is with
    | nil => simp [priority]
    | cons i is ih =>
      simp only [priority, count_mux, List.length_cons, Nat.add_mul, one_mul]
      have := rowMatchNet_count W h i
      have := hf i
      omega
  simpa [lookupBitNet, lookupBitBudget] using aux (List.ofFn id)

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI
