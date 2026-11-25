import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramLookup

/-! # One-hot tests for the table key and action fields -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram
open SignedMachine ExactQuantumFactoring ExactQuantumFactoring.BooleanNetwork

variable {n a : ℕ}

/-- The branch index selects one of the two padded moves stored in the row. -/
structure ActionSignals (n a : ℕ) where
  kind : Fin n → Fin 3 → BooleanNetwork a 1
  out : Fin n → Output → BooleanNetwork a 1
  state : Fin n → Bool → Fin (n+1) → BooleanNetwork a 1
  inputMove : Fin n → Bool → Direction → BooleanNetwork a 1
  workWrite : Fin n → Bool → Fin n → Symbol → BooleanNetwork a 1
  workMove : Fin n → Bool → Fin n → Direction → BooleanNetwork a 1

structure ActionSignals.Agrees (A : ActionSignals n a) (x : Fin a → Bool) (t : Table n) : Prop where
  kind : ∀ i d, (A.kind i d).eval x 0 = decide ((t.row i).kind = d)
  out : ∀ i o, (A.out i o).eval x 0 = decide ((t.row i).out = o)
  state : ∀ i p q, (A.state i p q).eval x 0 = decide (((t.row i).next p).state = q)
  inputMove : ∀ i p d, (A.inputMove i p d).eval x 0 = decide (((t.row i).next p).inputMove = d)
  workWrite : ∀ i p j s, (A.workWrite i p j s).eval x 0 = decide ((((t.row i).next p).work j).1 = s)
  workMove : ∀ i p j d, (A.workMove i p j d).eval x 0 = decide ((((t.row i).next p).work j).2 = d)

structure ActionSignals.Bounded (A : ActionSignals n a) (C : ℕ) : Prop where
  kind : ∀ i d, (A.kind i d).net.count ≤ C
  out : ∀ i o, (A.out i o).net.count ≤ C
  state : ∀ i p q, (A.state i p q).net.count ≤ C
  inputMove : ∀ i p d, (A.inputMove i p d).net.count ≤ C
  workWrite : ∀ i p j s, (A.workWrite i p j s).net.count ≤ C
  workMove : ∀ i p j d, (A.workMove i p j d).net.count ≤ C

/-- Compare two one-hot words by testing for a common asserted letter. -/
def oneHotEqNet {α : Type*} (letters : List α) (u v : α → BooleanNetwork a 1) : BooleanNetwork a 1 :=
  any (letters.map fun i => (u i).band (v i))

theorem oneHotEqNet_eval {α : Type*} [DecidableEq α] (letters : List α)
    (u v : α → BooleanNetwork a 1) (x : Fin a → Bool) (p q : α) (hp : p ∈ letters)
    (hu : ∀ i, (u i).eval x 0 = decide (p = i)) (hv : ∀ i, (v i).eval x 0 = decide (q = i)) :
    (oneHotEqNet letters u v).eval x 0 = decide (p = q) := by
  apply Bool.eq_iff_iff.mpr
  rw [oneHotEqNet, any_eval, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    simp only [eval_band, hu, hv, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.trans h.2.symm
  · rintro rfl
    exact ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, by simp [hu, hv]⟩

theorem oneHotEqNet_count {α : Type*} (letters : List α) (u v : α → BooleanNetwork a 1)
    {C : ℕ} (hu : ∀ i, (u i).net.count ≤ C) (hv : ∀ i, (v i).net.count ≤ C) :
    (oneHotEqNet letters u v).net.count ≤ letters.length * (2 * C + 5) + 1 := by
  have h := any_count (letters.map (fun i => (u i).band (v i))) (c := 2 * C + 1) (by
    intro c hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    simp only [count_band]
    have := hu i
    have := hv i
    omega)
  simpa [oneHotEqNet, Nat.add_assoc] using h

/-- One-hot key tests supplied by the table encoding and the tape-window frame. -/
structure KeyInputs (n a : ℕ) where
  rowActive : Fin n → BooleanNetwork a 1
  tapeActive : Fin n → BooleanNetwork a 1
  rowState : Fin n → Fin (n+1) → BooleanNetwork a 1
  configState : Fin (n+1) → BooleanNetwork a 1
  rowInput : Fin n → Symbol → BooleanNetwork a 1
  inputHead : Symbol → BooleanNetwork a 1
  rowRead : Fin n → Fin n → Symbol → BooleanNetwork a 1
  workHead : Fin n → Symbol → BooleanNetwork a 1

private def symbolLetters : List Symbol := [.blank,.zero,.one]

private theorem mem_symbolLetters (s : Symbol) : s ∈ symbolLetters := by cases s <;> simp [symbolLetters]

def keySignalsOfOneHot (F : KeyInputs n a) : LookupSignals n a where
  rowActive := F.rowActive
  tapeActive := F.tapeActive
  stateEq i := oneHotEqNet (List.ofFn id) (F.rowState i) F.configState
  inputEq i := oneHotEqNet symbolLetters (F.rowInput i) F.inputHead
  workEq i j := oneHotEqNet symbolLetters (F.rowRead i j) (F.workHead j)

structure KeyInputs.Agrees (F : KeyInputs n a) (x : Fin a → Bool) (t : Table n)
    (q : Fin (n+1)) (s : Symbol) (w : Fin n → Symbol) : Prop where
  row : ∀ i, (F.rowActive i).eval x 0 = decide (i.val < t.rows.val)
  tape : ∀ j, (F.tapeActive j).eval x 0 = decide (j.val < t.tapes.val)
  rowState : ∀ i p, (F.rowState i p).eval x 0 = decide ((t.row i).state = p)
  configState : ∀ p, (F.configState p).eval x 0 = decide (q = p)
  rowInput : ∀ i c, (F.rowInput i c).eval x 0 = decide ((t.row i).input = c)
  inputHead : ∀ c, (F.inputHead c).eval x 0 = decide (s = c)
  rowRead : ∀ i j c, (F.rowRead i j c).eval x 0 = decide ((t.row i).reads j = c)
  workHead : ∀ j c, (F.workHead j c).eval x 0 = decide (w j = c)

theorem KeyInputs.Agrees.keySignals {F : KeyInputs n a} {x t q s w} (h : F.Agrees x t q s w) :
    (keySignalsOfOneHot F).Agrees x t q s w where
  row := h.row
  tape := h.tape
  state i := oneHotEqNet_eval _ _ _ _ _ _ (List.mem_ofFn.mpr ⟨_,rfl⟩) (h.rowState i) h.configState
  input i := oneHotEqNet_eval _ _ _ _ _ _ (mem_symbolLetters _) (h.rowInput i) h.inputHead
  work i j := oneHotEqNet_eval _ _ _ _ _ _ (mem_symbolLetters _) (h.rowRead i j) (h.workHead j)

structure KeyInputs.Bounded (F : KeyInputs n a) (C : ℕ) : Prop where
  row : ∀ i, (F.rowActive i).net.count ≤ C
  tape : ∀ j, (F.tapeActive j).net.count ≤ C
  rowState : ∀ i p, (F.rowState i p).net.count ≤ C
  configState : ∀ p, (F.configState p).net.count ≤ C
  rowInput : ∀ i c, (F.rowInput i c).net.count ≤ C
  inputHead : ∀ c, (F.inputHead c).net.count ≤ C
  rowRead : ∀ i j c, (F.rowRead i j c).net.count ≤ C
  workHead : ∀ j c, (F.workHead j c).net.count ≤ C

theorem KeyInputs.Bounded.keySignals {F : KeyInputs n a} {C : ℕ} (h : F.Bounded C) :
    (keySignalsOfOneHot F).Bounded ((n+3) * (2*C+5) + 1) := by
  have hC : C ≤ (n+3) * (2*C+5) + 1 := by nlinarith
  refine ⟨fun i => (h.row i).trans hC, ?_, ?_, fun j => (h.tape j).trans hC, ?_⟩
  · intro i
    have hh := oneHotEqNet_count (List.ofFn id) _ _ (h.rowState i) h.configState
    rw [List.length_ofFn] at hh
    exact hh.trans (by nlinarith)
  · exact fun i => (oneHotEqNet_count symbolLetters _ _ (h.rowInput i) h.inputHead).trans
      (show 3*(2*C+5)+1 ≤ _ by nlinarith)
  · exact fun i j => (oneHotEqNet_count symbolLetters _ _ (h.rowRead i j) (h.workHead j)).trans
      (show 3*(2*C+5)+1 ≤ _ by nlinarith)

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI
