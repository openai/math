import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramHotLookup
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramLocal
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramUnaryCircuit

/-! # Boolean duplicate-key rejection for the signed verifier's program parser

Compare each active row with each other active row. Keys contain the state,
the input symbol, and the symbols read from the active work tapes.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SignedProgram

open ExactQuantumFactoring BooleanNetwork SignedMachine

variable {n a : ℕ}

private def distinctPair (R : Fin n → LookupSignals n a) (i j : Fin n) : BooleanNetwork a 1 :=
  if i = j then constant true else (((R j).rowActive j).band (rowMatchNet (R j) i)).bnot

def distinctNet (R : Fin n → LookupSignals n a) : BooleanNetwork a 1 :=
  Unary.andOver fun i => Unary.andOver fun j => distinctPair R i j

theorem distinctNet_correct (R : Fin n → LookupSignals n a) (t : Table n) (x : Basis a)
    (h : ∀ j, (R j).Agrees x t (t.row j).state (t.row j).input (t.row j).reads) :
    (distinctNet R).eval x 0 = true ↔ t.Distinct := by
  simp only [distinctNet, Unary.andOver_eval]
  have hp (i j : Fin n) : (distinctPair R i j).eval x 0 = true ↔
      (i.val < t.rows.val → j.val < t.rows.val → (t.row i).state = (t.row j).state →
        (t.row i).input = (t.row j).input →
        (∀ k : Fin n, k.val < t.tapes.val → (t.row i).reads k = (t.row j).reads k) → i = j) := by
    by_cases he : i = j
    · simp [distinctPair, he]
    · rw [distinctPair, ite_eq_right he, eval_bnot, eval_band, (h j).row, rowMatchNet_eval _ _ _ _ _ _ (h j)]
      simp only [keyMatch, Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq, he,
        decide_eq_false_iff_not]
      tauto
  simp only [hp, Table.Distinct]

theorem distinctNet_count (R : Fin n → LookupSignals n a) (C : ℕ) (h : ∀ j, (R j).Bounded C) :
    (distinctNet R).net.count ≤ n*(n*(C+rowMatchBudget n C+3)+2)+1 := by
  apply (Unary.andOver_count _ (C := n*(C+rowMatchBudget n C+3)+1) ?_).trans
  · simp [Nat.add_assoc]
  · intro i
    apply (Unary.andOver_count _ (C := C+rowMatchBudget n C+2) ?_).trans
    · simp [Nat.add_assoc]
    · intro j
      by_cases he : i = j
      · rw [distinctPair, ite_eq_left he, count_constant]
        omega
      · rw [distinctPair, ite_eq_right he, count_bnot, count_band]
        have := rowMatchNet_count (R j) (h j) i
        have := (h j).row j
        omega

namespace Hot

open private symbolCode_inj from OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramHotLookup

private def rowKey (read : CellReader n a) (j : Fin n) : KeyInputs n a :=
  keyInputs read (fun q => read (.row j .state) q.val)
    (fun s => read (.row j .input) (symbolCode s))
    (fun k s => read (.row j (.read k)) (symbolCode s))

/-- Read every candidate key directly from the guessed program coordinates. -/
def distinctRows (read : CellReader n a) : BooleanNetwork a 1 :=
  distinctNet (fun j => keySignalsOfOneHot (rowKey read j))

theorem distinctRows_correct {read : CellReader n a} {x : Basis a} {t : Table n}
    (h : read.Agrees x t) : (distinctRows read).eval x 0 = true ↔ t.Distinct := by
  apply distinctNet_correct
  intro j
  apply KeyInputs.Agrees.keySignals
  apply keyInputs_agrees h
  all_goals intros; rw [h]; simp only [Cell.value, RowCell.value, Fin.val_inj, symbolCode_inj.eq_iff]

def distinctRowsBound (n C : ℕ) :=
  let K := (n+3)*(2*((n+1)*(C+4)+1)+5)+1
  n*(n*(K+rowMatchBudget n K+3)+2)+1

theorem distinctRows_count {read : CellReader n a} {C : ℕ} (h : read.Bounded C) :
    (distinctRows read).net.count ≤ distinctRowsBound n C := by
  apply distinctNet_count
  intro j
  apply KeyInputs.Bounded.keySignals
  apply keyInputs_bounded h <;> intros <;> apply h

end Hot
end SignedProgram

end

end SpectralBooks
end LinearAlgebra
end OAI
