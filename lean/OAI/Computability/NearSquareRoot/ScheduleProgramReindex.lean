import OAI.Computability.NearSquareRoot.InterchangeSplitCompose
import Mathlib.SetTheory.Cardinal.Finite

/-! # Numbering arbitrary finite controls for the candidate interpreter -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal.Reindex

open IntegerMultiplication
open TapeSequence (relabel)

variable {A Q R I : Type}

/-- Number the states and place the designated entry in the first program-table row. -/
def numbering {n : ℕ} (e : Q ≃ Fin n) (start : Q) : Q ≃ Fin n :=
  e.trans (Equiv.swap (e start) ⟨0,Nat.zero_lt_of_lt (e start).isLt⟩)

@[simp] theorem numbering_start {n : ℕ} (e : Q ≃ Fin n) (start : Q) :
    numbering e start start = ⟨0,Nat.zero_lt_of_lt (e start).isLt⟩ := by
  simp [numbering]

noncomputable def finiteNumbering [Finite Q] (start : Q) : Q ≃ Fin (Nat.card Q) :=
  numbering (Finite.equivFin Q) start

@[simp] theorem finiteNumbering_start [Finite Q] (start : Q) :
    (finiteNumbering start start).val = 0 := by simp [finiteNumbering]

/-- Relabel only the finite control, keeping the alphabet, tape indices and actions. -/
def rule (e : Q ≃ R) (m : TM.Rule A Q I) : TM.Rule A R I :=
  fun q read => (m (e.symm q) read).map fun op => (e op.1, op.2)

theorem advance (e : Q ≃ R) (m : TM.Rule A Q I) (x : TM.Config A Q I) :
    TM.advance (rule e m) (relabel e x) = (TM.advance m x).map (relabel e) := by
  simp [rule, TM.advance, relabel, Option.map_map, Function.comp_def]

theorem trace (e : Q ≃ R) (m : TM.Rule A Q I) {x y : TM.Config A Q I} {n : ℕ}
    (h : Trace (TM.advance m) x n y) :
    Trace (TM.advance (rule e m)) (relabel e x) n (relabel e y) := by
  induction h with
  | nil => exact .nil _
  | cons step _ ih => exact .cons (by rw [advance,step]; rfl) ih

@[simp] theorem inverse_rule (e : Q ≃ R) (m : TM.Rule A Q I) : rule e.symm (rule e m) = m := by
  funext q r
  simp [rule]
  cases m q r <;> simp

@[simp] theorem inverse_relabel (e : Q ≃ R) (x : TM.Config A Q I) :
    relabel e.symm (relabel e x) = x := by simp [relabel]

theorem halt_iff (e : Q ≃ R) (m : TM.Rule A Q I) (x : TM.Config A Q I) :
    TM.advance (rule e m) (relabel e x) = none ↔ TM.advance m x = none := by simp [advance]

theorem visits (e : Q ≃ R) (m : TM.Rule A Q I) (x : TM.Config A Q I) (n s : ℕ)
    (h : VisitsAtMost m x n s) : VisitsAtMost (rule e m) (relabel e x) n s := by
  obtain ⟨cells,hcard,cover⟩ := h
  refine ⟨cells,hcard,?_⟩
  intro t ht z hz i
  have h' := trace e.symm _ hz
  exact cover t ht (relabel e.symm z) (by simpa using h') i

end Universal.Reindex

end NearSquareRoot
end Computability
end OAI
