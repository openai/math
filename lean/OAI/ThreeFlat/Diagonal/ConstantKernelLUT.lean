import OAI.ThreeFlat.Diagonal.TraceCircuitArray
import OAI.Computability.QuantumFactoring.BitEncoding
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace OAI
/-! # Trivalent records for an arbitrary fixed finite kernel

For each pattern `s`, a private branch contributes `(f s - 1)` only when
the input is `s`. The other branch contributes one. Multiplying these
tests leaves exactly the coefficient in the matching row of the table.
The resource constants depend only on the binary arity of the base motif.
-/

namespace ThreeFlat.Diagonal.ConstantKernelLUT

open TraceCircuit
open scoped BigOperators

variable {F : Type*} [CommRing F] {n : ℕ}

private def single : Bool ≃ (Fin 1 → Bool) where
  toFun b := fun _ => b
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := funext fun i => congrArg f (Subsingleton.elim _ i)

private def first (a : F) : Cell F 1 n :=
  ⟨fun _ => .hidden 0, fun z => if z 0 then a - 1 else 1⟩

private def test (t : Fin n → Bool) (i : Fin n) : Cell F 1 n :=
  ⟨![.hidden 0, .pin i, .constant false], fun z => if z 0 = true ∧ z 1 ≠ t i then 0 else 1⟩

private def records (t : Fin n → Bool) (a : F) : Fin (n+1) → Cell F 1 n :=
  Fin.cases (first a) (test t)

private theorem records_eval (t pin : Fin n → Bool) (a : F) :
    (∑ g : Fin 1 → Bool, ∏ j, (records t a j).eval pin g) =
      if pin = t then a else 1 := by
  rw [← single.sum_comp, Fintype.sum_bool]
  simp only [Fin.prod_univ_succ, records, Fin.cases_zero, Fin.cases_succ]
  have nil : (∏ j, (test (F := F) t j).eval pin (single false)) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    simp [test, Cell.eval, single, BitSource.read]
  rw [nil]
  by_cases he : pin = t
  · subst t
    have ok : (∏ j, (test (F := F) pin j).eval pin (single true)) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      simp [test, Cell.eval, single, BitSource.read]
    rw [ok]
    simp [first, Cell.eval, single, BitSource.read]
  · obtain ⟨j,hj⟩ : ∃ j, pin j ≠ t j := not_forall.mp (fun h => he (funext h))
    have bad : (∏ k, (test (F := F) t k).eval pin (single true)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [test, Cell.eval, single, BitSource.read, hj])
    rw [bad]
    simp [first, Cell.eval, single, BitSource.read, he]

private def index (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (ExactQuantumFactoring.bitsEquiv n).trans BitVec.equivFin.toEquiv

/-- The one fixed trivalent circuit computing an arbitrary field-valued lookup table. -/
def network (f : (Fin n → Bool) → F) : BitNetwork F n :=
  TraceCircuit.assemble (b := 0)
    (fun i : Fin (2^n) => records ((index n).symm i) (f ((index n).symm i)))
    (fun _ j => .pin j)

@[simp] theorem network_internal (f : (Fin n → Bool) → F) :
    (network f).internal = 2 ^ n := by simp [network, TraceCircuit.assemble]

@[simp] theorem network_cells (f : (Fin n → Bool) → F) :
    (network f).cells = 2 ^ n * (n + 1) := rfl

/-- The same circuit layout works for every setting of the motif coefficients. -/
theorem network_eval (f : (Fin n → Bool) → F) (pin : Fin n → Bool) :
    (network f).eval pin = f pin := by
  classical
  unfold network
  rw [TraceCircuit.assemble_eval]
  simp only [BitSource.read, records_eval, Fintype.sum_unique]
  rw [← (index n).prod_comp]
  simp

end ThreeFlat.Diagonal.ConstantKernelLUT

end OAI
