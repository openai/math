import OAI.ThreeFlat.Diagonal.TraceCircuit
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Assembling locally addressed row circuits

Each row's private gates occupy a consecutive block of hidden addresses.
The shared guess prefix carries the register and sort messages that can
be read by different rows. The fixed pins may be placed in any input row.
-/

namespace ThreeFlat.Diagonal.TraceCircuit

variable {F : Type*} {t n c p q b : ℕ}

/-- Consecutive block addressing of the private wire array. -/
def blocks (t n : ℕ) : (Fin t → Fin n → Bool) ≃ (Fin (t*n) → Bool) :=
  (Equiv.curry _ _ _).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl _))

@[simp] theorem blocks_at (ws : Fin t → Fin n → Bool) (i : Fin t) (j : Fin n) :
    blocks t n ws (finProdFinEquiv (i,j)) = ws i j := by simp [blocks]

/-- Translate a local operand. A hidden input at the row boundary addresses
a shared message, while a private gate refers to the same row only. -/
def rowAddress (i : Fin t) (inputs : Fin t → Fin q → BitSource b p) :
    BitSource n q → BitSource (b + t*n) p
  | .constant v => .constant v
  | .hidden j => .hidden (Fin.natAdd b (finProdFinEquiv (i,j)))
  | .pin j =>
    match inputs i j with
    | .constant v => .constant v
    | .pin k => .pin k
    | .hidden k => .hidden (k.castAdd (t*n))

private theorem rowAddress_read (i : Fin t) (inputs : Fin t → Fin q → BitSource b p)
    (a : BitSource n q) (pin : Fin p → Bool) (guess : Fin b → Bool) (ws : Fin t → Fin n → Bool) :
    (rowAddress i inputs a).read (Fin.append guess (blocks t n ws)) pin =
      a.read (ws i) (fun j => (inputs i j).read guess pin) := by
  cases a with
  | constant v => rfl
  | hidden j => simp [rowAddress, BitSource.read]
  | pin j => cases h : inputs i j <;> simp [rowAddress, BitSource.read, h]

/-- Combine `t` row verifiers. They have `t*c` cells and exactly `b+t*n`
hidden bits, including the unique shared copy of each boundary guess. -/
def assemble (rows : Fin t → Fin c → Cell F n q) (inputs : Fin t → Fin q → BitSource b p) :
    BitNetwork F p where
  internal := b+t*n
  cells := t*c
  source k j := let ij := finProdFinEquiv.symm k
                rowAddress ij.1 inputs ((rows ij.1 ij.2).source j)
  table k := let ij := finProdFinEquiv.symm k
             (rows ij.1 ij.2).table

/-- For fixed shared and private bits, the entire array factors by row. -/
theorem assemble_weight [CommMonoid F] (rows : Fin t → Fin c → Cell F n q)
    (inputs : Fin t → Fin q → BitSource b p) (pin : Fin p → Bool)
    (guess : Fin b → Bool) (ws : Fin t → Fin n → Bool) :
    (assemble rows inputs).weight pin (Fin.append guess (blocks t n ws)) =
      ∏ i, ∏ j, (rows i j).eval (fun k => (inputs i k).read guess pin) (ws i) := by
  let term := (assemble rows inputs).factor pin (Fin.append guess (blocks t n ws))
  change (∏ k : Fin (t*c), term k) = _
  rw [← finProdFinEquiv.prod_comp term, Fintype.prod_prod_type]
  simp [term, BitNetwork.factor, assemble, Cell.eval, rowAddress_read]

/-- Summing local deterministic wires or local private guesses occurs inside
each row. All rows read one common setting of the public boundary messages. -/
theorem assemble_eval [CommSemiring F] (rows : Fin t → Fin c → Cell F n q)
    (inputs : Fin t → Fin q → BitSource b p) (pin : Fin p → Bool) :
    (assemble rows inputs).eval pin =
      ∑ guess : Fin b → Bool, ∏ i, ∑ ws : Fin n → Bool,
        ∏ j, (rows i j).eval (fun k => (inputs i k).read guess pin) ws := by
  classical
  let f := (assemble rows inputs).weight pin
  change (∑ x : Fin (b+t*n) → Bool, f x) = _
  rw [← (Fin.appendEquiv (α := Bool) b (t*n)).sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro guess _
  change (∑ z : Fin (t*n) → Bool, f (Fin.append guess z)) = _
  rw [← (blocks t n).sum_comp (fun z => f (Fin.append guess z)), Fintype.prod_sum]
  exact Finset.sum_congr rfl fun ws _ => assemble_weight rows inputs pin guess ws

end ThreeFlat.Diagonal.TraceCircuit

end OAI
