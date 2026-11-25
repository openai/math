import OAI.Computability.NearSquareRoot.KernelPassBank
import OAI.Computability.NearSquareRoot.KernelPassAxes

/-! # Finite row matrices selected by the frequency signature

All entries of a fixed rectangular table can be applied at each streamed
address. The selector uses only the xor-sum of fixed per-column queries.
Conversions to and from the frequency domain charge each basis row once.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Plan

open Matrix Finset

variable {A h i o m n : ℕ}

/-- Execute a finite family of single-output plans on copies of the input bank. -/
def collect : (n : ℕ) → (Fin n → Plan A i 1) → Plan A i n
  | 0, _ => .mix (fun j => Fin.elim0 j)
  | n+1, p => (collect n (fun j => p j.castSucc)).fork (p (Fin.last n))

theorem applyAt_collect (p : Fin n → Plan A i 1) (x : Bank A h i) (b : Fin n) :
    (collect n p).applyAt h x b = (p b).applyAt h x 0 := by
  induction n with
  | zero => exact Fin.elim0 b
  | succ n ih =>
    rw [collect, applyAt_fork]
    refine Fin.lastCases ?_ (fun j => ?_) b
    · change Fin.append _ _ (Fin.natAdd n (0 : Fin 1)) = _
      rw [Fin.append_right]
    · change Fin.append _ _ (Fin.castAdd 1 j) = _
      rw [Fin.append_left, ih]

@[simp] theorem calls_collect (p : Fin n → Plan A i 1) :
    (collect n p).calls = ∑ j, (p j).calls := by
  induction n with
  | zero => simp [collect, calls]
  | succ n ih => rw [collect, calls_fork, ih, Fin.sum_univ_castSucc]

/-- Apply an independent one-row plan to each row. -/
def perRow (p : Fin n → Plan A 1 1) : Plan A n n :=
  collect n fun j => (p j).seq (route (fun _ => j))

theorem applyAt_perRow (p : Fin n → Plan A 1 1) (x : Bank A h n) (b : Fin n) :
    (perRow p).applyAt h x b = (p b).applyAt h (fun _ => x b) 0 := by
  rw [perRow, applyAt_collect, applyAt_seq, applyAt_route]
  rfl

@[simp] theorem calls_perRow (p : Fin n → Plan A 1 1) :
    (perRow p).calls = ∑ j, (p j).calls := by
  simp [perRow, calls]

theorem applyAt_scale (test : Column A → Fin m → ZMod 2)
    (c : (Fin m → ZMod 2) → Coefficient) (x : Bank A h 1) (b : Fin 1) (y : Addr A h) :
    (scale m test c).applyAt h x b y = value (c (∑ t, test (y t))) * x 0 y := by
  simp [applyAt, eval, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

/-- Apply the selected rectangular matrix to the rows at each address. -/
def matrixTable (test : Column A → Fin m → ZMod 2)
    (c : (Fin m → ZMod 2) → Fin o → Fin i → Coefficient) : Plan A i o :=
  collect o fun b => (Plan.mix (fun _ _ => (1,0))).seq
    (collect i fun a => (scale m test (fun k => c k b a)).seq (route fun _ => a))

@[simp] theorem calls_matrixTable (test : Column A → Fin m → ZMod 2)
    (c : (Fin m → ZMod 2) → Fin o → Fin i → Coefficient) :
    (matrixTable test c).calls = 0 := by simp [matrixTable, calls]

theorem applyAt_matrixTable (test : Column A → Fin m → ZMod 2)
    (c : (Fin m → ZMod 2) → Fin o → Fin i → Coefficient)
    (x : Bank A h i) (b : Fin o) (y : Addr A h) :
    (matrixTable test c).applyAt h x b y =
      ∑ a, value (c (∑ t, test (y t)) b a) * x a y := by
  simp [matrixTable, applyAt_collect, applyAt_seq, applyAt_mix, applyAt_scale, applyAt_route, value]

/-- Change each row between the stream and frequency bases. -/
def convertBank (A n : ℕ) : Plan A n n := perRow fun _ => fullConversion (List.finRange A)

@[simp] theorem calls_convertBank (A n : ℕ) : (convertBank A n).calls = n*A := by
  simp [convertBank, calls_fullConversion]

/-- One forward and one backward conversion on the check rows. -/
def spectralTable (test : Column A → Fin m → ZMod 2)
    (c : (Fin m → ZMod 2) → Fin o → Fin i → Coefficient) : Plan A i o :=
  (convertBank A o).seq ((matrixTable test c).seq (convertBank A i))

@[simp] theorem calls_spectralTable (test : Column A → Fin m → ZMod 2)
    (c : (Fin m → ZMod 2) → Fin o → Fin i → Coefficient) :
    (spectralTable test c).calls = o*A+i*A := by simp [spectralTable, calls]

end KernelPass.Plan

end NearSquareRoot
end Computability
end OAI
