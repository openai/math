import OAI.Computability.QuantumFactoring.BitStackGCD
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackListLength
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentBits
import Mathlib.Data.List.FinRange

/-! # Compiling binary transshipment capacity schedules to bit stacks

A pass reads each expert's low bit and divides its remaining capacity by two.
Prepending the bit row yields most-significant-first order. The iteration bound
is the binary length of the encoded capacity list, so there is no unary loop
over numerical capacities.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace ScheduleMachine
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

abbrev Plane := List Bool
abbrev planeCode : Plane → List Bool := listCode boolCode
abbrev PlaneState := List ℕ × List Plane
abbrev stateCode : PlaneState → List Bool := prodCode (listCode Nat.bits) (listCode planeCode)

def low (q : ℕ) : Bool := q % 2 == 1

def advance (s : PlaneState) : PlaneState :=
  (s.1.map (· / 2), (s.1.map low) :: s.2)

noncomputable def halfP : Procedure Nat.bits Nat.bits (fun n => n / 2) :=
  binaryDiv.comp ((identity Nat.bits).pair (constant Nat.bits Nat.bits 2))

noncomputable def lowP : Procedure Nat.bits boolCode low := by
  let dec := binaryMod.comp ((identity Nat.bits).pair (constant Nat.bits Nat.bits 2))
  exact (boolNot.comp (binaryZero.comp dec)).congrFun (by
    intro n
    have hm := Nat.mod_lt n (by decide : 0 < 2)
    by_cases h : n % 2 = 0
    · simp [low, h]
    · have h₁ : n % 2 = 1 := by omega
      simp [low, h₁])

noncomputable def advanceP : Procedure stateCode stateCode advance := by
  let qs := first (listCode Nat.bits) (listCode planeCode)
  let rows := second (listCode Nat.bits) (listCode planeCode)
  let half := (listMap 0 0 halfP).comp qs
  let bits := (listMap 0 false lowP).comp qs
  exact half.pair ((listCons planeCode).comp (bits.pair rows))

private theorem half_length (xs : List ℕ) :
    (listCode Nat.bits (xs.map (· / 2))).length ≤ (listCode Nat.bits xs).length := by
  induction xs with
  | nil => simp [listCode]
  | cons a xs ih =>
    have h := Nat.size_le_size (Nat.div_le_self a 2)
    simp only [List.map_cons, listCode_length_cons, Nat.size_eq_bits_len]
    omega

private theorem plane_length (xs : List ℕ) : (planeCode (xs.map low)).length = 4 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (listCode boolCode (low a :: xs.map low)).length = _
    rw [listCode_length_cons]
    change 2 * 1 + 2 + (planeCode (xs.map low)).length = _
    simp [ih, Nat.mul_add]; omega

private theorem advance_width (s : PlaneState) :
    (stateCode (advance s)).length ≤ (stateCode s).length + (8*s.1.length + 4) := by
  rcases s with ⟨xs, rows⟩
  have hh := half_length xs
  simp only [advance, stateCode, prodCode, pairBits_length, listCode_length_cons]
  rw [plane_length]; omega

private theorem unchanged_length (i : ℕ) (s : PlaneState) :
    ((advance^[i]) s).1.length = s.1.length := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [Function.iterate_succ_apply', advance] using ih

private theorem iterate_width (i : ℕ) (s : PlaneState) :
    (stateCode ((advance^[i]) s)).length ≤ (stateCode s).length + i*(8*s.1.length+4) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', Nat.succ_mul]
    have h := advance_width ((advance^[i]) s)
    rw [unchanged_length] at h
    omega

def planes : ℕ → List ℕ → List Plane
  | 0, _ => []
  | k+1, qs => planes k (qs.map (·/2)) ++ [qs.map low]

theorem iterate_planes (qs : List ℕ) (out : List Plane) (k : ℕ) :
    ((advance^[k]) (qs,out)).2 = planes k qs ++ out := by
  induction k generalizing qs out with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    simpa [planes, advance, List.append_assoc] using ih (qs.map (·/2)) ((qs.map low)::out)

/-- A polynomial-time bit machine for the padded bit rows with explicit width. -/
noncomputable def planesP : Procedure (prodCode unaryCode (listCode Nat.bits)) (listCode planeCode)
    (fun input => planes input.1 input.2) := by
  let q : Polynomial ℕ := Polynomial.X + Polynomial.X * (8 * Polynomial.X + 4)
  let loop := advanceP.iterate q (by
    intro n s i hi
    have h := iterate_width i s
    have hs : s.1.length ≤ (stateCode s).length := by
      have hq := list_length_le_code Nat.bits s.1
      simp only [stateCode, prodCode, pairBits_length]
      omega
    simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    apply h.trans
    gcongr <;> omega)
  let width := first unaryCode (listCode Nat.bits)
  let capacities := second unaryCode (listCode Nat.bits)
  let empty := constant (prodCode unaryCode (listCode Nat.bits)) (listCode planeCode) []
  let init := width.pair (capacities.pair empty)
  exact ((second (listCode Nat.bits) (listCode planeCode)).comp (loop.comp init)).congrFun
    (by intro x; exact (iterate_planes x.2 [] x.1).trans (List.append_nil _))

/-- Padding by the encoded input length is computed from the word itself, with
at most one loop iteration per input bit. -/
noncomputable def paddedPlanesP : Procedure (listCode Nat.bits) (listCode planeCode)
    (fun qs => planes (listCode Nat.bits qs).length qs) :=
  planesP.comp ((Procedure.length.precompose (listCode Nat.bits)).pair (identity (listCode Nat.bits)))

private theorem member_bits {qs : List ℕ} {n : ℕ} (h : n ∈ qs) :
    n.bits.length ≤ (listCode Nat.bits qs).length := by
  induction qs with
  | nil => simp at h
  | cons a as ih =>
    rw [listCode_length_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem padding_fits {m : ℕ} (qty : Fin m → ℕ) (j : Fin m) :
    qty j < 2 ^ (listCode Nat.bits ((List.finRange m).map qty)).length := by
  apply Nat.size_le.mp
  have hh := member_bits (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩ :
    qty j ∈ (List.finRange m).map qty)
  simpa only [Nat.size_eq_bits_len] using hh

/-- Reading each bit row in expert order yields precisely the solver's unit instructions. -/
def rowActions (m : ℕ) (row : Plane) : List (Option (Fin m)) :=
  none :: ((List.finRange m).filter (fun i => row[i.val]?.getD false)).map some

private theorem actions_low {m : ℕ} (qty : Fin m → ℕ) :
    rowActions m (((List.finRange m).map qty).map low) = none :: (Augment.oddExperts qty).map some := by
  have hh : (fun i : Fin m => (((List.finRange m).map qty).map low)[i.val]?.getD false) =
      fun i => qty i % 2 == 1 := by
    funext i
    simp [List.finRange, low, i.isLt]
  simp only [rowActions, Augment.oddExperts, hh]

theorem planes_expand {m : ℕ} (k : ℕ) (qty : Fin m → ℕ) :
    (planes k ((List.finRange m).map qty)).flatMap (rowActions m) = Augment.schedule k qty := by
  induction k generalizing qty with
  | zero => rfl
  | succ k ih =>
    simp only [planes, List.flatMap_append, List.flatMap_singleton, Augment.schedule, actions_low]
    congr 1
    simpa only [List.map_map, Function.comp_def] using ih (fun i => qty i / 2)

end ScheduleMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
