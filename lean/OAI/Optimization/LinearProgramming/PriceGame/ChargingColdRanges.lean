import OAI.Optimization.LinearProgramming.PriceGame.ChargingColdLists
import OAI.Optimization.LinearProgramming.PriceGame.LearningAddressMachine
import OAI.Optimization.LinearProgramming.PriceGame.LearningGroupingSort

/-! # Measuring the search ranges from a unary dimension

Only addresses up to `2N²` are enumerated. A binary shift test picks precisely
the addresses belonging to the given depth, so building a table never expands
an unbounded binary shift into an exponentially long word.
-/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Cold

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Learning.GenerationCost States.Mass

theorem flat_guard {A B : Type} (xs : List A) (p : A → Bool) (f : A → List B) :
    xs.flatMap (fun a => if p a then f a else []) = (xs.filter p).flatMap f := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases ha : p a <;> simp [ha,ih]

/-- Filter a framed list with a context while charging each comparison and copy. -/
private noncomputable def selectedP {A C : Type} {ea : A → List Bool} {ec : C → List Bool}
    (da : A) {p : A × C → Bool} (test : Procedure (prodCode ea ec) boolCode p) :
    Procedure (prodCode (listCode ea) ec) (listCode ea) (fun z => z.1.filter fun a => p (a,z.2)) :=
  Learning.BitMachine.filterWithP da (test.comp (swap ec ea))

/-- Filtering an increasing range by a cutoff preserves its exact ordering. -/
theorem filter_range_lt (n k : ℕ) : (List.range n).filter (fun i => decide (i < k)) = List.range (min n k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.filter_append,ih]
    by_cases h : n < k
    · rw [Nat.min_eq_left h.le,Nat.min_eq_left h]
      simp [h,List.range_succ]
    · rw [Nat.min_eq_right (by omega : k ≤ n),Nat.min_eq_right (by omega : k ≤ n+1)]
      simp [h]

/-- Membership in the actual depth range, using a binary shift on the dimension. -/
def atLevel (N k : ℕ) : Bool := if k = 0 then true else decide (0 < N >>> k)

theorem atLevel_eq (N k : ℕ) : atLevel N k = decide (k < depth N) := by
  by_cases hk : k = 0
  · subst k; simp [atLevel,depth]
  by_cases hN : N = 0
  · subst N; simp [atLevel,hk,depth]
  have hpow : 0 < 2^k := by positivity
  simp [atLevel,hk,depth,Nat.shiftRight_eq_div_pow,Nat.div_pos_iff,hpow,← Nat.le_log2 hN]

private noncomputable def atLevelP : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun z => atLevel z.2 z.1) := by
  let arg := prodCode Nat.bits Nat.bits
  let zeroK := binaryZero.comp (first Nat.bits Nat.bits)
  let root := Learning.BitMachine.rootAddressP.comp (swap Nat.bits Nat.bits)
  let positive := binaryLt.comp ((constant arg Nat.bits 0).pair root)
  exact (conditional zeroK (constant arg boolCode true) positive).congrFun
    (by rintro ⟨k,n⟩; simp [atLevel])

/-- The largest necessary public array is quadratic in the materialized dimension. -/
def addressBound (N : ℕ) := 2 * (N * N)

private noncomputable def addressBoundP : Procedure unaryCode unaryCode addressBound := by
  let sq := unaryMul.comp ((identity unaryCode).pair (identity unaryCode))
  exact (unaryMul.comp ((constant unaryCode unaryCode 2).pair sq)).congrFun fun _ => rfl

def rows (N : ℕ) : List Row := (List.range (depth N)).map (fun k => (k,List.range (N * 2^k)))

private theorem vertices_fit {N k : ℕ} (hk : k < depth N) : N * 2^k ≤ addressBound N := by
  by_cases hn : N = 0
  · simp [hn,addressBound]
  have hc := card_vertices_le N k (Nat.pos_of_ne_zero hn) hk.le
  simpa [card_vertices,addressBound,pow_two,Nat.mul_comm] using hc

private theorem allowedRange (N k : ℕ) :
    (List.range (addressBound N)).filter (fun a => decide ((a >>> k) < N)) =
      List.range (min (addressBound N) (N*2^k)) := by
  simpa only [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity : 0<2^k)]
    using filter_range_lt (addressBound N) (N*2^k)

private abbrev RangeEnv := ℕ × List ℕ
private abbrev rangeEnvCode := prodCode Nat.bits (listCode Nat.bits)

private noncomputable def rowP : Procedure (prodCode Nat.bits rangeEnvCode) rowCode
    (fun z : ℕ × RangeEnv => (z.1,z.2.2.filter fun a => decide ((a >>> z.1) < z.2.1))) := by
  let arg := prodCode Nat.bits (prodCode Nat.bits Nat.bits)
  let a := first Nat.bits (prodCode Nat.bits Nat.bits)
  let env := second Nat.bits (prodCode Nat.bits Nat.bits)
  let n := (first Nat.bits Nat.bits).comp env
  let k := (second Nat.bits Nat.bits).comp env
  let test := binaryLt.comp ((Learning.BitMachine.rootAddressP.comp (a.pair k)).pair n)
  let idx := first Nat.bits rangeEnvCode
  let data := second Nat.bits rangeEnvCode
  let candidates := (second Nat.bits (listCode Nat.bits)).comp data
  let n0 := (first Nat.bits (listCode Nat.bits)).comp data
  let valid := (selectedP 0 test).comp (candidates.pair (n0.pair idx))
  exact idx.pair valid

/-- Compile the full depth/vertex table using a physical unary-to-range routine.
No specialized constant for the input dimension appears in the compiled program. -/
noncomputable def rowsFromRangeP (rangeP : Procedure unaryCode (listCode Nat.bits) List.range) :
    Procedure unaryCode (listCode rowCode) rows := by
  let n := unaryToBits
  let levels := (selectedP 0 atLevelP).comp ((rangeP.comp unarySuccessor).pair n)
  let cand := rangeP.comp addressBoundP
  let compiled := (mapContextP 0 emptyRow rowP).comp (levels.pair (n.pair cand))
  apply compiled.congrFun
  intro N
  change ((List.range (N+1)).filter (fun k => atLevel N k)).map
    (fun k => (k,(List.range (addressBound N)).filter (fun a => decide ((a >>> k) < N)))) = rows N
  have hd : depth N ≤ N+1 := Nat.succ_le_succ (Nat.log2_le_self N)
  simp_rw [atLevel_eq]
  rw [filter_range_lt,Nat.min_eq_right hd,rows]
  apply List.map_congr_left
  intro k hk
  rw [allowedRange,Nat.min_eq_right (vertices_fit (List.mem_range.mp hk))]

end Cold
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
