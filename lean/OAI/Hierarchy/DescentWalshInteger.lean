import OAI.Hierarchy.DescentWalshCorrelation

namespace OAI
/-! # Integer butterfly tables for the compiler's prefix scorer -/

namespace Hierarchy.DescentWalshTables
open scoped BigOperators

/-- The integral input is maintained through both butterflies. -/
def integerNumerator {k : ℕ} (t : Table ℤ k) : Table ℤ k × ℕ :=
  let first := t.transform
  let squares := Table.combine (·*·) first.1 first.1
  let second := squares.1.transform
  (second.1, first.2+squares.2+second.2)

/-- The final division is exact entry by entry. -/
def integerCorrelation {k : ℕ} (t : Table ℤ k) : Table ℤ k × ℕ :=
  let numerator := integerNumerator t
  let result := Table.combine (·/·) numerator.1 (Table.tabulate k fun _=>2^k)
  (result.1,numerator.2+result.2)

theorem integerCorrelation_cost {k : ℕ} (t : Table ℤ k) :
    (integerCorrelation t).2=(2*k+2)*2^k := by
  simp only [integerCorrelation,integerNumerator,Table.transform_cost,Table.combine_cost]
  ring

theorem integerTransform_cast {k : ℕ} (t : Table ℤ k) (f : Bits k) :
    ((t.transform.1.read f:ℤ):ℝ)=coefficient (fun i=>(t.read i:ℝ)) f := by
  induction t with
  | scalar a => simp [Table.transform,Table.read,coefficient,character]
  | @branch k a b ha hb =>
    rw [coefficient,sum_first_bit]
    by_cases first : f 0=0
    · simp [Table.transform,Table.read,Table.combine_read,character,first,ha,hb,coefficient]
    · simp [Table.transform,Table.read,Table.combine_read,character,first,ha,hb,coefficient,sub_eq_add_neg]

theorem integerNumerator_exact {k : ℕ} (t : Table ℤ k) (d : Bits k) :
    (integerNumerator t).1.read d = 2^k * (∑ i,t.read i*t.read (i+d)) := by
  let x (i : Bits k) : ℝ := t.read i
  have squares (i : Bits k) : ((Table.combine (·*·) t.transform.1 t.transform.1).1.read i : ℝ)
      = (coefficient x i)^2 := by simp [Table.combine_read,integerTransform_cast,x,pow_two]
  have casted : ((integerNumerator t).1.read d : ℝ) = 2^k * ∑ i,x i*x (i+d) := by
    rw [integerNumerator,integerTransform_cast]
    simp_rw [squares,←coefficient_correlation]
    exact coefficient_twice (DescentRowScore.autocorrelation x) d
  dsimp only [x] at casted
  exact_mod_cast casted

theorem integerCorrelation_read {k : ℕ} (t : Table ℤ k) (d : Bits k) :
    (integerCorrelation t).1.read d = ∑ i,t.read i*t.read (i+d) := by
  simp only [integerCorrelation,Table.combine_read,Table.tabulate_read,integerNumerator_exact]
  exact Int.mul_ediv_cancel_left _ (by positivity)

end Hierarchy.DescentWalshTables

end OAI
