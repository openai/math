import OAI.Hierarchy.DescentRowScore
import OAI.Hierarchy.DescentWalshTables
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Pi

namespace OAI
/-! # Computing the autocorrelation and all next-row scores by Walsh transforms -/

namespace Hierarchy.DescentWalshTables
open scoped BigOperators Classical
noncomputable section

/-- The binary functional determined by the concrete coefficients of a row. -/
def binaryRow {k : ℕ} (f : Bits k) : Bits k →ₗ[ZMod 2] ZMod 2 :=
  ∑ i,f i • LinearMap.proj i

theorem binaryRow_apply {k : ℕ} (f x : Bits k) : binaryRow f x = ∑ i,f i*x i := by
  simp [binaryRow,LinearMap.sum_apply]

def sign (z : ZMod 2) : ℝ := if z=0 then 1 else -1

theorem sign_add (a b : ZMod 2) : sign (a+b)=sign a * sign b := by
  have bits : ∀ z : ZMod 2,z=0 ∨ z=1 := by decide
  have eleven : (1:ZMod 2)+1=0 := by decide
  rcases bits a with rfl|rfl <;> rcases bits b with rfl|rfl <;> simp [sign,eleven]

theorem character_row {k : ℕ} (f x : Bits k) : character k f x = sign (binaryRow f x) := by
  rw [binaryRow_apply]
  induction k with
  | zero => simp [character,sign]
  | succ k ih =>
    rw [Fin.sum_univ_succ,sign_add]
    change (if f 0≠0 ∧ x 0≠0 then -1 else 1) * character k (Fin.tail f) (Fin.tail x) =
      sign (f 0*x 0) * sign (∑ i,Fin.tail f i * Fin.tail x i)
    rw [ih]
    congr 1
    by_cases h : f 0=0 <;> by_cases l : x 0=0 <;> simp [sign,h,l]

theorem character_add {k : ℕ} (f x y : Bits k) :
    character k f (x+y) = character k f x * character k f y := by
  simp only [character_row,map_add,sign_add]

theorem character_symm {k : ℕ} (f x : Bits k) : character k f x=character k x f := by
  simp only [character_row,binaryRow_apply,mul_comm]

theorem character_orthogonal {k : ℕ} (d : Bits k) :
    (∑ f,character k f d) = if d=0 then (2:ℝ)^k else 0 := by
  induction k with
  | zero =>
    have h : d=0 := Subsingleton.elim _ _
    simp [character,h]
  | succ k ih =>
    rw [sum_first_bit]
    have zeros : d=0 ↔ d 0=0 ∧ Fin.tail d=0 := by
      constructor
      · rintro rfl; exact ⟨rfl,rfl⟩
      · rintro ⟨a,b⟩
        funext i
        exact Fin.cases a (fun j=>congrFun b j) i
    by_cases first : d 0=0
    · by_cases rest : Fin.tail d=0 <;>
        simp [character,first,zeros,rest,ih,pow_succ]; ring
    · simp [character,first,zeros]

def coefficient {k : ℕ} (x : Bits k → ℝ) (f : Bits k) : ℝ := ∑ z,character k f z * x z

theorem coefficient_eq_walsh {k : ℕ} (x : Bits k→ℝ) (f : Bits k) :
    coefficient x f = DescentRowScore.walsh (binaryRow f) x := by
  simp [coefficient,DescentRowScore.walsh,character_row,sign]

private theorem self_add_zero {k : ℕ} (d : Bits k) : d+d=0 := by
  funext i
  exact CharTwo.add_self_eq_zero (d i)

private theorem add_eq_zero {k : ℕ} (x y : Bits k) : x+y=0 ↔ x=y := by
  constructor
  · intro h
    calc
      x = x+(y+y) := by rw [self_add_zero,add_zero]
      _ = y := by rw [←add_assoc,h,zero_add]
  · rintro rfl
    exact self_add_zero _

/-- Orthogonality yields the inverse transform by a second identical butterfly. -/
theorem coefficient_twice {k : ℕ} (x : Bits k→ℝ) (d : Bits k) :
    coefficient (coefficient x) d = 2^k*x d := by
  unfold coefficient
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j,(∑ f,character k f (d+j))*x j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro f _
      rw [character_add,character_symm d f]
      ring
    _ = _ := by
      simp [character_orthogonal,add_eq_zero,ite_mul]

/-- Input autocorrelation transforms into the pointwise square of the spectrum. -/
theorem coefficient_correlation {k : ℕ} (x : Bits k→ℝ) (f : Bits k) :
    coefficient (DescentRowScore.autocorrelation x) f = (coefficient x f)^2 := by
  unfold coefficient DescentRowScore.autocorrelation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm,pow_two,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Fintype.sum_equiv (Equiv.addLeft i)
  intro d
  change character k f d*(x i*x (i+d)) =
    character k f i*x i*(character k f (i+d)*x (i+d))
  have cancel : character k f i * character k f (i+d) = character k f d := by
    rw [←character_add,←add_assoc,self_add_zero,zero_add]
  linear_combination -(x i*x (i+d))*cancel

/-- This formula computes every off-diagonal coefficient at once, including
the diagonal at zero. There are two transforms and one squaring per entry. -/
theorem correlation_by_transforms {k : ℕ} (x : Bits k→ℝ) (d : Bits k) :
    coefficient (fun f=>(coefficient x f)^2) d / 2^k = DescentRowScore.autocorrelation x d := by
  simp_rw [←coefficient_correlation]
  rw [coefficient_twice]
  field_simp

/-- The shared two-transform algorithm. Its normalization scalar is fixed by
the dimension. The counter records scalar additions, subtractions,
multiplications and divisions. -/
def correlationTable {k : ℕ} (t : Table ℝ k) : Table ℝ k × ℕ :=
  let first := t.transform
  let squares := Table.combine (·*·) first.1 first.1
  let second := squares.1.transform
  let normalized := Table.combine (·/·) second.1 (Table.tabulate k (fun _=>2^k))
  (normalized.1,first.2+squares.2+second.2+normalized.2)

theorem correlationTable_cost {k : ℕ} (t : Table ℝ k) :
    (correlationTable t).2=(2*k+2)*2^k := by
  simp only [correlationTable,Table.transform_cost,Table.combine_cost]
  ring

theorem correlationTable_read {k : ℕ} (t : Table ℝ k) (d : Bits k) :
    (correlationTable t).1.read d=DescentRowScore.autocorrelation t.read d := by
  have forward (u : Table ℝ k) (i : Bits k) :
      u.transform.1.read i=coefficient u.read i := transform_read u i
  change (Table.combine (·/·) _ _).1.read d=_
  simp only [Table.combine_read,Table.tabulate_read,forward]
  convert! correlation_by_transforms t.read d using 2
  apply congrArg (fun g : Bits k→ℝ=>coefficient g d)
  funext i
  simp [Table.combine_read,forward,pow_two]

end
end Hierarchy.DescentWalshTables

end OAI
