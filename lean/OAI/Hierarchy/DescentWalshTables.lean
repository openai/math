import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace OAI
/-! # Finite binary Walsh transform with a counted butterfly implementation -/

namespace Hierarchy.DescentWalshTables
open scoped BigOperators

abbrev Bits (k : ℕ) := Fin k → ZMod 2

/-- The two subtrees contain the entries of a table with first bit zero and one. -/
inductive Table (R : Type*) : ℕ → Type _
  | scalar (value : R) : Table R 0
  | branch {k : ℕ} (low high : Table R k) : Table R (k+1)

namespace Table
variable {R : Type*}

def read : {k : ℕ} → Table R k → Bits k → R
  | 0,.scalar a,_ => a
  | _+1,.branch lo hi,x => if x 0=0 then read lo (Fin.tail x) else read hi (Fin.tail x)

def tabulate : (k : ℕ) → (Bits k → R) → Table R k
  | 0,f => .scalar (f Fin.elim0)
  | k+1,f => .branch (tabulate k fun x=>f (Fin.cons 0 x)) (tabulate k fun x=>f (Fin.cons 1 x))

theorem tabulate_read (k : ℕ) (f : Bits k→R) (x : Bits k) : read (tabulate k f) x = f x := by
  induction k with
  | zero => exact congrArg f (Subsingleton.elim _ _)
  | succ k ih =>
    rw [tabulate,read]
    have rebuild (b : ZMod 2) (hb : x 0=b) : Fin.cons b (Fin.tail x)=x := by
      rw [←hb,Fin.cons_self_tail]
    by_cases first : x 0=0
    · simp only [first,ite_true,ih,rebuild _ first]
    · have one : x 0=1 := by
        have ex : ∀ z : ZMod 2,z=0 ∨ z=1 := by decide
        exact (ex _).resolve_left first
      simp only [first,ite_false,ih,rebuild _ one]

/-- Evaluate one binary operation at each table entry and count its applications. -/
def combine (op : R→R→R) : {k : ℕ} → Table R k → Table R k → Table R k × ℕ
  | 0,.scalar a,.scalar b => (.scalar (op a b),1)
  | _+1,.branch a b,.branch c d =>
    let lo := combine op a c
    let hi := combine op b d
    (.branch lo.1 hi.1,lo.2+hi.2)

theorem combine_cost (op : R→R→R) {k : ℕ} (a b : Table R k) : (combine op a b).2=2^k := by
  induction a with
  | scalar a => cases b; rfl
  | @branch k a c ha hc =>
    cases b with | branch b d =>
      simp only [combine,ha,hc,pow_succ]
      omega

theorem combine_read (op : R→R→R) {k : ℕ} (a b : Table R k) (x : Bits k) :
    read (combine op a b).1 x = op (read a x) (read b x) := by
  induction a with
  | scalar a => cases b; rfl
  | @branch k a c ha hc =>
    cases b with | branch b d =>
      by_cases first : x 0=0 <;> simp [combine,read,first,ha,hc]

/-- Both recursive results are computed once, then shared by the two output halves. -/
def transform [AddGroup R] : {k : ℕ} → Table R k → Table R k × ℕ
  | 0,.scalar a => (.scalar a,0)
  | _+1,.branch a b =>
    let lo := transform a
    let hi := transform b
    let plus := combine (·+·) lo.1 hi.1
    let minus := combine (·-·) lo.1 hi.1
    (.branch plus.1 minus.1,lo.2+hi.2+plus.2+minus.2)

theorem transform_cost [AddGroup R] {k : ℕ} (t : Table R k) :
    (transform t).2 = k*2^k := by
  induction t with
  | scalar => rfl
  | @branch k a b ha hb =>
    simp only [transform,ha,hb,combine_cost,pow_succ]
    ring

end Table

noncomputable def character : (k : ℕ) → Bits k → Bits k → ℝ
  | 0,_,_ => 1
  | k+1,f,x =>
    (if f 0≠0 ∧ x 0≠0 then -1 else 1) * character k (Fin.tail f) (Fin.tail x)

theorem sum_first_bit {k : ℕ} (f : Bits (k+1)→ℝ) :
    ∑ x,f x = (∑ x : Bits k,f (Fin.cons 0 x)) + (∑ x : Bits k,f (Fin.cons 1 x)) := by
  let e := Fin.consEquiv (fun _ : Fin (k+1)=>ZMod 2)
  rw [←e.sum_comp f,Fintype.sum_prod_type]
  exact Fin.sum_univ_two _

/-- The output at every index is its Walsh coefficient of the original table. -/
theorem transform_read {k : ℕ} (t : Table ℝ k) (f : Bits k) :
    (Table.transform t).1.read f = ∑ x,character k f x * t.read x := by
  induction t with
  | scalar a => simp [Table.transform,Table.read,character]
  | @branch k a b ha hb =>
    rw [sum_first_bit]
    by_cases first : f 0=0
    · simp [Table.transform,Table.read,Table.combine_read,character,first,ha,hb]
    · simp [Table.transform,Table.read,Table.combine_read,character,first,ha,hb,sub_eq_add_neg]

end Hierarchy.DescentWalshTables

end OAI
