import OAI.Computability.VPVNP.RankQueryStackWords

/-!
# Fixed arithmetic code for Schur node dispatch

The same decision trees serve every matrix size and every bidegree. Input
registers zero through five hold the query, register six is the product-loop
counter, and register seven is the matrix height. The child routine selects a
side and returns the six registers of that child. The description routine
returns a scalar, a scalar-entry request, or the arity of the product sum.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Dispatch

/-- Natural-number arithmetic operations available in Schur dispatch expressions. -/
inductive Arith where
  | add | sub | mul | div | mod
  deriving DecidableEq

/-- Interpret a dispatch arithmetic operation using natural addition, subtraction,
multiplication, division or remainder. -/
def Arith.eval : Arith → ℕ → ℕ → ℕ
  | .add => Nat.add
  | .sub => Nat.sub
  | .mul => Nat.mul
  | .div => Nat.div
  | .mod => Nat.mod

/-- Arithmetic expression over literals and the eight immutable dispatch inputs. -/
inductive Expr where
  | reg (i : Fin 8)
  | lit (v : ℕ)
  | op (a : Arith) (lhs rhs : Expr)

instance (n : ℕ) : OfNat Expr n := ⟨.lit n⟩
instance : Add Expr := ⟨.op .add⟩
instance : Sub Expr := ⟨.op .sub⟩
instance : Mul Expr := ⟨.op .mul⟩
instance : Div Expr := ⟨.op .div⟩
instance : Mod Expr := ⟨.op .mod⟩

/-- Evaluate a dispatch expression in the supplied bank of eight natural numbers. -/
def Expr.eval (inputs : Fin 8 → ℕ) : Expr → ℕ
  | .reg i => inputs i
  | .lit v => v
  | .op a l r => a.eval (l.eval inputs) (r.eval inputs)

/-- Decision tree that tests expression equality and emits six expressions at the selected
leaf. -/
inductive Code where
  | emit (fields : Fin 6 → Expr)
  | test (x y : Expr) (yes no : Code)

/-- Follow equality tests on the input words and evaluate the six fields of the reached leaf. -/
def Code.eval (inputs : Fin 8 → ℕ) : Code → Fin 6 → ℕ
  | .emit fields => fun i => (fields i).eval inputs
  | .test x y yes no => if x.eval inputs = y.eval inputs then yes.eval inputs else no.eval inputs

private abbrev tag : Expr := .reg 0
private abbrev a : Expr := .reg 1
private abbrev i : Expr := .reg 2
private abbrev j : Expr := .reg 3
private abbrev h : Expr := .reg 4
private abbrev z : Expr := .reg 5
private abbrev k : Expr := .reg 6
private abbrev rows : Expr := .reg 7

/-- Absolute row of an index in the trailing matrix. -/
private abbrev absolute (x : Expr) := x + 1 + a
private abbrev tailCount := rows - a - 1
private abbrev mid := k / (z+1)
private abbrev deg := k % (z+1)

private def oneChild : Code := .emit ![6,0,0,0,0,0]

private def productChild (right : Bool) : Code :=
  .test a 0
    (if right then oneChild else .emit ![1,i,0,0,h,z])
    (if right then .emit ![0,a-1,i+j/2,j-j/2,h-mid,z-deg]
      else .emit ![0,a-1,i,j/2,mid,deg])

private def factorChild (right : Bool) : Code :=
  if right then oneChild else .emit ![2,a,k/tailCount,k%tailCount,h-2,z]

private def outerChild (right : Bool) : Code :=
  if right then .emit ![5,absolute j,a,1,0,z-k] else .emit ![3,a,i,j,h,k]

private def innerChild (right : Bool) : Code :=
  if right then .emit ![4,a,i,j,h,z-k] else .emit ![5,a,absolute i,0,0,k]

private def powerChild (right : Bool) : Code :=
  if right then .emit ![4,a,mid,j,h-h/2,z-deg] else .emit ![4,a,i,mid,h/2,deg]

/-- Dispatch on the Schur key tag to construct the selected left or right child query. -/
def child (right : Bool) : Code :=
  .test tag 0 (productChild right) <| .test tag 1 (factorChild right) <|
    .test tag 2 (outerChild right) <| .test tag 3 (innerChild right) (powerChild right)

private def zeroResult : Code := .emit ![0,0,0,0,0,0]
private def oneResult : Code := .emit ![1,0,0,0,0,0]
private def unitResult : Code := .test h 0 (.test z 0 oneResult zeroResult) zeroResult

private def read (neg : Bool) (row col degree : Expr) : Code :=
  .emit ![if neg then 3 else 2,row,col,degree,0,0]

private def branch (count : Expr) : Code := .emit ![4,count,0,0,0,0]

private def productDescription : Code :=
  .test a 0 (.test j 0 unitResult (branch 1)) (branch ((h+1)*(z+1)))

private def factorDescription : Code :=
  .test h 0 (.test z 0 oneResult zeroResult) <| .test h 1 (read true a a z) (branch (tailCount*tailCount))

private def powerDescription : Code :=
  .test h 0 (.test i j (.test z 0 oneResult zeroResult) zeroResult) <|
    .test h 1 (read false (absolute i) (absolute j) z) (branch (tailCount*(z+1)))

/-- Dispatch on the Schur key tag to describe its product scan or its scalar result. -/
def describe : Code :=
  .test tag 0 productDescription <| .test tag 1 factorDescription <|
    .test tag 2 (branch (z+1)) <| .test tag 3 (branch (z+1)) <|
      .test tag 4 powerDescription <| .test tag 5 (.test j 0 (read false a i z) (read true a i z)) oneResult

variable {n U Z : ℕ}

/-- Assemble the six encoded query words, child index and matrix dimension into the dispatch
input bank. -/
def inputs (q : SchurKey n U Z) (k : ℕ) : Fin 8 → ℕ :=
  ![q.words 0,q.words 1,q.words 2,q.words 3,q.words 4,q.words 5,k,n]

/-- Interpret an emitted descriptor using only a query for a scalar entry. -/
def decode {R : Type*} [CommRing R] (entry : Entry n R) (v : Fin 6 → ℕ) : Sum R ℕ :=
  if v 0 = 4 then .inr (v 1) else if v 0 = 1 then .inl 1 else if v 0 = 0 then .inl 0 else
    if hi : v 1 < n then if hj : v 2 < n then
      let x := entry ⟨v 1,hi⟩ ⟨v 2,hj⟩ (v 3)
      if v 0 = 2 then .inl x else if v 0 = 3 then .inl (-x) else .inl 0
    else .inl 0 else .inl 0

theorem eval_add (s : Fin 8 → ℕ) (x y : Expr) : (x+y).eval s = x.eval s + y.eval s := rfl
theorem eval_sub (s : Fin 8 → ℕ) (x y : Expr) : (x-y).eval s = x.eval s - y.eval s := rfl
theorem eval_mul (s : Fin 8 → ℕ) (x y : Expr) : (x*y).eval s = x.eval s * y.eval s := rfl
theorem eval_div (s : Fin 8 → ℕ) (x y : Expr) : (x/y).eval s = x.eval s / y.eval s := rfl
theorem eval_mod (s : Fin 8 → ℕ) (x y : Expr) : (x%y).eval s = x.eval s % y.eval s := rfl
theorem eval_lit (s : Fin 8 → ℕ) (n : ℕ) : (OfNat.ofNat n : Expr).eval s = n := rfl

private theorem subscript {q : Fin n} (i : TailIndex q) : i.val + 1 + q.val < n := by
  have := q.isLt
  have := i.isLt
  omega

/-- Evaluate the rank-query dispatcher and its selected child description
using the branch and cursor equations in the local context. -/
macro (name := simplifyDispatch) "simplify_dispatch" : tactic => `(tactic|
  simp [Code.eval, inputs, SchurKey.words, eval_add, eval_sub, eval_mul, eval_div, eval_mod,
    eval_lit, Expr.eval, Arith.eval, tag, a, i, j, h, z, k, rows, absolute, mid, deg, tailCount,
    describe, productDescription, factorDescription, powerDescription, unitResult,
    branch, read, oneResult, zeroResult, decode, SchurKey.node, Node.box, Node.describe,
    SchurKey.unitCoeff, PowerKey.node, Node.map, tailEntry, tailIndex, suffixIndex, subscript,
    child, productChild, factorChild, outerChild, innerChild, powerChild, oneChild,
    SchurKey.program, Node.program, Node.children, PowerKey.split, predBy,
    lowDegree, highDegree, Block.lower, Block.upper, Fin.ext_iff, Nat.pos_iff_ne_zero, *])

theorem describe_eq {R : Type*} [CommRing R] (entry : Entry n R) (q : SchurKey n U Z) (cursor : ℕ) :
    decode entry (describe.eval (inputs q cursor)) = (q.node entry).describe := by
  cases q with
  | product d b u z =>
    by_cases hd : d.val = 0 <;> by_cases hb : b.count = 0 <;>
      by_cases hu : u.val = 0 <;> by_cases hz : z.val = 0 <;>
      simplify_dispatch
  | factor a u z =>
    by_cases hu : u.val = 0 <;> by_cases hu' : u.val = 1 <;> by_cases hz : z.val = 0 <;> simplify_dispatch
  | outer | inner | one => simplify_dispatch
  | scalar neg i j z => cases neg <;> simplify_dispatch
  | power a q =>
    by_cases h0 : q.exponent.val = 0 <;> by_cases h1 : q.exponent.val = 1 <;>
      by_cases hij : q.row.val = q.col.val <;> by_cases hz : q.degree.val = 0 <;> simplify_dispatch

/-- At a valid product-loop index the fixed code supplies precisely the
query saved by the typed stack interpreter. -/
theorem child_eq {R : Type*} [CommRing R] (entry : Entry n R) (q : SchurKey n U Z)
    {t : ℕ} {f : Fin t → SchurKey n U Z × SchurKey n U Z}
    (hn : q.node entry = .branch t f) (idx : Fin t) (right : Bool) :
    (child right).eval (inputs q idx.val) = (if right then (f idx).2 else (f idx).1).words := by
  cases q with
  | product d b u z =>
    simp only [SchurKey.node] at hn
    split_ifs at hn with hd hc
    all_goals cases hn; cases right <;> funext field <;> fin_cases field <;> simplify_dispatch <;> rfl
  | factor a u z =>
    simp only [SchurKey.node] at hn
    split_ifs at hn
    cases hn
    cases right <;> funext field <;> fin_cases field <;> simplify_dispatch
  | outer | inner =>
    cases hn
    cases right <;> funext field <;> fin_cases field <;> simplify_dispatch
  | power a q =>
    simp only [SchurKey.node, PowerKey.node] at hn
    split_ifs at hn <;> simp only [Node.map, Node.box] at hn
    all_goals cases hn
    cases right <;> funext field <;> fin_cases field <;> simplify_dispatch
    all_goals rfl
  | scalar | one => contradiction

end RankQuery.Stack.Dispatch

end VPVNP
end Computability
end OAI
