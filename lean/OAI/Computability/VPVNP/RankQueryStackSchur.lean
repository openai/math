import OAI.Computability.VPVNP.RankQueryStackPower

/-!
# Stack execution of the Schur determinant product

The query tags implement the balanced product of Schur factors, the two degree
convolutions inside one factor, and the power of its trailing principal
submatrix. The only matrix reads are individual scalar coefficients.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack

variable {n U Z : ℕ} {R : Type*} [CommRing R]

namespace Node

/-- Relabel both child queries of every product term while preserving scalar leaves. -/
def map {A B : Type*} (f : A → B) : Node A R → Node B R
  | .leaf r => .leaf r
  | .branch t g => .branch t (fun i => ((f (g i).1), f (g i).2))

theorem value_map {A B : Type*} (f : A → B) (node : Node A R) (v : B → R) :
    (node.map f).value v = node.value (v ∘ f) := by cases node <;> rfl

end Node

/-- A contiguous interval of Schur factors, stored by its start and its length. -/
structure Block (n : ℕ) where
  /-- First factor index in the contiguous block used by the balanced Schur product. -/
  start : ℕ
  /-- Number of consecutive Schur factors in the block. -/
  count : ℕ
  fits : start + count ≤ n

namespace Block

/-- Initial half of a block, containing the first `count / 2` factors. -/
def lower (b : Block n) : Block n :=
  ⟨b.start, b.count / 2, by have := b.fits; omega⟩

/-- Remaining half of a block, starting immediately after its initial half. -/
def upper (b : Block n) : Block n :=
  ⟨b.start + b.count / 2, b.count - b.count / 2, by have := b.fits; omega⟩

end Block

/-- Natural numbers from zero through the inclusive bound `b`. -/
abbrev Limit (b : ℕ) := Fin (b + 1)
/-- Local indices of the principal submatrix strictly after pivot `a`. -/
abbrev TailIndex (a : Fin n) := Fin (n - a.val - 1)

/-- Embed the first part of a coefficient-degree split into the original degree range. -/
def lowDegree {b : ℕ} (q : Limit b) (d : Fin (q.val + 1)) : Limit b :=
  ⟨d.val, by have := d.isLt; have := q.isLt; omega⟩

/-- Complementary degree `q - d` of a coefficient convolution. -/
def highDegree {b : ℕ} (q : Limit b) (d : Fin (q.val + 1)) : Limit b :=
  ⟨q.val - d.val, by have := q.isLt; omega⟩

/-- Subtract `k` from a bounded natural degree, saturating at zero. -/
def predBy {b : ℕ} (q : Limit b) (k : ℕ) : Limit b :=
  ⟨q.val - k, by have := q.isLt; omega⟩

/-- Translate a local tail index to its index in the original matrix after pivot `a`. -/
def tailIndex (a : Fin n) (i : TailIndex a) : Fin n := suffixIndex a i.succ

/-- Scalar coefficient reader indexed by matrix row, matrix column, and polynomial degree. -/
abbrev Entry (n : ℕ) (R : Type*) := Fin n → Fin n → ℕ → R

/-- Restrict the coefficient reader to the trailing principal submatrix after pivot `a`. -/
def tailEntry (entry : Entry n R) (a : Fin n) : Entry (n-a.val-1) R :=
  fun i j => entry (tailIndex a i) (tailIndex a j)

/-- The query tags and their numeric fields. `inner` handles the convolution of
the leading row with a matrix power, and `outer` multiplies by the trailing
column with the negative sign of the Schur factor. -/
inductive SchurKey (n U Z : ℕ) where
  | product (d : Limit (Nat.clog 2 n)) (b : Block n) (u : Limit U) (z : Limit Z)
  | factor (a : Fin n) (u : Limit U) (z : Limit Z)
  | outer (a : Fin n) (h : Limit U) (i j : TailIndex a) (z : Limit Z)
  | inner (a : Fin n) (h : Limit U) (i j : TailIndex a) (z : Limit Z)
  | power (a : Fin n) (q : PowerKey (n-a.val-1) U Z)
  | scalar (negative : Bool) (i j : Fin n) (z : Limit Z)
  | one

namespace SchurKey

/-- Schur query keys with fixed matrix order and two bounded coefficient degrees. -/
abbrev K (n U Z : ℕ) := SchurKey n U Z

/-- Bivariate coefficient of the constant polynomial one, supported at bidegree `(0,0)`. -/
def unitCoeff (u z : ℕ) : R := if u = 0 ∧ z = 0 then 1 else 0

/-- Coefficient at `(u,z)` of the Schur factor for pivot `a`, using the unit factor after the
last pivot. -/
def factorCoeff (entry : Entry n R) (a u z : ℕ) : R :=
  if ha : a < n then
    let i : Fin n := ⟨a, ha⟩
    streamedHeadFactorQuery (fun b c => entry (suffixIndex i b) (suffixIndex i c)) u z
  else unitCoeff u z

/-- Degree-`z` convolution of a pivot-row entry and an entry of the `h`th power of the trailing
submatrix. -/
def innerCoeff (entry : Entry n R) (a : Fin n) (h : ℕ) (i j : TailIndex a) (z : ℕ) : R :=
  streamAntiSum z fun e₁ e₂ => entry a (tailIndex a i) e₁ *
    powerEntryCoeff (tailEntry entry a) h i j e₂

/-- Degree-`z` convolution of the inner Schur product and the negated entry returning from the
tail to the pivot column. -/
def outerCoeff (entry : Entry n R) (a : Fin n) (h : ℕ) (i j : TailIndex a) (z : ℕ) : R :=
  streamAntiSum z fun d₁ d₂ => innerCoeff entry a h i j d₁ * (-entry (tailIndex a j) a d₂)

/-- Scalar specified by a Schur query, from a product of factors down to an individual matrix
coefficient. -/
def value (entry : Entry n R) : K n U Z → R
  | .product d b u z => balancedBivariateProduct (factorCoeff entry) d b.start b.count u z
  | .factor a u z => factorCoeff entry a u z
  | .outer a h i j z => outerCoeff entry a h i j z
  | .inner a h i j z => innerCoeff entry a h i j z
  | .power a q => q.value (tailEntry entry a)
  | .scalar negative i j z => if negative then -entry i j z else entry i j z
  | .one => 1

/-- Expand a Schur query into a scalar leaf or the indexed products that make up its next
coefficient convolution. -/
def node (entry : Entry n R) : K n U Z → Node (K n U Z) R
  | .product d b u z =>
    if d.val = 0 then
      if hc : 0 < b.count then
        let a : Fin n := ⟨b.start, by have := b.fits; omega⟩
        .branch 1 fun _ => (.factor a u z, .one)
      else .leaf (unitCoeff u z)
    else Node.box (u.val+1) (z.val+1) fun s t =>
      (.product (predBy d 1) b.lower (lowDegree u s) (lowDegree z t),
       .product (predBy d 1) b.upper (highDegree u s) (highDegree z t))
  | .factor a u z =>
    if u.val = 0 then .leaf (unitCoeff 0 z)
    else if u.val = 1 then .leaf (-entry a a z)
    else Node.box (n-a.val-1) (n-a.val-1) fun i j => (.outer a (predBy u 2) i j z, .one)
  | .outer a h i j z =>
    .branch (z.val+1) fun d => (.inner a h i j (lowDegree z d), .scalar true (tailIndex a j) a (highDegree z d))
  | .inner a h i j z =>
    .branch (z.val+1) fun e =>
      (.scalar false a (tailIndex a i) (lowDegree z e), .power a ⟨h,i,j,highDegree z e⟩)
  | .power a q => (q.node (tailEntry entry a)).map (.power a)
  | .scalar negative i j z => .leaf (if negative then -entry i j z else entry i j z)
  | .one => .leaf 1

private theorem factor_succ (entry : Entry n R) (a : Fin n) (h z : ℕ) :
    factorCoeff entry a (h+2) z = ∑ i, ∑ j, outerCoeff entry a h i j z := by
  have hz : suffixIndex a 0 = a := by apply Fin.ext; simp [suffixIndex]
  simp only [factorCoeff, a.isLt, dite_eq_left, streamedHeadFactorQuery, streamSum_eq,
    streamAntiSum, outerCoeff, innerCoeff, streamedPowerEntryCoeff_eq, tailIndex,
    hz, mul_neg, Finset.sum_neg_distrib]
  rfl

theorem value_node (entry : Entry n R) (q : K n U Z) :
    q.value entry = (q.node entry).value (value entry) := by
  cases q with
  | product d b u z =>
    rcases d with ⟨d, hd⟩
    cases d with
    | zero =>
      by_cases hc : 0 < b.count
      · have hn : b.count ≠ 0 := by omega
        simp [value, node, balancedBivariateProduct, balancedProduct, hc, hn, Node.value]
      · have hn : b.count = 0 := by omega
        simp [value, node, balancedBivariateProduct, balancedProduct, hn, Node.value, unitCoeff]
    | succ d =>
      simp only [value, node, Nat.succ_ne_zero, ite_false, Node.value_box,
        balancedBivariateProduct, balancedProduct, streamAntiSum, streamSum_eq]
      rfl
  | factor a u z =>
    have hzero : suffixIndex a 0 = a := by apply Fin.ext; simp [suffixIndex]
    rcases u with ⟨u, hu⟩
    rcases u with _ | _ | h
    · simp [value, node, factorCoeff, Node.value, streamedHeadFactorQuery, unitCoeff]
    · simp [value, node, factorCoeff, Node.value, streamedHeadFactorQuery, hzero]
    · simpa [value, node, Node.value_box, predBy] using factor_succ entry a h z
  | outer a h i j z => simp only [value, node, Node.value, outerCoeff, streamAntiSum, streamSum_eq]; rfl
  | inner a h i j z => simp only [value, node, Node.value, innerCoeff, streamAntiSum, streamSum_eq]; rfl
  | power a q =>
    rw [node, Node.value_map]
    exact q.value_node _
  | scalar | one => rfl

/-- Stack program evaluating Schur queries by expanding their product nodes and reading scalar
leaves. -/
def program (entry : Entry n R) : Program (K n U Z) R := Node.program (node entry)

theorem realizes (entry : Entry n R) : (program (U := U) (Z := Z) entry).Realizes (value entry) :=
  Node.realizes (value_node entry)

/-- Initial query for coefficient `(u,z)` of the determinant pencil, taking the Schur product
over all `n` factors. -/
def root (u : Limit U) (z : Limit Z) : K n U Z :=
  .product (Fin.last _) ⟨0, n, by omega⟩ u z

theorem value_root (entry : Entry n R) (u : Limit U) (z : Limit Z) :
    (root (n := n) u z).value entry = determinantQuery entry u z := rfl

end SchurKey

end RankQuery.Stack

end VPVNP
end Computability
end OAI
