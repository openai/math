import Init.Data.Vector.OfFn
import OAI.Optimization.LinearProgramming.Geometry.Projection
import OAI.Optimization.LinearProgramming.Geometry.MatrixBits
import OAI.Optimization.LinearProgramming.Elimination.Basic
import OAI.Optimization.LinearProgramming.Compression.RationalMinorSize
import OAI.Optimization.LinearProgramming.Compression.PowerBits
import OAI.Optimization.LinearProgramming.Compression.DetCircuitBits

/-! # Rational computation of the rounded row-space projector

The Gram matrix, inverse, intermediate rectangular matrix and answer are
materialized once. The determinant routine tabulates its polynomial-size
Bird recurrence. A singular Gram matrix returns zero without dividing by zero. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix
open scoped Matrix BigOperators

variable {r n : ℕ}

/-- Materialize a rectangular table, including widths and heights equal to zero. -/
def tabulateRect {K : Type*} (A : Matrix (Fin r) (Fin n) K) : Matrix (Fin r) (Fin n) K :=
  let table := Vector.ofFn fun i => Vector.ofFn fun j => A i j
  fun i j => (table.get i).get j

@[simp] theorem tabulateRect_eq {K : Type*} (A : Matrix (Fin r) (Fin n) K) : tabulateRect A = A := by
  ext i j
  change ((Vector.ofFn (fun a : Fin r => Vector.ofFn (fun b : Fin n => A a b))).get i).get j = A i j
  have row : (Vector.ofFn (fun a : Fin r => Vector.ofFn (fun b : Fin n => A a b))).get i =
      Vector.ofFn (fun b : Fin n => A i b) :=
    Vector.getElem_ofFn (f := fun a : Fin r => Vector.ofFn (fun b : Fin n => A a b)) i.isLt
  rw [row]
  exact Vector.getElem_ofFn (f := fun b : Fin n => A i b) j.isLt

theorem tabulateRect_apply {K : Type*} (A : Matrix (Fin r) (Fin n) K) (i : Fin r) (j : Fin n) :
    tabulateRect A i j = A i j := congrFun (congrFun (tabulateRect_eq A) i) j

/-- Inverse from r² row substitution determinants and a single shared reciprocal.
The explicit branch is the legality test for field division. -/
def gramInverse {K : Type*} [Field K] [DecidableEq K] (G : Matrix (Fin r) (Fin r) K) :
    Matrix (Fin r) (Fin r) K :=
  let d := Elimination.determinant G
  if d = 0 then 0 else
    let inv := d⁻¹
    tabulateRect (fun i j => inv * Elimination.determinant (G.updateRow j (Pi.single i 1)))

@[simp] theorem gramInverse_eq {K : Type*} [Field K] [DecidableEq K] (G : Matrix (Fin r) (Fin r) K) :
    gramInverse G = G⁻¹ := by
  classical
  by_cases h : G.det = 0
  · simp [gramInverse, h, Matrix.nonsing_inv_apply_not_isUnit G (by simp [h])]
  · ext i j
    simp [gramInverse, h, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_apply]
    exact tabulateRect_apply _ i j

/-- Compute the rational projector Dᵀ (D Dᵀ)⁻¹ D. The final product reads from
the stored table of the first product. -/
def computeGramProjector {K : Type*} [Field K] [DecidableEq K]
    (D : Matrix (Fin r) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  let d := tabulateRect D
  let g := tabulateRect (d * dᵀ)
  let inv := gramInverse g
  let left := tabulateRect (dᵀ * inv)
  tabulateRect (left * d)

@[simp] theorem computeGramProjector_eq {K : Type*} [Field K] [DecidableEq K]
    (D : Matrix (Fin r) (Fin n) K) :
    computeGramProjector D = rowGramProjector D := by
  simp [computeGramProjector, rowGramProjector]

/-- Fixed polynomial encoding bound for the determinant of any r-by-r matrix
with inputs bounded by a bits, also for the substitution matrices. -/
def gramDetBits (r a : ℕ) : ℕ := 3 + r^2 + a*r + 2*a*r^3

private theorem gram_input_bits (D : Matrix (Fin r) (Fin n) ℚ) {B : ℕ}
    (h : ∀ i j, RAM.ratBits (D i j) ≤ B) :
    ∀ i j, RAM.ratBits ((D * Dᵀ) i j) ≤ dotBitBound n B B :=
  matrix_product_bits D Dᵀ h (fun i j => h j i)

/-- A substituted row uses zero and one. Every retained row uses its original entries. This covers all r² determinant inputs with one bound. -/
theorem gram_substitution_input_bits (G : Matrix (Fin r) (Fin r) ℚ) {a : ℕ}
    (ha : 3 ≤ a) (h : ∀ i j, RAM.ratBits (G i j) ≤ a) (i j k l : Fin r) :
    RAM.ratBits ((G.updateRow j (Pi.single i 1)) k l) ≤ a := by
  by_cases hkj : k = j
  · subst k
    by_cases hil : l = i
    · subst l; simpa using ha
    · simpa [Pi.single_eq_of_ne hil, show RAM.ratBits (0 : ℚ) = 3 from rfl] using ha
  · simpa [Matrix.updateRow_ne hkj] using h k l

/-- Both the normalizing determinant and every cofactor numerator fit the same
fixed polynomial, independent of the numerical sizes of the entries. -/
theorem gram_determinants_bits (G : Matrix (Fin r) (Fin r) ℚ) {a : ℕ}
    (ha : 3 ≤ a) (h : ∀ i j, RAM.ratBits (G i j) ≤ a) :
    RAM.ratBits (Elimination.determinant G) ≤ gramDetBits r a ∧
    ∀ i j, RAM.ratBits (Elimination.determinant (G.updateRow j (Pi.single i 1))) ≤ gramDetBits r a := by
  simp only [Elimination.determinant_eq]
  exact ⟨Compression.rational_det_bits G h, fun i j =>
    Compression.rational_det_bits _ (gram_substitution_input_bits G ha h i j)⟩

theorem gram_inverse_bits (G : Matrix (Fin r) (Fin r) ℚ) {a : ℕ}
    (ha : 3 ≤ a) (h : ∀ i j, RAM.ratBits (G i j) ≤ a) (i j : Fin r) :
    RAM.ratBits (gramInverse G i j) ≤ 2 * gramDetBits r a := by
  obtain ⟨hd, hco⟩ := gram_determinants_bits G ha h
  by_cases hz : Elimination.determinant G = 0
  · simp only [gramInverse, hz, ite_true, Matrix.zero_apply]
    change 3 ≤ _
    unfold gramDetBits; omega
  · have hs : gramInverse G i j = (Elimination.determinant G)⁻¹ *
          Elimination.determinant (G.updateRow j (Pi.single i 1)) := by
      simp [gramInverse, -Elimination.determinant_eq, hz]
      exact tabulateRect_apply _ i j
    rw [hs]
    apply (Compression.ratBits_mul_le_add _ _).trans
    rw [Compression.ratBits_inv_eq]
    have := hco i j
    omega

/-- Polynomial bit envelope for the final computed matrix, with the source
dimensions and the input-entry bound as the only parameters. -/
def gramProjectorBits (r n B : ℕ) : ℕ :=
  let g := dotBitBound n B B
  let inv := 2 * gramDetBits r g
  dotBitBound r (dotBitBound r B inv) B

theorem computeGramProjector_bits (D : Matrix (Fin r) (Fin n) ℚ) {B : ℕ}
    (h : ∀ i j, RAM.ratBits (D i j) ≤ B) (i j : Fin n) :
    RAM.ratBits (computeGramProjector D i j) ≤ gramProjectorBits r n B := by
  have hG := gram_input_bits D h
  have hG0 : 3 ≤ dotBitBound n B B := by unfold dotBitBound; omega
  have hI := gram_inverse_bits (D * Dᵀ) hG0 hG
  have hL := matrix_product_bits Dᵀ (gramInverse (D * Dᵀ)) (fun i j => h j i) hI
  simp only [computeGramProjector, tabulateRect_eq]
  exact matrix_product_bits _ D hL h i j

/-- Select the whole Gram matrix or one of the r² row substitutions used in the inverse. -/
def gramDetInput (G : Matrix (Fin r) (Fin r) ℚ) :
    Option (Fin r × Fin r) → Matrix (Fin r) (Fin r) ℚ
  | none => G
  | some (i,j) => G.updateRow j (Pi.single i 1)

private theorem gramDetInput_bits (G : Matrix (Fin r) (Fin r) ℚ) {a : ℕ}
    (ha : 3 ≤ a) (h : ∀ i j, RAM.ratBits (G i j) ≤ a)
    (d : Option (Fin r × Fin r)) (i j : Fin r) :
    RAM.ratBits (gramDetInput G d i j) ≤ a := by
  rcases d with _ | ⟨p,q⟩
  · exact h i j
  · exact gram_substitution_input_bits G ha h p q i j

/-- All kinds of scalar values encountered in the matrix routine. Singletons
in a dot-product summation give the intermediate scalar products as well. -/
inductive GramRegister (r n : ℕ)
  | zero | one | minusOne
  | input (i : Fin r) (j : Fin n)
  | gramDot (i j : Fin r) (t : Finset (Fin n))
  | detInput (d : Option (Fin r × Fin r)) (i j : Fin r)
  | detTemporary (d : Option (Fin r × Fin r)) (stage : Fin (r + 1)) (reg : Compression.BirdRegister r)
  | detValue (d : Option (Fin r × Fin r))
  | reciprocal
  | inverseEntry (i j : Fin r)
  | leftDot (i : Fin n) (j : Fin r) (t : Finset (Fin r))
  | outputDot (i j : Fin n) (t : Finset (Fin r))

def GramRegister.read (D : Matrix (Fin r) (Fin n) ℚ) (reg : GramRegister r n) : ℚ :=
  let G := D * Dᵀ
  let I := gramInverse G
  match reg with
  | .zero => 0
  | .one => 1
  | .minusOne => -1
  | .input i j => D i j
  | .gramDot i j t => ∑ k ∈ t, D i k * D j k
  | .detInput d i j => gramDetInput G d i j
  | .detTemporary d stage w => w.read (gramDetInput G d)
      (Compression.birdLayer (gramDetInput G d) stage.val)
  | .detValue d => Elimination.determinant (gramDetInput G d)
  | .reciprocal => (Elimination.determinant G)⁻¹
  | .inverseEntry i j => I i j
  | .leftDot i j t => ∑ k ∈ t, D k i * I k j
  | .outputDot i j t => ∑ k ∈ t, (Dᵀ * I) i k * D k j

/-- Sum of the stage envelopes. Every term is a fixed polynomial in the two
dimensions and the largest entry bit length. -/
def gramWorkspaceBits (r n B : ℕ) : ℕ :=
  let g := dotBitBound n B B
  let d := gramDetBits r g
  let i := 2*d
  let l := dotBitBound r B i
  let p := dotBitBound r l B
  let bird := 3 + (r + g + 2*g*r^2 + 3) * (r+2)
  3 + B + g + d + i + l + p + bird

/-- All inputs, products, partial sums, determinants, Bird stage registers,
reciprocals and computed entries have bounded reduced rational encodings. -/
theorem gramRegister_bits (D : Matrix (Fin r) (Fin n) ℚ) {B : ℕ}
    (h : ∀ i j, RAM.ratBits (D i j) ≤ B) (reg : GramRegister r n) :
    RAM.ratBits (reg.read D) ≤ gramWorkspaceBits r n B := by
  let G := D * Dᵀ
  let g := dotBitBound n B B
  let d := gramDetBits r g
  let inv := 2*d
  let l := dotBitBound r B inv
  let p := dotBitBound r l B
  let bird := 3 + (r + g + 2*g*r^2 + 3) * (r+2)
  change _ ≤ 3 + B + g + d + inv + l + p + bird
  have hg : ∀ i j, RAM.ratBits (G i j) ≤ g := gram_input_bits D h
  have hg0 : 3 ≤ g := by dsimp [g, dotBitBound]; omega
  have hi : ∀ i j, RAM.ratBits (gramInverse G i j) ≤ inv := gram_inverse_bits G hg0 hg
  have hl : ∀ i j, RAM.ratBits ((Dᵀ * gramInverse G) i j) ≤ l :=
    matrix_product_bits Dᵀ _ (fun i j => h j i) hi
  have hd (k : Option (Fin r × Fin r)) :
      RAM.ratBits (Elimination.determinant (gramDetInput G k)) ≤ d := by
    rw [Elimination.determinant_eq]
    exact Compression.rational_det_bits _ (gramDetInput_bits G hg0 hg k)
  cases reg with
  | zero => change 3 ≤ _; omega
  | one => change 3 ≤ _; omega
  | minusOne => change 3 ≤ _; omega
  | input i j => exact (h i j).trans (by omega)
  | gramDot i j t =>
    exact (dotProduct_partial_bits (D i) (D j) (h i) (h j) t).trans (by omega)
  | detInput k i j => exact (gramDetInput_bits G hg0 hg k i j).trans (by omega)
  | detTemporary k stage w =>
    apply (Compression.birdRegister_bits (gramDetInput G k)
      (gramDetInput_bits G hg0 hg k) stage.val w).trans
    have hst : stage.val + 2 ≤ r + 2 := by omega
    have hb : 3 + (r + g + 2*g*r^2 + 3) * (stage.val+2) ≤ bird :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hst) _
    omega
  | detValue k => exact (hd k).trans (by omega)
  | reciprocal =>
    change RAM.ratBits (Elimination.determinant G)⁻¹ ≤ _
    rw [Compression.ratBits_inv_eq]
    exact (hd none).trans (by omega)
  | inverseEntry i j => exact (hi i j).trans (by omega)
  | leftDot i j t =>
    exact (dotProduct_partial_bits (fun k => D k i) (fun k => gramInverse G k j)
      (fun k => h k i) (fun k => hi k j) t).trans (by omega)
  | outputDot i j t =>
    exact (dotProduct_partial_bits ((Dᵀ * gramInverse G) i) (D.col j)
      (hl i) (fun k => h k j) t).trans (by omega)

/-- The straight-line expression for any one cell of a matrix product. -/
def gramDotExpr (k : ℕ) : Compression.ArithExpr (Fin k ⊕ Fin k) :=
  Compression.sumExpr k fun i => .mul (.read (.inl i)) (.read (.inr i))

theorem gramDotExpr_eval {K : Type} [CommRing K] {k : ℕ} (x y : Fin k → K) :
    (gramDotExpr k).eval (Sum.elim x y) = x ⬝ᵥ y := by
  simp only [gramDotExpr, Compression.eval_sumExpr, Compression.ArithExpr.eval, Sum.elim_inl,
    Sum.elim_inr, dotProduct]

theorem gramDotExpr_size (k : ℕ) : (gramDotExpr k).size ≤ 1 + 4*k := by
  apply (Compression.size_sumExpr k 3 _ fun i => by simp [Compression.ArithExpr.size]).trans
  omega

/-- Upper envelope for scalar-expression nodes in the three products, each of
the r²+1 Bird calls, one division and the r² cofactor scalings. The singular
branch skips the cofactor calls and scalings. -/
def gramArithmeticNodes (r n : ℕ) : ℕ :=
  r^2 * (gramDotExpr n).size +
  (r^2 + 1) * ((r-1) * Compression.birdStageNodes r + 2) +
  1 + r^2 + n*r*(gramDotExpr r).size + n^2*(gramDotExpr r).size

theorem gramArithmeticNodes_le (r n : ℕ) :
    gramArithmeticNodes r n ≤ r^2 * (1+4*n) + (r^2+1) * (8*(r+1)^4) +
      1 + r^2 + n*r*(1+4*r) + n^2*(1+4*r) := by
  unfold gramArithmeticNodes
  gcongr
  all_goals first | exact gramDotExpr_size _ | exact Compression.birdDet_nodes_le _

/-- Every scalar read or produced by the dot-product expression is an input
or a partial dot product. This includes intermediate expression nodes. -/
theorem gramDotExpr_allValues {k : ℕ} (x y : Fin k → ℚ) (P : ℚ → Prop)
    (hx : ∀ i, P (x i)) (hy : ∀ i, P (y i))
    (hpartials : ∀ t : Finset (Fin k), P (∑ i ∈ t, x i * y i)) :
    (gramDotExpr k).AllValues (Sum.elim x y) P := by
  apply Compression.allValues_sumExpr
  · intro i
    refine ⟨?_, hx i, hy i⟩
    simpa [Compression.ArithExpr.eval] using hpartials {i}
  · simpa only [Compression.ArithExpr.eval, Sum.elim_inl, Sum.elim_inr] using hpartials

/-- Every scalar in an arithmetic expression for one Gram-matrix cell obeys
the workspace bound, as does every cell in either subsequent matrix product. -/
theorem gram_product_gates_bounded (D : Matrix (Fin r) (Fin n) ℚ) {B : ℕ}
    (h : ∀ i j, RAM.ratBits (D i j) ≤ B) :
    (∀ i j, (gramDotExpr n).AllValues (Sum.elim (D i) (D j))
      (fun q => RAM.ratBits q ≤ gramWorkspaceBits r n B)) ∧
    (∀ i j, (gramDotExpr r).AllValues
      (Sum.elim (fun k => D k i) ((gramInverse (D * Dᵀ)).col j))
      (fun q => RAM.ratBits q ≤ gramWorkspaceBits r n B)) ∧
    (∀ i j, (gramDotExpr r).AllValues
      (Sum.elim ((Dᵀ * gramInverse (D * Dᵀ)) i) (D.col j))
      (fun q => RAM.ratBits q ≤ gramWorkspaceBits r n B)) := by
  have H := gramRegister_bits D h
  refine ⟨fun i j => gramDotExpr_allValues _ _ _ (fun k => H (.input i k))
    (fun k => H (.input j k)) (fun t => H (.gramDot i j t)), ?_, ?_⟩
  · intro i j
    exact gramDotExpr_allValues _ _ _ (fun k => H (.input k i))
      (fun k => H (.inverseEntry k j)) (fun t => H (.leftDot i j t))
  · intro i j
    apply gramDotExpr_allValues _ _ _ _ (fun k => H (.input k j))
      (fun t => H (.outputDot i j t))
    intro k
    exact H (.leftDot i k Finset.univ)

/-- The circuit realizing a Bird stage of any of the r²+1 determinant requests
also obeys the same single polynomial envelope. -/
theorem gram_determinant_gates_bounded (D : Matrix (Fin r) (Fin n) ℚ) {B : ℕ}
    (h : ∀ i j, RAM.ratBits (D i j) ≤ B) (d : Option (Fin r × Fin r))
    (stage : Fin (r+1)) (i j : Fin r) :
    (Compression.birdStepExpr i j).AllValues
      (Compression.readBird (gramDetInput (D * Dᵀ) d)
        (Compression.birdLayer (gramDetInput (D * Dᵀ) d) stage.val))
      (fun q => RAM.ratBits q ≤ gramWorkspaceBits r n B) := by
  apply (Compression.birdStepExpr_registers _ _ i j).mono
  rintro _ ⟨w, rfl⟩
  exact gramRegister_bits D h (.detTemporary d stage w)

end Geometry
end LinearProgramming
end Optimization
end OAI
