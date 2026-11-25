import OAI.Hierarchy.Models

namespace OAI
/-! # Separating an arithmetic formula at one subtree

Replace a selected subtree by zero or one. The original polynomial is the
affine interpolation of the resulting two formulas at the subtree polynomial.
A descent by gate count bounds all three recursive problems.
-/

namespace Hierarchy.Formula

open MatrixMultiplication.Arithmetic

variable {F : Type*} {σ : Type} [Field F]

private inductive Binary where
  | add | sub | mul

private def Binary.node (op : Binary) (a b : Formula F σ) : Formula F σ :=
  match op with
  | .add => .add a b
  | .sub => .sub a b
  | .mul => .mul a b

private noncomputable def Binary.value (op : Binary) (x y : MvPolynomial σ F) : MvPolynomial σ F :=
  match op with
  | .add => x + y
  | .sub => x - y
  | .mul => x * y

omit [Field F] in
private theorem Binary.node_cost (op : Binary) (a b : Formula F σ) :
    (op.node a b).cost = a.cost + b.cost + 1 := by
  cases op <;> rfl

private theorem Binary.node_polynomial (op : Binary) (a b : Formula F σ) :
    (op.node a b).polynomial = op.value a.polynomial b.polynomial := by
  cases op <;> rfl

/-- The two substitutions remove exactly the gates of the chosen subtree. -/
private def Separated (t : ℕ) (f : Formula F σ) : Prop :=
  ∃ h z o : Formula F σ,
    t ≤ h.cost ∧ h.cost < 2*t ∧ z.cost + h.cost = f.cost ∧ o.cost = z.cost ∧
    f.polynomial = z.polynomial + h.polynomial * (o.polynomial - z.polynomial)

private theorem take_whole (t : ℕ) (f : Formula F σ) (lo : t ≤ f.cost) (hi : f.cost < 2*t) :
    Separated t f := by
  refine ⟨f,.constant 0,.constant 1,lo,hi,Nat.zero_add _,rfl,?_⟩
  simp [Formula.polynomial, LinearAlgebra.SpectralBooks.expressionPolynomial]

private theorem pass_left (op : Binary) (a b : Formula F σ) (t : ℕ)
    (cut : Separated t a) : Separated t (op.node a b) := by
  obtain ⟨h,z,o,lo,hi,size,eqSize,e⟩ := cut
  refine ⟨h,op.node z b,op.node o b,lo,hi,?_,?_,?_⟩
  · simp only [Binary.node_cost]
    omega
  · simp only [Binary.node_cost,eqSize]
  · simp only [Binary.node_polynomial,e]
    cases op <;> simp only [Binary.value] <;> ring

private theorem pass_right (op : Binary) (a b : Formula F σ) (t : ℕ)
    (cut : Separated t b) : Separated t (op.node a b) := by
  obtain ⟨h,z,o,lo,hi,size,eqSize,e⟩ := cut
  refine ⟨h,op.node a z,op.node a o,lo,hi,?_,?_,?_⟩
  · simp only [Binary.node_cost]
    omega
  · simp only [Binary.node_cost,eqSize]
  · simp only [Binary.node_polynomial,e]
    cases op <;> simp only [Binary.value] <;> ring

private theorem branch (op : Binary) (a b : Formula F σ) (t : ℕ)
    (left : t ≤ a.cost → Separated t a) (right : t ≤ b.cost → Separated t b)
    (lo : t ≤ (op.node a b).cost) : Separated t (op.node a b) := by
  by_cases hi : (op.node a b).cost < 2*t
  · exact take_whole t _ lo hi
  by_cases ha : t ≤ a.cost
  · exact pass_left op a b t (left ha)
  · apply pass_right op a b t
    apply right
    rw [Binary.node_cost] at hi
    omega

private theorem separate_at (t : ℕ) (positive : 0 < t) (f : Formula F σ) :
    t ≤ f.cost → Separated t f := by
  induction f with
  | constant c =>
    intro h
    change t ≤ 0 at h
    omega
  | input i =>
    intro h
    change t ≤ 0 at h
    omega
  | add a b ha hb => exact branch .add a b t ha hb
  | sub a b ha hb => exact branch .sub a b t ha hb
  | mul a b ha hb => exact branch .mul a b t ha hb

/-- For a formula with at least two gates, a subtree and both constant
substitutions have at most two thirds of the original gate count, rounded up
only when the original count is one modulo three. -/
theorem exists_separator (f : Formula F σ) (hn : 2 ≤ f.cost) :
    ∃ h z o : Formula F σ,
      f.polynomial = z.polynomial + h.polynomial * (o.polynomial - z.polynomial) ∧
      3*h.cost ≤ 2*f.cost+1 ∧ 3*z.cost ≤ 2*f.cost+1 ∧ 3*o.cost ≤ 2*f.cost+1 := by
  obtain ⟨h,z,o,lo,hi,size,eqSize,e⟩ :=
    separate_at ((f.cost+1)/3) (by omega) f (by omega)
  exact ⟨h,z,o,e,by omega,by omega,by omega⟩

end Hierarchy.Formula

end OAI
