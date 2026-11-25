import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights

/-! # Completion counts and conditional entropies on the uniform support -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse

abbrev Cell (i j k : ℕ) := Fin i × Fin j × Fin k
variable {F : Type*} [Field F] {i j k : ℕ}

open Classical in
def support (w : Fin i → Fin j → Fin k → F) : Finset (Cell i j k) :=
  Finset.univ.filter fun t => w t.1 t.2.1 t.2.2 ≠ 0

def rows (S : Finset (Cell i j k)) (t : Cell i j k) :=
  Finset.univ.filter fun x : Fin i => (x, t.2.1, t.2.2) ∈ S

def cols (S : Finset (Cell i j k)) (t : Cell i j k) :=
  Finset.univ.filter fun y : Fin j => (t.1, y, t.2.2) ∈ S

def inner (S : Finset (Cell i j k)) (t : Cell i j k) :=
  Finset.univ.filter fun z : Fin k => (t.1, t.2.1, z) ∈ S

/-- The conditional law of each missing label given the other two
is uniform on its completion set. Entropy here uses natural logs. -/
def conditional (S : Finset (Cell i j k)) : ℝ :=
  (∑ t ∈ S, (Real.log (rows S t).card + Real.log (cols S t).card +
    Real.log (inner S t).card)) / S.card

/-- Dual total correlation in bits. -/
def premium (S : Finset (Cell i j k)) : ℝ :=
  (Real.log S.card - conditional S) / Real.log 2

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
