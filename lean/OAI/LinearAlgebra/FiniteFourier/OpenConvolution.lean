import OAI.LinearAlgebra.FiniteFourier.Circuit

/-! # Linear reductions with open convolution gates

An integer open reduction uses the same linear map on each operand. Its
nonlinear gates are ordinary convolutions on disjoint pairs of blocks.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators

/-- The coefficient vector of ordinary (untruncated) convolution. -/
def openConv (R : Type*) [CommRing R] (n : ℕ) (x y : Fin n → R) (k : Fin (2*n-1)) : R :=
  ∑ i : Fin n, ∑ j : Fin n, if i.val + j.val = k.val then x i * y j else 0

/-- Ordinary convolution commutes with the coefficient map. -/
theorem openConv_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (n : ℕ) (x y : Fin n → R) (k : Fin (2*n-1)) :
    φ (openConv R n x y k) = openConv S n (φ ∘ x) (φ ∘ y) k := by
  simp [openConv, apply_ite φ]

/-- The two linear circuits around a collection of unfilled convolution gates. -/
structure OpenConvolution (R : Type*) (n : ℕ) (B : Type*) (len : B → ℕ) where
  inputSize : ℕ
  outputSize : ℕ
  input : Circuit R (Fin n) (Σ b, Fin (len b)) inputSize
  output : Circuit R (Σ b, Fin (2*len b-1)) (Fin (2*n-1)) outputSize

namespace OpenConvolution

variable {R : Type*} [CommRing R] {n : ℕ} {B : Type*} {len : B → ℕ}

/-- The vector of ordinary convolution outputs at the unfinished gates. -/
def children (p : OpenConvolution R n B len) (x y : Fin n → R) (bk : Σ b, Fin (2*len b-1)) : R :=
  openConv R (len bk.1) (fun i => p.input.eval x ⟨bk.1, i⟩)
    (fun i => p.input.eval y ⟨bk.1, i⟩) bk.2

/-- Evaluate both input circuits, the open convolution gates, and the output circuit. -/
def eval (p : OpenConvolution R n B len) (x y : Fin n → R) (k : Fin (2*n-1)) : R :=
  p.output.eval (p.children x y) k

/-- Both input maps are counted since they run on different operands. -/
def linearCost (p : OpenConvolution R n B len) : ℕ := 2*p.inputSize + p.outputSize

/-- The reduction gives the stated scalar multiple of every coefficient. -/
def RealizesMultiple (p : OpenConvolution R n B len) (D : R) : Prop :=
  ∀ x y k, p.eval x y k = D * openConv R n x y k

end OpenConvolution

end FiniteFourier
end LinearAlgebra
end OAI
