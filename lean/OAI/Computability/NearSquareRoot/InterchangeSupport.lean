import OAI.Computability.NearSquareRoot.InterchangeDependentStars
import OAI.Computability.NearSquareRoot.InterchangeStageTransport
import OAI.Computability.NearSquareRoot.InterchangeStageLift
import OAI.Computability.NearSquareRoot.InterchangeTriangular
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Rational address changes with a physical support

A dense change costs at most eighteen recursive pivots per active coordinate.
A unit lower triangular change on physically ordered slots costs zero pivots.
A finite family of these changes can share one radix at every word length.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Support

open IntegerMultiplication.Port Matrix

variable {J : Type} [DecidableEq J]

structure Piece (J : Type) (rank : J → ℕ) where
  dim : ℕ
  slot : Fin dim ↪ Spot J
  change : (Fin dim → ℚ) ≃ₗ[ℚ] (Fin dim → ℚ)
  free : Bool
  ordered : free = true → ∀ i j, i < j → Lag.early rank (slot i) (slot j)
  lower : free = true → (addressMatrix change).IsLowerTriangular
  diagonal : free = true → ∀ i, addressMatrix change i i = 1

namespace Piece

variable {rank : J → ℕ}

def dense {d : ℕ} (s : Fin d ↪ Spot J) (F : (Fin d → ℚ) ≃ₗ[ℚ] (Fin d → ℚ)) :
    Piece J rank := ⟨d,s,F,false,by simp,by simp,by simp⟩

def price (u : Piece J rank) : ℕ := if u.free then 0 else 18*u.dim

noncomputable def address (u : Piece J rank) : Duplex J ℚ ≃ₗ[ℚ] Duplex J ℚ :=
  NearSquareRoot.InterchangeStageLift.linearEquiv u.slot u.change

end Piece

/-- Address-map composition is in physical execution order. -/
inductive Word (J : Type) (rank : J → ℕ) where
  | idle
  | atom (a : Piece J rank)
  | seq (before after : Word J rank)
  | symm (forward : Word J rank)

namespace Word

variable {rank : J → ℕ}

def price : Word J rank → ℕ
  | .idle => 0
  | .atom a => a.price
  | .seq v w => price v + price w
  | .symm w => price w

noncomputable def address : Word J rank → Duplex J ℚ ≃ₗ[ℚ] Duplex J ℚ
  | .idle => .refl _ _
  | .atom a => a.address
  | .seq v w => (address v).trans (address w)
  | .symm w => (address w).symm

end Word

private theorem mulVec_unitLower {S : Type} [CommRing S] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) S) (hl : A.IsLowerTriangular) (hd : ∀ i, A i i = 1)
    (x : Fin d → S) (i : Fin d) :
    (A *ᵥ x) i = x i + ∑ j ∈ Finset.Iio i, A i j * x j := by
  classical
  change ∑ j, A i j * x j = _
  rw [← Finset.sum_subset (Finset.subset_univ (insert i (Finset.Iio i))) (fun j _ hj => ?_),
    Finset.sum_insert (by simp), hd, one_mul]
  have hij : i < j := by simpa [not_or, lt_iff_le_and_ne] using hj
  rw [hl hij, zero_mul]

/-- Compile a physically ordered unit lower triangular change at a previously
chosen radix. -/
theorem compile_unitLower {b d : ℕ} (rank : J → ℕ) (slot : Fin d ↪ Spot J)
    (order : ∀ i j, i < j → Lag.early rank (slot i) (slot j))
    (code : ℚ → Pinpoint b) (A : Matrix (Fin d) (Fin d) ℚ)
    (hl : A.IsLowerTriangular) (hd : ∀ i, A i i = 1)
    (M : (f : ℕ) → Matrix (Fin d) (Fin d) (Tower b f))
    (hM : ∀ f, MatrixToken A (M f)) (hc : ∀ i j f, Token (A i j) ((code (A i j)).stamp f)) :
    CompilesOn slot rank 0 M := by
  obtain ⟨ops, legal, effect⟩ := InterchangeTriangular.compile slot (fun _ => Span.one)
    (fun i j => code (A i j)) rank slot.injective order
  have hprice : (ops.map Lag.prices).sum = 0 := List.sum_eq_zero fun y hy => by
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
    exact (legal _ hz).2
  refine ⟨ops,fun v hv => (legal _ hv).1,hprice.le,fun f x => ?_⟩
  have low : (M f).IsLowerTriangular := fun {i j} hij =>
    ((hl hij) ▸ hM f i j).unique Token.zero
  have diag (i : Fin d) : M f i i = 1 := ((hd i) ▸ hM f i i).unique Token.unit
  refine ⟨fun i => ?_, (effect f x).2⟩
  rw [(effect f x).1 i, mulVec_unitLower _ low diag]
  simp only [InterchangeTriangular.rowValue, Span.land_one, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => congrArg (· * hear x (slot j))
    ((hc i j f).unique (hM f i j))

end Interchange.Support

end NearSquareRoot
end Computability
end OAI
