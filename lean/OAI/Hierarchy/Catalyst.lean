import OAI.Hierarchy.FlatPrices
import OAI.ThreeFlat.BitNetwork

namespace OAI
/-! # Finite table networks with directed Euclidean catalysts

Each physical catalyst bit has a negative and a positive port in its direction.
An approximation has one fixed addressed table network over the given field.
The error price is tested on all compatible spectral price systems. -/

namespace Hierarchy.Catalyst

open LinearAlgebra.SpectralBooks ThreeFlat
open scoped BigOperators Classical

abbrev Wire {k : ℕ} (b : Fin k → ℕ) := Σ j, Fin (b j)
abbrev Port {k : ℕ} (p : ℕ) (b : Fin k → ℕ) := Fin p ⊕ (Wire b × Bool)

/-- Each bit of the external data is at the origin. -/
noncomputable def sites {k p : ℕ} (b : Fin k → ℕ) :
    Port p b → EuclideanSpace ℝ (Fin k)
  | .inl _ => 0
  | .inr (⟨j,_⟩,s) => EuclideanSpace.single j (if s then 1 else -1)

/-- The labelled tensor product of all through-identities with the data table. -/
noncomputable def ideal {F : Type*} [Field F] {k p : ℕ} (b : Fin k → ℕ)
    (f : (Fin p → Bool) → F) (x : Port p b → Bool) : F :=
  if ∀ w : Wire b, x (.inr (w,false)) = x (.inr (w,true)) then f (fun i => x (.inl i)) else 0

/-- Physical size includes all open data and catalyst ports. -/
structure Approximation (F : Type*) (k p : ℕ) where
  width : Fin k → ℕ
  network : BitNetwork F (Fintype.card (Port p width))

namespace Approximation

variable {F : Type*} [Field F] {k p : ℕ} (X : Approximation F k p)

def size : ℕ := X.network.cells + X.network.internal + Fintype.card (Port p X.width)

noncomputable def coeff (x : Port p X.width → Bool) : F :=
  X.network.eval (fun i => x ((Fintype.equivFin (Port p X.width)).symm i))

noncomputable def error (f : (Fin p → Bool) → F) :
    SiteTensor.Raw.{0} (Port p X.width) F :=
  ⟨fun _ => Bool, fun _ => inferInstance, X.coeff - ideal X.width f⟩

/-- A zero error has infinite gap. This convention also applies below zero ordinary price. -/
def Gap (f : (Fin p → Bool) → F) (D : ℝ) : Prop :=
  ∀ P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k)),
    (X.error f).coeff = 0 ∨ P.price (X.error f) (sites X.width) ≤ 2 * (∑ j, (X.width j : ℝ)) - D

/-- Testing the standard Euclidean frame suffices for all isometric frames
in arbitrary price spaces, including rotated and translated frames. -/
theorem gap_at {f : (Fin p → Bool) → F} {D : ℝ} (h : X.Gap f D)
    {M : Type*} [MetricSpace M] (Q : SpectralPlacementPrices F M)
    (e : EuclideanSpace ℝ (Fin k) → M) (he : Isometry e) :
    (X.error f).coeff = 0 ∨
      Q.price (X.error f) (e ∘ sites X.width) ≤ 2 * (∑ j, (X.width j : ℝ)) - D :=
  h (Q.pullback e he)

theorem Gap.mono {f : (Fin p → Bool) → F} {D D' : ℝ}
    (h : X.Gap f D) (lower : D' ≤ D) : X.Gap f D' := by
  intro P
  exact (h P).imp_right (fun hx => hx.trans (sub_le_sub_left lower _))

/-- Error when all data values have first been pinned, leaving just the catalyst bits. -/
noncomputable def pinnedError (f : (Fin p → Bool) → F) (pin : Fin p → Bool) :
    SiteTensor.Raw.{0} (Wire X.width × Bool) F :=
  ⟨fun _ => Bool, fun _ => inferInstance, fun w => (X.error f).coeff (Sum.elim pin w)⟩

def PointwiseGap (f : (Fin p → Bool) → F) (D : ℝ) : Prop :=
  ∀ P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k)), ∀ pin : Fin p → Bool,
    (X.pinnedError f pin).coeff = 0 ∨
      P.price (X.pinnedError f pin) (fun i => sites (p:=p) X.width (.inr i)) ≤
        2 * (∑ j, (X.width j : ℝ)) - D

end Approximation
end Hierarchy.Catalyst

end OAI
