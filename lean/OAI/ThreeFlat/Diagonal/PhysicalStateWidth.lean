import OAI.ThreeFlat.Diagonal.PhysicalStage

namespace OAI
/-! # Largest individual width of a physical state -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression
open scoped Classical
noncomputable section

variable {d lanes D rem : ℕ} {F : Type} [Field F]

def State.maxWidth (A : State d lanes) : ℕ := Finset.univ.sup A.width

theorem State.width_le_maxWidth (A : State d lanes) (e) : A.width e ≤ A.maxWidth :=
  Finset.le_sup (f := A.width) (Finset.mem_univ e)

theorem State.maxWidth_le (A : State d lanes) {n : ℕ} (h : ∀ e, A.width e ≤ n) : A.maxWidth ≤ n :=
  Finset.sup_le fun e _ => h e

def Move.WidthBound {A : State d lanes} (R : Move F A D rem) (factor : ℕ) : Prop :=
  ∀ i, (R.next i).maxWidth ≤ factor*(1+A.maxWidth)

theorem Move.widthBound_degree {A : State d lanes} {D' : ℕ} (h : D=D')
    (R : Move F A D rem) {factor : ℕ} (H : R.WidthBound factor) :
    (h ▸ R : Move F A D' rem).WidthBound factor := by
  cases h
  exact H

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
