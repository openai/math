import OAI.Computability.VPVNP.DegreeRefreshActualStep
import OAI.Computability.VPVNP.NetworkHalfIso

/-!
# Relabeling the binary lanes of a wire network

The compression steps split the current lane into fresh port or packing
coordinates and the remaining lane. An additive equivalence on lanes
transports every base displacement, and its inverse recovers each original
width. This gives a network isomorphism and preserves the wire energy.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open NetworkKernel Refresh

variable {V A B : Type} {d : ℕ} [AddCommGroup A] [AddCommGroup B]

/-- Relabel all lane displacements using the same additive equivalence. -/
def relane (G : LiftedSlots V d A) (e : A ≃+ B) : LiftedSlots V d B where
  base := G.base
  displacement p := e (G.displacement p)

/-- A wire keeps the width at its original outgoing slot and lane. -/
def relaneWidths (e : A ≃+ B) (w : (V × Fin d) × A → ℕ) (p : (V × Fin d) × B) : ℕ :=
  w (p.1,e.symm p.2)

variable [Fintype V] [Fintype A] [Fintype B]

/-- Inverse lane relabeling identifies both ends and the payload of each
actual wire. Separate slots remain separate edges. -/
noncomputable def relaneIso (G : LiftedSlots V d A) (e : A ≃+ B) (w : (V × Fin d) × A → ℕ) :
    Network.Iso (actualWireGraph (relane G e) (relaneWidths e w)) (actualWireGraph G w) where
  site := (Equiv.refl V).prodCongr e.symm.toEquiv
  edge := ((Equiv.refl V).prodCongr e.symm.toEquiv).prodCongr (Equiv.refl (Fin d))
  src _ := rfl
  dst := by
    rintro ⟨⟨x,g⟩,i⟩
    change ((G.base.target (x,i)).1, e.symm (g + e (G.displacement (x,i)))) = _
    rw [map_add, e.symm_apply_apply]
    rfl
  payload _ := Equiv.refl _

/-- The lane coordinate change preserves the number of positions. -/
theorem relane_card_sites (e : A ≃+ B) : Fintype.card (V × B) = Fintype.card (V × A) :=
  Fintype.card_congr ((Equiv.refl V).prodCongr e.symm.toEquiv)

/-- Every sum over wire widths is preserved, in particular the sum of
squared widths divided by the common arc mass. -/
theorem relane_sum_widths (e : A ≃+ B) (w : (V × Fin d) × A → ℕ)
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑ p, f (relaneWidths e w p)) = ∑ p, f (w p) :=
  ((Equiv.refl (V × Fin d)).prodCongr e.symm.toEquiv).sum_comp (fun p => f (w p))

end Compression

namespace NetworkKernel

@[simp] theorem Step.reindexInput_output {N M : Network} {R : Type*} [CommSemiring R]
    (s : Step R N) (input : N.Iso M) (i : s.Choice) :
    ((s.reindexInput input).term i).output = (s.term i).output := rfl

end NetworkKernel

end VPVNP
end Computability
end OAI
