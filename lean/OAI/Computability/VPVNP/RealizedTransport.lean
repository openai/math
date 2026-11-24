import OAI.Computability.VPVNP.WireGeodesic
import Mathlib.Data.Fin.VecNotation

/-!
# Transport in spaces whose finite configurations are realized

Corollary 2.5 applies the spectral wire transport inequality to the four
endpoints and the two fractional points in one joint realization. Its
common positive scale cancels in both the fractional distances and the
transport bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open WireTensor

variable {k : Type*} [Field k]

/-- The six-point wire inequality implies the same inequality in any space
whose finite configurations are spectral up to scale. -/
theorem fractionTransport_of_realizable {X : Type*} [PseudoMetricSpace X]
    (hwire : ∀ (J : Type) [Fintype J] [Nontrivial J] (F : SpectralPoint k J),
      @FractionTransport J F.wirePseudoMetric)
    (hX : RealizableConfigurations k X) : FractionTransport X := by
  intro a b c d x y t ht₀ ht₁ hx hy
  let p : Fin 6 → X := ![a,b,c,d,x,y]
  obtain ⟨w⟩ := hX 6 p
  let D (i j : Fin 6) := w.spectrum.wireDistance (w.label i) (w.label j)
  have eqD (i j : Fin 6) : dist (p i) (p j) = w.scale * D i j := w.distances _ _
  have fract {i j z : Fin 6} (h : AtFraction (p i) (p j) t (p z)) :
      @AtFraction _ w.spectrum.wirePseudoMetric (w.label i) (w.label j) t (w.label z) := by
    obtain ⟨hl, hr⟩ := h
    rw [eqD, eqD] at hl hr
    constructor
    · exact mul_left_cancel₀ w.scale_pos.ne' (hl.trans (mul_left_comm _ _ _))
    · exact mul_left_cancel₀ w.scale_pos.ne' (hr.trans (mul_left_comm _ _ _))
  have bound := hwire w.Parties w.spectrum ht₀ ht₁
    (fract (i := 0) (j := 1) (z := 4) hx) (fract (i := 2) (j := 3) (z := 5) hy)
  change D 4 5 ≤ (1-t) * D 0 2 + t * D 1 3 at bound
  change dist (p 4) (p 5) ≤ (1-t) * dist (p 0) (p 2) + t * dist (p 1) (p 3)
  rw [eqD, eqD, eqD]
  calc
    _ ≤ w.scale * ((1-t) * D 0 2 + t * D 1 3) := mul_le_mul_of_nonneg_left bound w.scale_pos.le
    _ = _ := by ring

end WireGeometry

end VPVNP
end Computability
end OAI
