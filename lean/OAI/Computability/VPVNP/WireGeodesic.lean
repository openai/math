import OAI.Computability.VPVNP.SpectralRealizable
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Fractional points in the spectral wire geometry

Corollary 2.5 and Section 4 of *VP and VNP differ over every field* use
the metric characterization of a point at a specified fraction along a
segment. The six-point transport inequality makes such a point unique in a
metric space and controls its dependence on both endpoints.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open WireTensor

variable {X : Type*} [PseudoMetricSpace X]

/-- The two endpoint distances specifying a fractional point. -/
def AtFraction (x y : X) (t : ℝ) (z : X) : Prop :=
  dist x z = t * dist x y ∧ dist z y = (1-t) * dist x y

/-- Every pair admits an interpolating point at each fraction. -/
def HasFractions (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ (x y : X) (t : ℝ), 0 ≤ t → t ≤ 1 → ∃ z, AtFraction x y t z

/-- Equation (2.2), controlling interpolation along two segments. -/
def FractionTransport (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ {a b c d x y : X} {t : ℝ}, 0 ≤ t → t ≤ 1 → AtFraction a b t x → AtFraction c d t y →
    dist x y ≤ (1-t) * dist a c + t * dist b d

/-- Every finite list of points is jointly realized up to one scale in a
spectral wire pseudometric. -/
def RealizableConfigurations (k X : Type*) [Field k] [PseudoMetricSpace X] : Prop :=
  ∀ n (p : Fin n → X), RealizableUpToScale k (fun i j ↦ dist (p i) (p j))

theorem AtFraction.dist_eq_zero_of_transport (h : FractionTransport X)
    {x y z w : X} {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hz : AtFraction x y t z) (hw : AtFraction x y t w) : dist z w = 0 := by
  have bound := h ht ht' hz hw
  simp only [dist_self, mul_zero, add_zero] at bound
  exact le_antisymm bound dist_nonneg

/-- Metric separation gives uniqueness at every fraction. -/
theorem atFraction_unique {Y : Type*} [MetricSpace Y] (h : FractionTransport Y)
    {x y z w : Y} {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hz : AtFraction x y t z) (hw : AtFraction x y t w) : z = w :=
  dist_eq_zero.mp (hz.dist_eq_zero_of_transport h ht ht' hw)

end WireGeometry

end VPVNP
end Computability
end OAI
