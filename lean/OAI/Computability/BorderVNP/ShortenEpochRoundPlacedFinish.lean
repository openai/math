import OAI.Computability.BorderVNP.ShortenEpochRoundFinish
import OAI.Computability.BorderVNP.ShortenPreparedChildren
import OAI.Computability.BorderVNP.ShortenEpochPlacedVariance
import OAI.Computability.BorderVNP.ShortenCatalogFixed

/-!
# Rounding the last physical node of a shortening epoch

The charge mask in the rounding estimate contains precisely the positive
charged segments, including all and only the midpoint records used by the
physical node. Every sewn output has the canonical quotient midpoints needed
by this identification.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PlacedPack

open BorderVNP.Crossing BorderVNP.Cover BorderVNP.Epoch BorderVNP.Epoch.Round CombiningStep Finset
open scoped Classical

variable {D d : ℕ} {I : Type} [Fintype I] {P : Type} {R : Type*} {bits : P → ℕ} (p : PlacedPack D P bits R I d)

/-- Geometrically coincident edges have zero weighted length. -/
theorem positive_length : chargedLength p.pack.layout p.site p.active = p.length := by
  unfold chargedLength length
  apply sum_congr rfl
  intro e _
  by_cases h : p.site (p.pack.layout.src e) = p.site (p.pack.layout.dst e)
  · simp [active,h]
  · simp [active,h]

/-- The output midpoints are the quotient midpoints used by the rounding estimate. -/
def canonical : Prop := ∀ e, p.midpoint e = surfaceMidpoint
  (p.site (p.pack.layout.src e)) (p.site (p.pack.layout.dst e))

/-- The output charge mask and exact quotient midpoints identify the recurrence's X with the
tile concentration on which the final rounding estimate acts. -/
theorem final_coordinates {l : ℕ} (η : d+1 = l) (hc : p.canonical) :
    chargedLength p.pack.layout (levelCast η ∘ p.site) p.active = p.length ∧
    tileConcentration (midpointMass (by omega) (levelCast η ∘ p.site) p.active) = p.concentration := by
  subst l
  refine ⟨p.positive_length,?_⟩
  have h := p.active_midpoint_concentration p.active p.active_iff
  have hm (e : Wires p.pack p.active) : p.midpoint e.val =
      surfaceMidpoint (p.site (p.pack.layout.src e.val)) (p.site (p.pack.layout.dst e.val)) := hc e.val
  simp_rw [hm] at h
  convert! h using 1

end Shortening.PlacedPack

namespace Shortening.PlacedStep

open BorderVNP.Crossing BorderVNP.Cover BorderVNP.Epoch
variable {D m k d d' : ℕ} {I : Type} [Fintype I] [NeZero D] {P B : Type} [Fintype B] {bits : P → ℕ} {K : Type*} [Field K]
    {child : Fin k → PlacedPack D P bits K I d} (s : PlacedStep m B d' child)
    (e : PaidIdentity K D m)

/-- The final physical node satisfies the midpoint convention on every attained histogram. -/
theorem result_canonical (i : s.Index e) : (s.result e i).canonical := fun _ => rfl

end Shortening.PlacedStep

end BorderVNP
end Computability
end OAI
