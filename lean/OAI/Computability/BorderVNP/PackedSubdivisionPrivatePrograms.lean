import OAI.Computability.BorderVNP.PackedSubdivisionOriginal
import OAI.Computability.BorderVNP.PackedSubdivisionRelay

/-! # Installing every physical private program of an equality-subdivided pack -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision

open Crossing
open scoped Classical

variable {D m n np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (route : N.WireRoutes) (v : N.Site) (oldID : N.Edge ↪ Fin m)
    (newID : (N.subdivide route).Edge ↪ Fin n) (portID : P ↪ Fin np)

/-- Carry the earlier birth program and its complete observation fibers across the
actual first-hop, last-hop and exterior-port copies at this site. -/
noncomputable def originalLineage (prior : Site.Lineage (incoming N v)) :
    Site.Lineage (incoming (N.subdivide route) (.inl v)) :=
  ⟨prior.birth,originalProgram N route v oldID newID portID prior.program,
    originalRetention N route v oldID newID portID prior.retention prior.size,rfl⟩

/-- The subdivided pack installs the original endpoint programs at retained sites
and the one-row equality program at every actual intermediate hop. -/
noncomputable def subdividePrivatePrograms (prior : Site.Programs N) : Site.Programs (N.subdivide route)
  | .inl v => originalLineage N route v oldID newID portID (prior v)
  | .inr j => relayLineage N route newID portID j

/-- Every retained original site still points to its own original birth program. -/
theorem subdivide_birth (prior : Site.Programs N) :
    (subdividePrivatePrograms N route oldID newID portID prior (.inl v)).birth = (prior v).birth := rfl

/-- Both the inherited birth program and each new equality relay are local. -/
theorem subdivide_birth_local (prior : Site.Programs N) (locality : ∀ v, (prior v).birth.Local)
    (z : (N.subdivide route).Site) :
    (subdividePrivatePrograms N route oldID newID portID prior z).birth.Local := by
  rcases z with v | j
  · exact locality v
  · exact relay_local N route newID portID j

/-- Every new program models exactly its site in the genuine subdivided network,
including the signed and tagged observations of each retained prior program. -/
theorem subdivide_models {R : Type*} [AddCommMonoid R] [One R] (t : N.Tables R)
    (weight : List (Bool × Option ℕ) → R) (unit : weight [] = 1) (prior : Site.Programs N)
    (locality : ∀ v, (prior v).birth.Local)
    (models : ∀ v, (prior v).program.Models N oldID portID v (prior v).size weight t)
    (z : (N.subdivide route).Site) :
    let next := subdividePrivatePrograms N route oldID newID portID prior z
    next.program.Models (N.subdivide route) newID portID z next.size weight (N.subdivideTables route t) := by
  rcases z with v | j
  · exact original_models N route v oldID newID portID t (prior v).program (prior v).size
      ((prior v).retention.locality (locality v)) weight (models v)
  · exact relay_models N route newID portID j weight unit t

end Packing.Inherited.Subdivision

end BorderVNP
end Computability
end OAI
