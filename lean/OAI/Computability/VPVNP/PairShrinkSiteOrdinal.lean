import OAI.Computability.VPVNP.PairShrinkSelectedOccurrence

/-! # Numerical owner of a selected shrinking output row -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage.RoleDomains

open Compression CompressorRecords LocalHistory TraversalRows TraversalRoles ShrinkRoleDirectory

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    {K : Type*} [CommRing K] (f : B.Entry → K) (hf : B.IsSolution f)
    {lanes : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (branch : (B.execute f hf T hT X).Choices)

local notation "passes₀" => executeLevels B f hf T hT X branch
local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor

/-- Output-site ordinal in the chronological level's stored site count. -/
noncomputable def siteId (x : ShrinkSite (passes₀)) : Fin (passes₀)[x.val.1].outputSites :=
  ⟨((outputOrder (passes₀)[x.val.1]).entries.symm x.val.2).val, by
    rw [← levelLayer_count B f hf (passes₀)[x.val.1]]
    exact ((outputOrder (passes₀)[x.val.1]).entries.symm x.val.2).isLt⟩

/-- The native owner and the physical site row have the same natural index. -/
theorem siteId_val (x : ShrinkSite (passes₀)) :
    (siteId B f hf T hT X branch x).val = (MapResidentRows.siteIndex x.occurrence.state x.occurrence.site).val :=
  x.occurrence.ordinal.symm

/-- The chronological site address used by the physical dispatcher and by
the selected canonical family coincide before conversion to machine words. -/
theorem rowAddress_siteId (base : ℕ) (x : ShrinkSite (passes₀)) :
    ShrinkRoleDirectory.address B.recordLimit base (leaf₀) (passes₀) x.val =
      TraversalRows.address B.recordLimit (layerBase B.recordLimit base (selected B f hf T hT X branch)
        (x.val.1.val+1)) (siteId B f hf T hT X branch x).val := rfl

end PairSimulation.VertexImage.RoleDomains

end VPVNP
end Computability
end OAI
