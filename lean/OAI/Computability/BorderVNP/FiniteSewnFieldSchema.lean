import OAI.Computability.BorderVNP.FiniteSewnFieldStaging
import OAI.Computability.BorderVNP.PackedCompilerFields
import OAI.Computability.BorderVNP.PackedInheritedPlacementBoxes

/-! # Exterior sewing preserves the site's private compiler formats -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Crossing CellSparse Inherited

/-- Relative factor addresses at every true birth are retained verbatim. -/
theorem stage_relativeBoxes (s : Site) (n : ℕ) (runs : List Interval) (relative : s.RelativeBoxes) :
    (stage s n runs).RelativeBoxes := relative

/-- Every newly appended zero or equality interval meets the existing row
and profile-width schema, without adding any box reference. -/
theorem stage_schema (s : Site) (n : ℕ) (runs : List Interval) (schema : s.Schema) :
    (stage s n runs).Schema := by
  intro r hr
  rw [stage_rows] at hr
  rcases List.mem_append.mp hr with old | extra
  · exact schema r old
  · obtain ⟨p,_,rfl⟩ := List.mem_map.mp extra
    cases h : p.source <;> simp only [Interval.record,h] <;> exact ⟨trivial,trivial⟩

/-- The longest new exterior staging row is one nine-word equality.
All prior row/table/code/relative-address bounds therefore continue
to hold on the complete exterior-sewn compiler input. -/
theorem stage_compilerFields {D m : ℕ} {F : Type*} [Field F] (e : PaidIdentity F D m)
    (s : Site) (n : ℕ) (runs : List Interval) (L U : ℕ) (before : s.CompilerFields e L U) :
    (stage s n runs).CompilerFields e L U := by
  refine ⟨⟨stage_schema s n runs before.1.1,?_,before.1.2.2⟩,before.2⟩
  intro r hr
  rw [stage_rows] at hr
  rcases List.mem_append.mp hr with old | extra
  · exact before.1.2.1 r old
  · obtain ⟨p,_,rfl⟩ := List.mem_map.mp extra
    cases h : p.source with
    | none =>
      rw [Interval.record,h]
      change 6 ≤ 16*(e.count+1)
      omega
    | some j =>
      rw [Interval.record,h]
      change 9 ≤ 16*(e.count+1)
      omega

end Packing.SewnField

end BorderVNP
end Computability
end OAI
