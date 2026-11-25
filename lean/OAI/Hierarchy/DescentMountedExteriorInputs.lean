import OAI.Hierarchy.DescentExteriorContent
import OAI.Hierarchy.DescentLowCountBook
import OAI.Hierarchy.DescentRoleMountSpan

namespace OAI
/-! # The mounted role tables preserve the original exterior shelf and saved rotation words -/
namespace Hierarchy.DescentSixParty.Chronology

open DescentExterior DescentExteriorShelf DescentGL Computability.VPVNP.BurstRAM PrivateRAM

variable {w roleBase roof : ℕ} (mount : RoleMount w roleBase roof)
  (first size : ℕ) (source : ℕ → ℕ) (m : Memory w)

theorem RoleMount.between_counts_and_tables {a : ℕ} (past : first + size ≤ a) (low : a < roleBase) :
    mount.phase.image (DescentLowCountBook.output first source m size) a = m a :=
  (mount.frame _ a (.inl low)).trans (DescentLowCountBook.frame first source m size a (.inr past))

theorem RoleMount.loaded_after_counts {j r t e origin : ℕ} {M : Fin e → Layout (j+(j+r))}
    {x : Fin e → Plane j r → Fin t → Bool} {z : Hidden e j r t → Bool}
    (loaded : Loaded origin M x z m) (afterCounts : first + size ≤ origin)
    (beforeTables : origin + 17*span j r t e ≤ roleBase) :
    Loaded origin M x z (mount.phase.image (DescentLowCountBook.output first source m size)) := by
  intro col i hi
  have spanBound := Nat.mul_le_mul_right (span j r t e) (show col.val+1 ≤ 17 from col.isLt)
  rw [Nat.add_mul, one_mul] at spanBound
  have past : first + size ≤ (bank j r t e origin col.val).base + i := by
    change _ ≤ origin + col.val * span j r t e + i
    omega
  have low : (bank j r t e origin col.val).base + i < roleBase := by
    change origin + col.val * span j r t e + i < roleBase
    omega
  exact (mount.between_counts_and_tables first size source m past low).trans (loaded col i hi)

end Hierarchy.DescentSixParty.Chronology

end OAI
