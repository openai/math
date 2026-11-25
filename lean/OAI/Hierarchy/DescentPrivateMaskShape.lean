import OAI.Hierarchy.DescentResetStemProject
import OAI.Hierarchy.DescentResetRosterFunctions

namespace OAI
/-! # Static allocation of the private endpoint/width dictionaries and their successor rows -/
namespace Hierarchy.DescentPrivateMaskDeck
open DescentSIMDLookup DescentResetLocalRoster
noncomputable section
structure Shape where
  oldHosts : ℕ
  shapes : ℕ
  groups : ℕ
  blocks : ℕ
  oldBatch : ℕ
  batch : ℕ
  cap : ℕ
  rawBits : ℕ
  metaBits : ℕ
  residual : ℕ
  ports : ℕ

namespace Shape
variable (A : Shape)
def panels := A.rawBits*(A.cap*5)
def words := 2^(A.panels*A.oldBatch)
def keys := 2*(rootSlots A.residual A.ports*A.cap)
def «fields» := A.keys*3
def count := (A.cap*3)*A.words
def projected (base : ℕ) := base+A.count
def endAddress (base : ℕ) := DescentResetStemProject.endAddress (A.projected base) A.fields
  (A.oldHosts*A.shapes) A.groups A.blocks A.metaBits A.oldBatch A.batch

theorem translate (base : ℕ) : A.endAddress base=base+A.endAddress 0 := by
  unfold endAddress projected
  rw [DescentResetStemProject.extent (base + A.count),
    DescentResetStemProject.extent (0 + A.count), Nat.zero_add, Nat.add_assoc]

theorem cuts (base : ℕ) : base≤A.projected base ∧ A.projected base≤A.endAddress base :=
  ⟨Nat.le_add_right ..,by unfold endAddress;rw [DescentResetStemProject.extent];exact Nat.le_add_right ..⟩


end Shape
end
end Hierarchy.DescentPrivateMaskDeck

end OAI
