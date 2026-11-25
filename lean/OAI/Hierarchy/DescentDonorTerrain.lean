import OAI.Hierarchy.DescentDonorShape

namespace OAI
/-! # Decoding a stored matcher panel and its layout bit -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.ParentIncidence
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {r D cap d : ℕ}

/-- The old layout and chooser panel use the same original owner-board encoding. -/
def splitTerrain (raw : Cell (Owners.inputBits r D (2*cap) d)) : Bool × Panel r D (2*cap) d :=
  let p : Cell 1×Cell (d*fields r D (2*cap)):=finProdFinEquiv.symm (finCongr (pow_add 2 1 (d*fields r D (2*cap))) raw)
  (decide (p.1.val=1),decodePanel p.2)

@[simp] theorem split_register (l : Bool) (u : Panel r D (2*cap) d) : splitTerrain (Owners.register l u)=(l,u) := by
  cases l <;> simp [splitTerrain,Owners.register]

end
end Hierarchy.DescentPacking.PackedMatch.Local.ParentIncidence

end OAI
