import OAI.Hierarchy.DescentTerminalRoleWords
import OAI.Hierarchy.DescentSliceFields

namespace OAI
/-! # Physical scalar roles issued at a genuine seed, ordinary, or reset birth -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentBundleHistory DescentKernelHistory DescentEpochTagKeys
noncomputable section
variable {U : Type} {n A G p R N M : ℕ}

theorem shape_role {B : Type} {width : B→ℕ} {r : BitRecipe U B width} (hp : 0<p)
    (s : Shape p r) (v : r.Node) (old : Codec U n) (x : Fields A G) (birth : old.fits (r.tag v))
    (issued : Printed old x (r.tag v) (s.sliceFields v)) :
    written old p R x=((DescentBundleTagKeys.codec old A G p R).store ((s.recipe hp).tag v)).val+1 := by
  rw [Shape.tag_fields]
  exact written_read old x _ _ birth issued


theorem printed_role {B : Type} {widthAt : B→ℕ} {r : BitRecipe U B widthAt} (hp : 0<p)
    (s : Shape p r) (u : r.Node) (old : Codec U n) (x : Fin M→Fin N→Arrays n A G p R)
    (g : Fin M) (slot : Fin N) (birth : old.fits (r.tag u))
    (issued : Printed old (fields (x g slot)) (r.tag u) (s.sliceFields u)) :
    DescentSIMDLookup.digit (output n A G p R) slot.val (DescentSIMDLookup.digit (output n A G p R*N) g.val (rolePanel old (collect x)).val)=
      ((DescentBundleTagKeys.codec old A G p R).store ((s.recipe hp).tag u)).val+1 := by
  rw [rolePanel_read];exact shape_role hp s u old _ birth issued

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
