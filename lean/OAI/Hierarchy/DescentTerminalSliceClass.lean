import OAI.Hierarchy.DescentTerminalSliceRuns
import OAI.Hierarchy.DescentPrimitivePaletteLabels
import OAI.Hierarchy.DescentSliceFields
import OAI.Hierarchy.DescentFreshRoleHeaderData

namespace OAI
/-! # Select the recorded operand partition by its physical primitive token -/
namespace Hierarchy.DescentTerminalSliceRuns
open DescentBundleHistory DescentKernelHistory DescentSixParty DescentPrimitivePalette
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F) (p s:ℕ) {Z:ℕ} {op:RotorSpec}
def classify : Label G s Z op→Layout
  | .inl _=>.seed (s/p)
  | .inr (.inl (z,prof,h))=>.ordinary (DescentFreshRoleFields.header G p z.val prof h)
  | .inr (.inr (.inl ()))=>.relay
  | .inr (.inr (.inr _))=>.rotor

theorem Slice.positive {p:ℕ} {α:Type} (a:DescentBundleHistory.Slice p α) (hp:0<p) : 0<a.count :=
  (Nat.zero_le _).trans_lt (a.fits ⟨0,hp⟩)

variable {U A:Type} {w:A→ℕ} {r:BitRecipe U A w} (t:Shape p r) (u:r.Node)

theorem used_slice (hp:0<p) (c:SliceCode) (hc:c∈(t.sliceFields u).flatten) : 0<c.count := by
  obtain ⟨part,hpart,inPart⟩:=List.mem_flatten.mp hc
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hpart
  obtain ⟨g,rfl⟩:=List.mem_ofFn.mp inPart
  exact Slice.positive (t.chunk u j g) hp

theorem classify_read (hp:0<p) (tag:Label G s Z op)
    (valid:(classify G p s tag).correct (t.sliceFields u)) :
    (classify G p s tag).restore (repeatFields (t.sliceFields u).flatten)=t.sliceFields u :=
  Layout.restore_correct _ _ valid (used_slice p t u hp)

end
end Hierarchy.DescentTerminalSliceRuns

end OAI
