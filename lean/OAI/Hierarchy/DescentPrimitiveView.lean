import OAI.Hierarchy.DescentPrimitivePalette
import OAI.Hierarchy.DescentBundleWorld

namespace OAI
/-! # Relabeling a genuine bit recipe into a common coefficient dictionary -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentBundleHistory Computability.BorderVNP.Crossing
noncomputable section
variable {F : Type} [Field F]
section Relabel
variable {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {B : BitDescription W}
    {U : Type} (dict : U→List (List Bool)→F) (code : Encoding U dict B)

def Encoding.view : BitDescription W where
  Tag:=U
  scalar:=dict
  recipe v:=(B.recipe v).retag code.code
  correct:=by
    intro a x v
    rw [BitRecipe.retag_eval]
    have read : dict ∘ code.code=B.scalar := funext code.correct
    rw [read]
    exact B.correct a x v

def Encoding.viewShape {p R : ℕ} (sh : WorldShape p R B) : WorldShape p R (code.view dict) where
  sites v:=(sh.sites v).retag code.code
  stride:=sh.stride
  edges:=sh.edges

end Relabel

end
end Hierarchy.DescentPrimitivePalette

end OAI
