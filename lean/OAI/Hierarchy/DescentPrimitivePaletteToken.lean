import OAI.Hierarchy.DescentPrimitivePaletteLabels
import OAI.Hierarchy.DescentPrimitivePalettePrintedBits
import OAI.Hierarchy.DescentEpochTagKeys
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # The original palette encoding used by every physical coefficient lookup -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentKernelHistory DescentEpochTagKeys DescentResetGates DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]
section
variable {G : PoweredGadget F} {s Z : ℕ} (op : RotorSpec)
def codec : Codec (Label G s Z op) (colors G s Z op) :=
  (census s).birth ((gadget Z G.C).birth
    ((Codec.ofEquiv (Equiv.ofUnique Unit (Fin 1))).birth (Codec.ofEquiv (Fintype.equivFin _))))

end
variable (G : PoweredGadget F) (s Z : ℕ) (op : RotorSpec)
def token (label : Label G s Z op) : Cell (printedBits G s Z op) :=
  ⟨((codec (G:=G) op).store label).val+1,by
    have bounded:=((codec (G:=G) op).store label).isLt
    exact (Nat.succ_lt_succ bounded).trans_le (Nat.le_pow_clog (by decide) _)⟩

theorem token_val (label : Label G s Z op) :
    (token G s Z op label).val=((codec (G:=G) op).store label).val+1:=rfl

end
end Hierarchy.DescentPrimitivePalette

end OAI
