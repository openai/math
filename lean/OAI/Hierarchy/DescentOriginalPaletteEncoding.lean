import OAI.Hierarchy.DescentPrimitivePaletteLabels
import OAI.Hierarchy.DescentSelectedRotor
import OAI.Hierarchy.DescentLaneGates
import OAI.Hierarchy.DescentHubSeedHistory
import OAI.Hierarchy.DescentTrunkBitHistory
import OAI.Hierarchy.DescentGadgetHistory
import OAI.Hierarchy.DescentRecipeNodeTypes

namespace OAI
/-! # The original coefficient dictionary and a scalar encoding of a bit history -/
namespace Hierarchy.DescentPrimitivePalette
open DescentCompiler DescentSixParty DescentKernelHistory DescentRotor DescentResetGates
noncomputable section
variable {F : Type} [Field F] {s Z p : ℕ} (G : PoweredGadget F) (op : RotorSpec)

abbrev Runnable (F : Type) [Field F] (op : RotorSpec) := ∀π,Configures F op.arcs op.C op.w π
def gate (menu : Runnable F op) (p : ℕ) : CanonicalTag (2^op.n)→List (List Bool)→F :=
  DescentLaneGates.scalar op.arcs op.C op.w p (rom op.arcs op.C op.w (fixedTable menu))

def dictionary (menu : Runnable F op) (p : ℕ) : Label G s Z op→List (List Bool)→F :=
  Sum.elim seedRead (Sum.elim (gadgetScalar G) (Sum.elim (fun _=>equalWord) (gate op menu p)))

variable {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

structure Encoding (U : Type) (read : U→List (List Bool)→F) (B : BitDescription W) where
  code : B.Tag→U
  correct : ∀a,read (code a)=B.scalar a

end
end Hierarchy.DescentPrimitivePalette

end OAI
