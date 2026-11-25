import OAI.Hierarchy.TaggedWirePacketFaces

namespace OAI
/-! # Native coordinates and oriented faces of an earned placement -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip
open scoped Classical Fin.CommRing
variable {S : PurchaseSampler} {h d k n w : ℕ} {A B : Type}
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "Ports" => StripPorts S h d k C (Fin n) B

def EarnedPlacement (p : Ports) (b : Board) (m : Memory w) (reg : Word w)
    (col : C → Columns h d) (extra : A⊕B→DistinctPair X)
    (row : Fin b.rows→Site h d k×Site h d k) : Prop :=
  (∀c,((p.column c).eval m reg).val=((Fintype.equivFin _) (col c)).val) ∧
    ∃idx : R→Fin b.rows, ∃mate : C→Fin k→Fin b.rows,
      (∀r : R,paidRole r→((p.primary b r).eval m reg).val=(idx r).val) ∧
      (∀c j,((p.mate b (.catalyst c j : R)).eval m reg).val=(mate c j).val) ∧
      (∀e l (v : Fin b.rows),((b.coreOnly (p.horizontal e l)).eval m reg).val=v.val →
        Faces (Prod.map col id) (ColumnWires.ends (horizontal n) extra (.horizontal e l)) (row v)) ∧
      (∀j (v : Fin b.rows),((p.probe j).eval m reg).val=v.val →
        Faces (Prod.map col id) (extra (.inr j)) (row v))

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
