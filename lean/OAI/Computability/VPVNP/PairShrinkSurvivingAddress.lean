import OAI.Computability.VPVNP.PairShrinkOldHalfAddresses
import OAI.Computability.VPVNP.PairShrinkSurvivingOperands

/-!
# Private argument addresses of surviving wire endpoints

A surviving row supplies the numerical port at its selected endpoint.
Division by the output degree recovers the site ordinal and remainder
recovers the slot. The private packet node is a separate runtime operand.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSurvivingAddress

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData
open CompressorRecords CompressorRecords.PhaseRecipe CompressorRecords.PortRefresh.ArgumentAddress
open ShrinkOldHalves.Physical ShrinkSurvivingOperands NodeArguments
open private unpack word_of_val from OAI.Computability.VPVNP.PairShrinkOldHalfAddresses

/-- Use the oriented port for both the site ordinal and the slot in the resident packet. -/
def field (degree : ℕ) (H : Header) (node : Expr) (dir : Bool) (port : Expr) : Expr :=
  let args := { H.input degree port with node := node }
  PortRefresh.ArgumentAddress.field degree args dir (port.mod (.lit degree))

variable {a b g w pad : ℕ} (X : State a (packingLaneBits a g)) (layout : Bool)
variable (subdiv : Fin 4 → ℕ) (width : X.packingData.Motif → Fin 4 → ℕ)
variable {next : Equiv.Perm (X.Base × BitWord (packingTagBits (2 ^ a)))}
variable (I : X.packingData.ShrinkIndex layout subdiv next (2 ^ b) pad)
variable (m : X.packingData.Motif) (t : Fin 4) (dir : Bool) (j : Fin (subdiv t))
local notation "Y" => X.shrinkOutputState layout subdiv width I

/-- The actual port of the directed subdivision at either endpoint is the
native slot of the local half assignment, including the translated target lane. -/
theorem oriented_port_eq :
    let e := X.packingData.shrinkArcEquiv layout subdiv I.outgoing (.inl ⟨t, m, j⟩)
    (if dir then I.graph.actualGraph.target e else e) =
      (site X layout m t dir, slot X layout subdiv width I m t dir j) := by
  have ends := X.packingData.shrinkArc_endpoints layout subdiv I ⟨t, m, j⟩
  cases dir with
  | false => exact Prod.ext ends.1 rfl
  | true => exact Prod.ext ends.2 rfl

/-- The computed address is exactly the source pointer of the reverse-copy
loop for this subdivision in the selected resident packet. -/
theorem field_eq (H : Header) (T : IncidenceDirectory w) (A : Arena)
    {layer stride : ℕ} {pub : Fin 5 → Word w} {state : Word w} {mem : Memory w}
    (stored : H.Stored T A layer stride pub state mem) (cols : T.ActualColumns (Y) mem)
    (capacity : Fintype.card (Y).Base * 2 ^ g * 2 ^ b ≤ 2 ^ w)
    (degreeFits : 2 ^ b < 2 ^ w) (node port : Expr) (nodeID : ℕ)
    (nodeEq : node.eval pub state mem = CursorRAM.encode w nodeID)
    (portEq : port.eval pub state mem = IncidenceDirectory.actualPort (Y)
      (site X layout m t dir, slot X layout subdiv width I m t dir j)) :
    (field (2 ^ b) H node dir port).eval pub state mem = CursorRAM.encode w
      (A.fieldAddress (Y) (site X layout m t dir) nodeID dir
        (slot X layout subdiv width I m t dir j)) := by
  let u := site X layout m t dir
  let k := slot X layout subdiv width I m t dir j
  let n := siteOrdinal (Y) u
  let args := { H.input (2 ^ b) port with node := node }
  have idFit := (IncidenceDirectory.actualOrder (Y) (u, k)).isLt.trans_le capacity
  have val : (port.eval pub state mem).val = n * 2 ^ b + k.val := by
    rw [portEq, IncidenceDirectory.actualPort_number]
    exact (Nat.mod_eq_of_lt idFit).trans (IncidenceDirectory.actualOrder_val (Y) (u, k))
  have dval : (CursorRAM.encode w (2 ^ b)).val = 2 ^ b := Nat.mod_eq_of_lt degreeFits
  have split := unpack (port.eval pub state mem) (CursorRAM.encode w (2 ^ b)) n k.val
    (by rw [dval]; exact val) (by rw [dval]; exact k.isLt)
  have rep : Represents pub state mem args (Y) u T A nodeID :=
    ⟨stored.arenaBase, stored.arenaStride, nodeEq, word_of_val split.1,
      stored.actualIn, stored.width⟩
  exact eval_field rep cols dir _ k degreeFits (word_of_val split.2)

end PairSimulation.ShrinkSurvivingAddress

end VPVNP
end Computability
end OAI
