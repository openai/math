import OAI.Hierarchy.DescentDenseHostTape
import OAI.Hierarchy.DescentHostMaskCore

namespace OAI
namespace Hierarchy.DescentSixParty.ResetInput
open DescentCommonHost
open ThreeFlat.RAM Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "pool" => DescentDenseHostOrder.roster Z.graph (Z.k-T.commonDepth) Ht
variable {H : ℕ} (vertex : Z.V↪Fin H)

/-- Last cell of the already executed sparse ordinal scan. It publishes the authentic count
of new hosts even when some raw slots and some whole old host rows have no occupant. -/
theorem hostTape_count {w ids : ℕ} (m : Memory w) :
    let tape:=Z.hostTape T vertex
    let out:=ProtocolRAMEndpointPrefix.image ids (DescentEdgeTapePrefix.before tape.span tape.rank) m tape.slots
    out (ids+tape.slots)=(Fintype.card ↥(commonNames Z T):Word w) := by
  dsimp only
  rw [ProtocolRAMEndpointPrefix.read _ _ _ _ _ le_rfl,
    DescentEdgeTapePrefix.before_end _ _ _ (Z.hostTape T vertex).inSlots]
  apply congrArg (fun n : ℕ => (n : Word w))
  change (∑ _ : (Z.hostTape T vertex).Parent, (1 : ℕ)) = Fintype.card ↥(commonNames Z T)
  rw [Finset.sum_const_nat (m := 1) (fun _ _ => rfl), Nat.mul_one, Finset.card_univ]
  exact
    (Fintype.card_congr (Equiv.refl ↥(commonNames Z T)) :
      Fintype.card (Z.hostTape T vertex).Parent = Fintype.card ↥(commonNames Z T))

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
