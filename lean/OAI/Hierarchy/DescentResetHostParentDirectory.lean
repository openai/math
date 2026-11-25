import OAI.Hierarchy.DescentResetHostParents
import OAI.Hierarchy.DescentResetStemKeyReindex

namespace OAI
/-! # Recovering the preceding native actor at every actual successor actor index -/
namespace Hierarchy.DescentSixParty.ResetInput
open DescentDenseHostOrder DescentCommonHost DescentHubBits DescentCensusRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
variable {H : ℕ} (vertex : Z.V↪Fin H)

/-- Every physical dense actor has a predecessor actor even when the underlying sets are
empty. This reading agrees with the public vertex order chosen by the closed reset. -/
def parentIndex (j : Fin (Fintype.card ↥(Z.commonNames T))) : Fin H :=
  let row:=DescentStageEdgeReceipt.dense (Z.denseHostRank T vertex)
  vertex (position Z.graph (row.symm j).val)

theorem parentIndex_read (v : ↥(Z.commonNames T)) :
    parentIndex Z T vertex (Z.denseHostRank T vertex v)=vertex (position Z.graph v.val) := by
  let row:=DescentStageEdgeReceipt.dense (Z.denseHostRank T vertex)
  change vertex (position Z.graph (row.symm (row v)).val)=_
  rw [Equiv.symm_apply_apply]

theorem parent_directory {w : ℕ} (dest : ℕ) (out : Memory w)
    (reads : ∀v,out (dest+(Z.denseHostRank T vertex v).val)=((vertex (position Z.graph v.val)).val:Word w)) :
    DescentResetStemKeyReindex.Directory dest (parentIndex Z T vertex) out := by
  intro j
  let row:=DescentStageEdgeReceipt.dense (Z.denseHostRank T vertex)
  obtain ⟨v,rfl⟩:=row.surjective j
  change out (dest+(Z.denseHostRank T vertex v).val)=((parentIndex Z T vertex (Z.denseHostRank T vertex v)).val:Word w)
  rw [parentIndex_read Z T vertex]
  exact reads v

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
