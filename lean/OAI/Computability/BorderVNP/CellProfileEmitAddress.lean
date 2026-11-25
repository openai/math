import OAI.Computability.BorderVNP.CellEmitAddress
import OAI.Computability.BorderVNP.CellProfileEmitFields
import OAI.Computability.BorderVNP.CellProfileGenerator

/-! # Native descriptors for physical profile ports and scratch rectangles -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

variable {α : Type} {ea : α → List Bool}

/-- Encode one port's affine address from the three supplied binary fields. -/
noncomputable def portAddr {p : α → Port} {i k : α → NatExpr}
    (hp : Procedure ea Typed.port p) (hi : Address ea i) (hk : Address ea k) :
    Address ea (fun x => (p x).expr (i x) (k x)) := by
  let z := ProfileData.portFields.comp hp
  let b := (Procedure.first ..).comp z
  let strides := (Procedure.second ..).comp z
  let c := (Procedure.first ..).comp strides
  let l := (Procedure.second ..).comp strides
  exact addAddr (addAddr (litAddr b) (mulAddr hi (litAddr c))) (mulAddr hk (litAddr l))

/-- Prefix the affine port address by the number of locally allocated private flags. -/
noncomputable def shiftedPortAddr {off : α → ℕ} {p : α → Port} {i k : α → NatExpr}
    (ho : Procedure ea Nat.bits off) (hp : Procedure ea Typed.port p) (hi : Address ea i) (hk : Address ea k) :
    Address ea (fun x => Profile.portExpr (off x) (p x) (i x) (k x)) :=
  addAddr (litAddr ho) (portAddr hp hi hk)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
