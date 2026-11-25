import OAI.Hierarchy.DescentExteriorCalendarTableData

import OAI.Hierarchy.DescentExteriorSpineMatrix
import OAI.Hierarchy.DescentOrdinaryPinStep
import OAI.Hierarchy.DescentResetPinStep

namespace OAI
/-! # The actual ordinary and reset matrix words use the fixed exterior advice -/
namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing Catalyst DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open PinCohorts DescentHostDirectory DescentHostDegree
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k tail : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε u : ℝ} {S : AtomSchedule}
  {W : MarkedWorld F d P bits} {i z D wire hist z' D' : ℕ}
  {source : Reached W G q ε S k i z D wire hist}
  {a n : ℕ} {old:P→Bits a} {O:Type} {original:P→O}

namespace Chronology
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice} {nu : Normalize ((T.result he).state c)}
  {target : Reached nu.result G q ε S k (i+1) z' D' wire hist}
  (ticket : OrdinaryLink source he T c nu target)
  (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
  (owns : ∀pin,source.placement.hub (host source pin)=true)
  (past : Spine old (active source base radix) original (host source) n)

omit [Fintype P] in
theorem OrdinaryLink.matrix_word :
    let selected:=multiplier source.placement.fieldBits (BitDescription.scannedRows he source.placement.stage).μ
    let next:=ticket.pinStep base radix owns
    let ext:=Spine.promoteCut past.width (past.append next).width (ordinaryCut k (S.group_cut ticket.hubRows.choose))
    DescentExteriorMatrixUpdate.entry ext (matrixCode past.matrix) (matrixCode selected)=matrixCode (past.append next).matrix := by
  apply Spine.packed_update
  rfl
end Chronology

namespace ClosedReset
variable {n₀ h C f g cut : ℕ} {ctl : ResetRates G S k D n₀ h C f g cut tail}
  (b : ClosedReset source ctl) (owns : ∀pin,source.placement.hub (host source pin)=true)
  (past : Spine old (active source ctl.base ctl.radix) original (host source) n)

omit [Fintype P] in
theorem matrix_word :
    let next:=b.pinStep owns
    let ext:=Spine.promoteCut past.width (past.append next).width (Chronology.resetCut k (S.group_cut b.age))
    DescentExteriorMatrixUpdate.entry ext (matrixCode past.matrix) (matrixCode b.frame.basis)=
      matrixCode (past.append next).matrix := by
  apply Spine.packed_update
  rfl
end ClosedReset
end
end Hierarchy.DescentSixParty

end OAI
