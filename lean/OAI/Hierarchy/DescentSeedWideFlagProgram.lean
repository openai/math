import OAI.Hierarchy.DescentSeedPackedHeaderNumbers
import OAI.Hierarchy.DescentPackedScore
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Native original-count flag checker and its exact instruction-table size -/
namespace Hierarchy.DescentWideSeedFlags
open Catalyst DescentSeedRoot ProtocolRAM
open ThreeFlat.RAM DescriptorExpr
noncomputable section
variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (R s payload bw : ℕ)
set_option quotPrecheck false
local notation "lanes_" => DescentPackedSeed.multiplicity payload s
local notation "base_" => endInput X R s payload
local notation "tab" => dictionary X R s payload
local notation "src" => source X R s payload

def check := DescentPackedScore.raw src tab base_ 1 (Fintype.card (Old X)) (R*8) lanes_ bw

omit [Field F] in
theorem names : DescentStaticWordColumn.names (check X R s payload bw)=135 := by
  simp only [check,DescentPackedScore.raw,DescentStaticWordColumn.names,SumScores.procedure,
    PhysicalInputPhases.writing,Term.labels_eq,SumScores.step_binds,DescentPackedScore.read,Expr.work]

end
end Hierarchy.DescentWideSeedFlags

end OAI
