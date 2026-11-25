import OAI.Hierarchy.DescentDatedSeedPublicCode

namespace OAI
/-! # Size and time of the original seed validator followed by the native seed producer -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSeedRoot DescentPackedSeed DescentTerminalEpochChart
open DescentInitialHost DescentColonies DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM Catalyst Computability.BorderVNP.Crossing ThreeFlat.Diagonal
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F J A : Type} [Field F] [Fintype J] [DecidableEq J] {k p R d G H : ℕ}
variable (X : Approximation F k p) (name : J≃Fin G) (digits : Fin R≃J×Block d)
  (host : Vertex X↪Fin H) (l : Layout) (w : ℕ)
local notation "checker" => DescentTerminalPackedSeedFlags.check X R l.seedWidth w ([] : List (Source A))
def clock (H G d R : ℕ) :=
  4+(DescentPackedSeed.rows X R l.seedWidth w+1)*66+DescentDatedSeedStartup.clock X l H G d

omit [Fintype J] [DecidableEq J] in
theorem program_names :
    DescentStaticWordColumn.names (program (A:=A) X name digits host l w)≤
      135+nameBound X l H G d := by
  have count : DescentStaticWordColumn.names checker=135 := by
    simp only [DescentTerminalPackedSeedFlags.check,DescentPackedScore.raw,
      DescentStaticWordColumn.names,SumScores.procedure,PhysicalInputPhases.writing,Term.labels_eq,
      SumScores.step_binds,DescentPackedScore.read,Expr.work]
  rw [program,DescentStaticWordColumn.names_seq,count]
  exact Nat.add_le_add_left (hardware X name digits host l w).2 135

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
