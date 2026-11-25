import OAI.Computability.BorderVNP.CubeTeamOwnedGroups
import OAI.Computability.BorderVNP.TransmissionPinsPositive
import OAI.Computability.BorderVNP.RoutingISACubeConstantRun

/-! # Event signs of the native owned-group traversal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA
open private scan Indexing Indexing.lookup Indexing.advance ownerCode from OAI.Computability.BorderVNP.CubeScatterDispatch

private theorem mode_program_positive (xs : List Mode) : (program xs).positive = true := by
  have hc (a : Mode) : a.code.positive=true := by cases a <;> rfl
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [program,Code.positive,hc,ih,Bool.and_self]

private theorem scan_positive (key : Reg) (advance : Code) (ha : advance.positive=true)
    {k : ℕ} (branches : Fin k → Code) (hb : ∀ j,(branches j).positive=true) :
    (scan key advance branches).positive=true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [scan,Code.positive,hb,ha,ih (branches ∘ Fin.succ) (fun j ↦ hb j.succ),Bool.and_self]

private theorem lookup_positive (idx : Indexing) {k : ℕ} (branches : Fin k → Code)
    (hb : ∀ j,(branches j).positive=true) : (Indexing.lookup idx branches).positive=true := by
  have ha : (Indexing.advance idx).positive=true := by cases idx <;> rfl
  simp only [Indexing.lookup,Code.positive,scan_positive _ _ ha _ hb,Bool.and_self]

/-- Positive signs for every packet mode and selector dispatch branch. -/
theorem ownedPacket_positive (n b h K s : ℕ) : (ownedPacket n b h K s).positive=true := by
  have dp : (scatterPacket n b h K s).positive=true := by
    unfold scatterPacket dispatch
    apply lookup_positive
    intro k
    apply lookup_positive
    intro i
    simp only [ownerCode,Code.positive,mode_program_positive,Bool.and_self]
  simp only [ownedPacket,ownedPrefix,copySelectors,Code.positive,dp,mode_program_positive,
    show startPacket.positive=true by decide,show decodeOwner.positive=true by decide,Bool.and_self]

end Cube.Scatter

namespace Cube.TeamRows

open RoutingISA BorderVNP.Cube.Scatter
open private singleTail from OAI.Computability.BorderVNP.CubeISAOwnedFilter

private theorem positive_of_unsigned {c : Code} (hc : c.unsigned = true) : c.positive = true := by
  induction c <;> simp_all [Code.unsigned,Code.positive]

/-- Every event of the compiled group traversal, including the local binary
guesses in its packet and singleton rows, has positive sign. -/
theorem ownedGroups_positive (n b h K s : ℕ) : (ownedGroups n b h K s).positive=true := by
  have pf (k : ℕ) : (Owned.packetFilter k).positive=true := by
    induction k with
    | zero => rfl
    | succ k ih => change (true && ((Owned.packetFilter k).positive && true))=true; rw [ih]; rfl
  have sf (k : ℕ) : (singleTail k).positive=true := by
    induction k with
    | zero => rfl
    | succ k ih => change (true && (true && (singleTail k).positive))=true; rw [ih]; rfl
  have pc : (Owned.packetCandidate n).positive=true := by
    change (true && (Owned.packetFilter n).positive) = true
    rw [pf]; rfl
  have sc : (Owned.singleCandidate n).positive=true := by
    change (true && (true && (singleTail n).positive)) = true
    rw [sf]; rfl
  have lit (x : ℕ) : (Constants.literal (Constants.digits x)).positive=true :=
    positive_of_unsigned (Constants.literal_unsigned _).1
  have pa : (OwnedRowSetup.parameters n b h K s).positive=true := by
    simp only [OwnedRowSetup.parameters,Code.block,Code.positive,lit,Bool.and_self]
  have ph (x : ℕ) : (LocalRow.pushLiteral x).positive=true := by
    simp only [LocalRow.pushLiteral,Code.positive,lit,show (LocalRow.push 58).positive=true by decide,Bool.and_self]
  simp only [ownedGroups,startVertices,finishVertices,scan,body,select,strictRole,diagonalRole,
    OwnedStages.strictSide,OwnedStages.diagonalSide,OwnedStages.strictScatter,OwnedStages.packetStage,
    OwnedStages.doubleStage,OwnedStages.singleStage,OwnedRowSetup.packet,OwnedVertex.vertexRow,
    Owned.rowLoop,LocalRow.strictChecked,LocalRow.diagonalChecked,LocalRow.setup,LocalRow.prime,LocalRow.metadata,
    DeclaredRow.strict,SingleTally.oriented,SingleTally.row,Code.block,Code.positive,pc,sc,pa,
    ownedPacket_positive,ph,Bool.and_self,Bool.and_true,Bool.true_and]
  rfl

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
