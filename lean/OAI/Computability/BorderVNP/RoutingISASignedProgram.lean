import OAI.Computability.BorderVNP.RoutingISASignedAssembly
import OAI.Computability.BorderVNP.CubeTeamOwnedGroups

/-! # The fixed signed team program of Sections 8 and 11 -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA
open private scan Indexing Indexing.lookup Indexing.advance ownerCode from OAI.Computability.BorderVNP.CubeScatterDispatch

private theorem mode_program_returns (xs : List Mode) : (program xs).withoutAccept = true := by
  have hc (a : Mode) : a.code.withoutAccept=true := by cases a <;> rfl
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [program,Code.withoutAccept,hc,ih,Bool.and_self]

private theorem scan_returns (key : Reg) (advance : Code) (ha : advance.withoutAccept=true)
    {k : ℕ} (branches : Fin k → Code) (hb : ∀ j,(branches j).withoutAccept=true) :
    (scan key advance branches).withoutAccept=true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [scan,Code.withoutAccept,hb,ha,ih (branches ∘ Fin.succ) (fun j ↦ hb j.succ),Bool.and_self]

private theorem lookup_returns (idx : Indexing) {k : ℕ} (branches : Fin k → Code)
    (hb : ∀ j,(branches j).withoutAccept=true) : (Indexing.lookup idx branches).withoutAccept=true := by
  have ha : (Indexing.advance idx).withoutAccept=true := by cases idx <;> rfl
  simp only [Indexing.lookup,Code.withoutAccept,scan_returns _ _ ha _ hb,Bool.and_self]

/-- Every compiled packet layout and the full selector dispatch return to the
enclosing group scan, including the final selector comparison. -/
theorem ownedPacket_returns (n b h K s : ℕ) : (ownedPacket n b h K s).withoutAccept=true := by
  have dp : (scatterPacket n b h K s).withoutAccept=true := by
    unfold scatterPacket dispatch
    apply lookup_returns
    intro k
    apply lookup_returns
    intro i
    simp only [ownerCode,Code.withoutAccept,mode_program_returns,Bool.and_self]
  simp only [ownedPacket,ownedPrefix,copySelectors,Code.withoutAccept,dp,mode_program_returns,
    show startPacket.withoutAccept=true by decide,show decodeOwner.withoutAccept=true by decide,Bool.and_self]

end Cube.Scatter

namespace Cube.TeamRows

open RoutingISA BorderVNP.Cube.Scatter
open private singleTail from OAI.Computability.BorderVNP.CubeISAOwnedFilter

/-- The complete two-sided traversal contains only returning or rejecting
instructions, regardless of the dimension and the fixed finite cube tables. -/
theorem ownedGroups_returns (n b h K s : ℕ) : (ownedGroups n b h K s).withoutAccept=true := by
  have pf (k : ℕ) : (Owned.packetFilter k).withoutAccept=true := by
    induction k with
    | zero => rfl
    | succ k ih => change (true && ((Owned.packetFilter k).withoutAccept && true))=true; rw [ih]; rfl
  have sf (k : ℕ) : (singleTail k).withoutAccept=true := by
    induction k with
    | zero => rfl
    | succ k ih => change (true && (true && (singleTail k).withoutAccept))=true; rw [ih]; rfl
  have pc : (Owned.packetCandidate n).withoutAccept=true := by
    change (true && (Owned.packetFilter n).withoutAccept) = true
    rw [pf]; rfl
  have sc : (Owned.singleCandidate n).withoutAccept=true := by
    change (true && (true && (singleTail n).withoutAccept)) = true
    rw [sf]; rfl
  have lit (x : ℕ) : (Constants.literal (Constants.digits x)).withoutAccept=true :=
    (Constants.literal_unsigned _).2
  have pa : (OwnedRowSetup.parameters n b h K s).withoutAccept=true := by
    simp only [OwnedRowSetup.parameters,Code.block,Code.withoutAccept,lit,Bool.and_self]
  have ph (x : ℕ) : (LocalRow.pushLiteral x).withoutAccept=true := by
    simp only [LocalRow.pushLiteral,Code.withoutAccept,lit,show (LocalRow.push 58).withoutAccept=true by decide,Bool.and_self]
  simp only [ownedGroups,startVertices,finishVertices,scan,body,select,strictRole,diagonalRole,
    OwnedStages.strictSide,OwnedStages.diagonalSide,OwnedStages.strictScatter,OwnedStages.packetStage,
    OwnedStages.doubleStage,OwnedStages.singleStage,OwnedRowSetup.packet,OwnedVertex.vertexRow,
    Owned.rowLoop,LocalRow.strictChecked,LocalRow.diagonalChecked,LocalRow.setup,LocalRow.prime,LocalRow.metadata,
    DeclaredRow.strict,SingleTally.oriented,SingleTally.row,Code.block,Code.withoutAccept,pc,sc,pa,
    ownedPacket_returns,ph,Bool.and_self,Bool.and_true,Bool.true_and]
  rfl

end Cube.TeamRows

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally

/-- One fixed native signed team program for the given finite cube identity.
All tables depending on the input length are initialized from the ordinary
literal and broadcast streams or computed by its linked word instructions. -/
noncomputable def signedProgram {n b h K s : ℕ} (id : TableEntry n b h K s → ℕ) : Code :=
  signedAssembly id (TeamRows.ownedGroups n b h K s)

/-- Acceptance by the actual fetched word program is equivalent to a
normal return of the complete signed evaluator on the exact choice tape. -/
theorem signedProgram_execute_iff {w n b h K s : ℕ} (id : TableEntry n b h K s → ℕ)
    {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {bank : Bank w} {m bits es} :
    TeamRAM.execute ((signedProgram id).program.fetch pub macros) ⟨0,bank⟩ m bits = some es ↔
      (∃ t mt, Runs pub macros (signedProgram id) bank m es t mt) ∧ es.map TeamRAM.Event.choices=bits :=
  signedAssembly_execute_iff id (TeamRows.ownedGroups_returns ..)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
