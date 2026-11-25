import OAI.Hierarchy.DescentDatedSeedBounds
import OAI.Hierarchy.DescentTerminalPackedSeedFlags
import OAI.Hierarchy.DescentAtomSchedule
import OAI.Hierarchy.DescentPrivateHeaderCheap
import OAI.Hierarchy.ProtocolRAMSumScoresCheap

namespace OAI
/-! # The native original seed checksum, constructor and private-header clearance -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentSeedRoot DescentPackedSeed DescentInitialHost DescentColonies DescentSIMDLookup
open DescentTerminalEpochChart DescentCompiler Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
section
variable {F J A : Type} [Field F] [Fintype J] [DecidableEq J] {k p R d G H : ℕ}
    (X : Approximation F k p) (name : J≃Fin G) (digits : Fin R≃J×Block d)
    (host : Vertex X↪Fin H) (l : Layout) (w : ℕ)
local notation "checker" => DescentTerminalPackedSeedFlags.check X R l.seedWidth w ([] : List (Source A))
local notation "middle" => DescentDatedSeedStartup.program X name digits host l w

def program := (checker).seq middle

end

variable {F A : Type} [Field F] {S : AtomSchedule} {k cp p H w : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k) (publicWide : Fintype.card (Vertex X)≤H)
    (l : Layout) (header : ℕ)
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)

def publicProgram := (program (A:=A) X (Equiv.refl _) digits hs l w).seq (DescentPrivateHeader.clearHeader w header)

/-- The fixed program has allowed instructions on every public geometry. -/
theorem public_cheap : CheapCode (publicProgram (A:=A) X digits publicWide l header (w:=w)) := by
  intro P R K pc reg pub exit i
  exact cheap_seq (cheap_seq (PruneFlag.cheap _ _ _ _ _) (hardware X (Equiv.refl _) digits hs l w).1)
    (DescentPrivateHeader.initialize_cheap w header) pc reg pub exit i

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
