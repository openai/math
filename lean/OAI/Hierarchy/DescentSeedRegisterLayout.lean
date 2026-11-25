import OAI.Hierarchy.DescentSeedSiteGeometry
import OAI.Hierarchy.DescentSeedSignedBroadcast
import OAI.Hierarchy.DescentSeedInitialTable
import OAI.Hierarchy.DescentDatedSeedLayout
import OAI.Hierarchy.DescentDatedOperandHeader

namespace OAI
/-! Public row counts and physical addresses of the initial signed, operand and directory banks. -/
namespace Hierarchy
open DescentSeedRoot DescentSIMDLookup DescentPackedColony DescentDyadicSpan Catalyst ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)

namespace DescentPackedSeed.Signed
abbrev size := Fintype.card (Vertex X)*(3*2)
end DescentPackedSeed.Signed

namespace DescentPackedSeed.CopyOrdinal
def words (k G M : ℕ) := 2^k*chunks G M
end DescentPackedSeed.CopyOrdinal

namespace DescentOperandStateBanks.Seed
abbrev count := Fintype.card (Vertex X)*3
end DescentOperandStateBanks.Seed

namespace DescentOperandStateBanks.Seed
open DescentPackedSeed
def stampStart (base : ℕ) := base+Signed.size X+count X
end DescentOperandStateBanks.Seed

namespace DescentOperandStateBanks.Seed.Columns
open DescentPackedSeed
def maskBase (copy d G M : ℕ) :=copy+span (CopyOrdinal.words d G M)
def first (copy d G M : ℕ) :=maskBase copy d G M+span (CopyOrdinal.words d G M)
end DescentOperandStateBanks.Seed.Columns

namespace DescentOperandStateBanks.Seed.Physical
open DescentOperandStateBanks.Seed.Columns
def bankStart (base d G M : ℕ) :=first (stampStart X base) d G M
def endAddress (base slots d H G M : ℕ) :=
  bankStart X base d G M+(7*slots)*(2^d*(H*chunks G M))+2^Nat.clog 2 (H*chunks G M+1)
end DescentOperandStateBanks.Seed.Physical

namespace DescentPackedSeed.Signed.Plane
local notation "C" => Fintype.card (Vertex X)*(2*3)+1
local notation "sockets" => 2*256
def output (base H groups M : ℕ) := base+DescentSeedSignedBroadcast.size C (sockets*H) groups M
def page (base H groups M : ℕ) (s : Fin sockets) : Bank :=
  ⟨output X base H groups M+s.val*(H*chunks groups M),Nat.clog 2 (H*chunks groups M)⟩
def endAddress (base H groups M : ℕ) :=output X base H groups M+(sockets*H)*chunks groups M
end DescentPackedSeed.Signed.Plane

namespace DescentDatedSeedStartup
open DescentPackedSeed DescentOperandStateBanks
variable (l : Layout)
local notation "M" => l.packedLanes
local notation "N" => l.groupsPerNode
def operandBase (H G : ℕ) := Signed.Plane.endAddress X l.base H G M
def directoryBase (H G d : ℕ) :=
  Seed.Physical.endAddress X (operandBase X l H G) (3*N) d H G l.operandLanes
def endAddress (H G d : ℕ) := DescentSeedInitialTable.endAddress (directoryBase X l H G d) H G M 3
end DescentDatedSeedStartup

namespace DescentDatedSeedStartup
open DescentPackedSeed DescentPacking.PackedMatch.Local.Stage
variable (l : Layout)
local notation "M" => l.packedLanes
def operands (d H G : ℕ) : Dated.Operands :=
  let directoryBank:=DescentSeedInitialTable.bank (directoryBase X l H G d) H G l.packedLanes 3
  { roster:=directoryBank 0
    ids i:=directoryBank (8+i)
    offsets:=directoryBank 1
    chunks:=directoryBank 2
    actors:=directoryBank 3
    wire _ j:=Signed.Plane.page X l.base H G M ⟨j%512,Nat.mod_lt _ (by decide)⟩
    hubs:=directoryBank 4
    atoms _:=.lookup (directoryBank 5) .row }
end DescentDatedSeedStartup

end
end Hierarchy

end OAI
