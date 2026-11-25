import OAI.Hierarchy.DescentSeedSiteGeometry
import OAI.Hierarchy.DescentSeedTokenNumbers
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentTerminalEpochChart
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Input addresses of the packed original seed and its shared dictionary -/
namespace Hierarchy
open Catalyst DescentSeedRoot DescentInitialHost DescentTerminalEpochChart ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false

namespace DescentPackedSeed
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
local notation "V₀" => Fintype.card (Vertex X)
local notation "E₀" => Fintype.card (Cable X)
local notation "H" => Fintype.card (Old X)
def multiplicity (w s : ℕ) :=
  if 16*digitsNeeded s≤w then DescentSIMDLookup.lanes w (8*digitsNeeded s)*8
  else DescentSIMDLookup.lanes w (digitsNeeded s)

def rows (R s w : ℕ) := H*DescentSIMDLookup.chunks (R*8) (multiplicity w s)

def publicWords := 6+(V₀+E₀)*8
end DescentPackedSeed

namespace DescentTerminalEpochHeader
variable {A : Type}
def extent : List (Source A) → ℕ
  | [] => 0
  | a::ts => DescentDyadicSpan.span a.seats + extent ts
end DescentTerminalEpochHeader

namespace DescentTerminalPackedSeedFlags
variable {F A : Type} [Field F] {k p : ℕ} (X : Approximation F k p) (R s w : ℕ)
local notation "M" => DescentPackedSeed.multiplicity w s
local notation "d" => digitsNeeded s
local notation "N" => DescentPackedSeed.rows X R s w

def source : Bank := ⟨DescentPackedSeed.publicWords X,Nat.clog 2 N⟩
def start := (source X R s w).base+(source X R s w).size
def dictionary (ts : List (Source A)) : Bank := ⟨start X R s w+DescentTerminalEpochHeader.extent ts,d*M⟩
def endInput (ts : List (Source A)) := (dictionary X R s w ts).base+(dictionary X R s w ts).size
end DescentTerminalPackedSeedFlags

namespace DescentWideSeedFlags
variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (R s payload : ℕ)
abbrev source := DescentTerminalPackedSeedFlags.source X R s payload
abbrev dictionary := DescentTerminalPackedSeedFlags.dictionary X R s payload ([] : List (Source Unit))
abbrev endInput := DescentTerminalPackedSeedFlags.endInput X R s payload ([] : List (Source Unit))
end DescentWideSeedFlags

namespace DescentExterior
variable {F : Type} [Field F] {arity data : ℕ} (X : Approximation F arity data)
abbrev ExteriorCount := Fintype.card (Catalyst.Port data X.width)
end DescentExterior
end
end Hierarchy

end OAI
