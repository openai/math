import OAI.Hierarchy.DescentDonorPublicCounts
import OAI.Hierarchy.DescentNativeDonorROM
import OAI.Hierarchy.DescentPackedCounterFrame
import OAI.Hierarchy.ProtocolRAMPortScale

namespace OAI
/-! # The unconditional public machine for the native private counter -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated
open DescentSixParty DescentSixParty.Chronology DescentHostDegree DescentPackedPrivateSum
open DescentRawCablePanel DescentSIMDLookup Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
/-- Only public word widths, the number of lane groups per input word and the
two persistent bank addresses enter the literal instruction table. -/
structure Meter where
  hosts : ℕ
  groups : ℕ
  k : ℕ
  degree : ℕ
  cap : ℕ
  radix : ℕ
  ceiling : ℕ
  padding : ℕ
  quantum : ℕ
  groupLanes : ℕ
  base : ℕ
  header : ℕ
  deriving DecidableEq

namespace Meter
variable (b : Meter)
local notation "units" => normBits b.cap b.radix b.ceiling b.padding
local notation "donors" => b.groups*2^b.k*b.cap
local notation "digits" => donorNameBits b.k b.degree
local notation "field" => bundleBits 3 digits units
local notation "short" => 2+units
local notation "M" => b.groupLanes*(2^b.k*b.cap)
local notation "law" => donorROM b.k (gainExponent 20 b.degree) (2^(packExponent 20 b.degree)+2) 3 digits units
local notation "bank" => DescentPackedDonorSpace.banks b.base b.hosts donors M field
local notation "ports" => DescentPackedDonorSpace.layout b.base b.hosts donors M field short
local notation "read" => DescentPackedDonorSpace.counters b.header b.base b.hosts donors M field short

def counter : DescentPackedCounter.Counter :=
  ⟨b.hosts,donors,M,field,short,b.quantum,b.base,b.header⟩

def program (w : ℕ) : Procedure w := b.counter.program law score w

theorem counter_cheap (w : ℕ) : ProtocolRAM.CheapCode (b.program w) :=
  @DescentPackedCounter.Counter.counter_cheap b.counter law score w

def ticks := ((4+10*DescentPackedDonorTables.size bank (ports).rom.base short M)+
  ((4+44*(b.hosts*chunks donors M))+(Layout.billed b.hosts (donors*11) (M*11)+(read).scaling.steps b.quantum)))+11

def hardware := 15*(DescentPackedDonorTables.size bank (ports).rom.base short M+1)+308+
  8*ProtocolRAMPortScale.bitWidth b.quantum

end Meter
end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated

end OAI
