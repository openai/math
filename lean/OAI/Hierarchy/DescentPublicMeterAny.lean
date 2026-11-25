import OAI.Hierarchy.DescentDatedMeterCode
import OAI.Hierarchy.DescentPackedCounterFrame

namespace OAI
/-! # Public ordinary counter execution and memory frame before inspecting a ballot -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated
open DescentSixParty DescentSixParty.Chronology DescentHostDegree DescentPackedPrivateSum
open DescentRawCablePanel DescentSIMDLookup Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
namespace Meter
variable (b : Meter) {bw : ℕ}
local notation "units" => normBits b.cap b.radix b.ceiling b.padding
local notation "J" => b.groups*2^b.k*b.cap
local notation "names" => donorNameBits b.k b.degree
local notation "inputBits" => bundleBits 3 names units
local notation "short" => 2+units
local notation "full" => max inputBits (short*11)
local notation "M" => b.groupLanes*(2^b.k*b.cap)
local notation "law" => donorROM b.k (gainExponent 20 b.degree) (2^(packExponent 20 b.degree)+2) 3 names units
local notation "bank" => DescentPackedDonorSpace.banks b.base b.hosts J M inputBits
local notation "L₀" => DescentPackedDonorSpace.layout b.base b.hosts J M inputBits short
local notation "C₀" => DescentPackedDonorSpace.counters b.header b.base b.hosts J M inputBits short


def endAddr := DescentPackedDonorSpace.endAt b.base b.hosts J M inputBits short

def image (m : Memory bw) : Memory bw :=
  let pre:=DescentPackedDonorTables.image bank (L₀).rom.base b.hosts J M law score m
  let mid:=ProtocolRAM.image (L₀).source.base (b.hosts*chunks J M) (lookup bank) pre
  let out:=DescentPackedPrivateAccumulator.image L₀ C₀ b.hosts (J*11) (M*11) b.quantum mid
  DescentPrivateHeader.committed b.header (C₀).out out

structure Room (bw : ℕ) : Prop where
  before : b.header≤b.base
  positive : 0<M
  packed : M*full≤bw/2
  room : b.endAddr<2^bw

theorem counter_any (m : Memory bw) (fit : b.Room bw) :
    (b.program bw).Exec m (b.image m) b.ticks :=
  b.counter.counter_any law score m ⟨fit.before,fit.positive,fit.packed,fit.room⟩

theorem counter_frame (m : Memory bw) (fit : b.Room bw) (addr : ℕ) (apart : addr≠b.header)
    (away : addr≤b.base ∨ b.endAddr≤addr) : b.image m addr=m addr :=
  b.counter.counter_frame law score m ⟨fit.before,fit.positive,fit.packed,fit.room⟩ addr apart away

theorem counter_program (bw : ℕ) : b.program bw=b.counter.program law score bw :=rfl

end Meter
end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated

end OAI
