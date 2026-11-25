import OAI.Hierarchy.DescentPrivateNativeDate
import OAI.Hierarchy.DescentPackedCounterFrame

namespace OAI
/-! # Fixed running time of the path charge opcode on arbitrary data -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentHostDegree DescentPackedPrivateSum DescentRawCablePanel DescentSIMDLookup
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink source he T c n target)

namespace MeterPort
variable (b : MeterPort source) (a : ℕ)

local notation "A" => source.placement
local notation "units" => normBits (A).cap G.b G.C G.k
local notation "J" => S.groupCount i*2^k*(A).cap
local notation "names" => donorNameBits T.k T.Δ
local notation "inputBits" => bundleBits 3 names units
local notation "short" => 2+units
local notation "M" => b.groupsPerWord*(2^k*(A).cap)
local notation "law" => donorROM T.k (gainExponent 20 T.Δ) (2^(packExponent 20 T.Δ)+2) 3 names units
/-- Packed counter for the donor rows of this ordinary date. -/
def packedCounter : DescentPackedCounter.Counter :=
  let _ := ticket
  ⟨b.hosts, J, M, inputBits, short, T.z, b.base, a⟩

theorem packedCounter_room {K : ℕ} (fit : Fits ticket b a bw K) :
    (packedCounter ticket b a).Room bw :=
  ⟨fit.before, Nat.mul_pos fit.positive (Nat.mul_pos (Nat.two_pow_pos _) (A).capPos),
    fit.packed.trans (Nat.div_le_div_right fit.word), fit.room⟩

/-- All loops and lookups follow allocated numeric bounds for every input word. -/
theorem any (K : ℕ) (m : Memory bw) (fit : Fits ticket b a bw K) :
    (program ticket b a bw).Exec m (image ticket b a m) (ticks ticket b a) :=
  (packedCounter ticket b a).counter_any law score m (packedCounter_room ticket b a fit)

end MeterPort
end
end Hierarchy.DescentSixParty.Chronology

end OAI
