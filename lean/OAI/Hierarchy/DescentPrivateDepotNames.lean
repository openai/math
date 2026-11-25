import OAI.Hierarchy.DescentPrivateDepotPort

namespace OAI
/-! # Names of the actual recursive meter and its two installed literal tables -/
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
local notation "full" => max inputBits (short*11)
local notation "M" => b.groupsPerWord*(2^k*(A).cap)
local notation "law" => donorROM T.k (gainExponent 20 T.Δ) (2^(packExponent 20 T.Δ)+2) 3 names units
local notation "bank" => DescentPackedDonorSpace.banks b.base b.hosts J M inputBits
local notation "L₀" => DescentPackedDonorSpace.layout b.base b.hosts J M inputBits short
local notation "C₀" => DescentPackedDonorSpace.counters a b.base b.hosts J M inputBits short


theorem names_at (K : ℕ) (fit : Fits ticket b a bw K) :
    DescentStaticWordColumn.names (program ticket b a bw) ≤
      398+8*ProtocolRAMPortScale.bitWidth T.z+60*(b.hosts*chunks (S.groupCount i) b.groupsPerWord)+30*2^(b.payload/2) := by
  have roles:0<2^k*(A).cap:=Nat.mul_pos (Nat.two_pow_pos _) (A).capPos
  have live:0<M:=Nat.mul_pos fit.positive roles
  have cap:=DescentPackedDonorTables.arena_size b.base b.hosts J M inputBits short live
  obtain ⟨inputFit,outputFit⟩:=DescentPackedDonorTables.grouped_pages fit.packed
  have batches : chunks J M=chunks (S.groupCount i) b.groupsPerWord := by
    rw [Nat.mul_assoc]
    exact chunks_group _ _ _ fit.positive roles
  rw [batches] at cap
  apply (names_le ticket b a bw).trans
  dsimp only [hardware]
  omega

end MeterPort
namespace OrdinaryLink
variable (shortDigit : ℕ)
local notation "A" => source.placement
local notation "units" => normBits (A).cap G.b G.C G.k
local notation "names" => donorNameBits T.k T.Δ
local notation "inputBits" => bundleBits 3 names units
local notation "short" => 2+units
local notation "full" => max inputBits (short*11)
local notation "roles" => 2^k*(A).cap

variable (H : ℕ) (padded : Fintype.card source.V≤H) (base payload : ℕ)

local notation "unit" => depotWidth ticket shortDigit
local notation "groupLanes" => lanes payload unit
local notation "b" => depotPort ticket shortDigit H padded base payload


/-- Actual CPU name bits at the lane count selected for all six input banks.
The padded contiguous literal installer is charged for each word it writes. -/
theorem sizedDepot_names (amount : ℕ) (covers : unit≤amount) {header bw K : ℕ}
    (wide : 2*amount≤payload)
    (fit : MeterPort.Fits ticket (sizedDepotPort H padded base payload amount) header bw K) :
    DescentStaticWordColumn.names (MeterPort.program ticket (sizedDepotPort H padded base payload amount) header bw)*bw ≤
      K*((398+8*ProtocolRAMPortScale.bitWidth T.z+30*2^(payload/2))*payload+
        60*(H*payload+4*H*S.groupCount i*amount)) := by
  let port:=sizedDepotPort H padded base payload amount
  have width : 0<full:=lt_of_lt_of_le (by positivity : 0<short*11) (Nat.le_max_right ..)
  have size : 0<amount:=(Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (A).capPos) width).trans_le
    ((Nat.le_max_right ..).trans covers)
  have nameBound:=MeterPort.names_at ticket port header K fit
  change DescentStaticWordColumn.names (MeterPort.program ticket port header bw) ≤
    398+8*ProtocolRAMPortScale.bitWidth T.z+60*(H*chunks (S.groupCount i) (lanes payload amount))+30*2^(payload/2) at nameBound
  have front:=Nat.mul_le_mul nameBound fit.overhead
  have rows:=Nat.mul_le_mul_left (K*60) (volume H (S.groupCount i) payload amount size wide)
  apply front.trans
  change (398+8*ProtocolRAMPortScale.bitWidth T.z+60*(H*chunks (S.groupCount i) (lanes payload amount))+
    30*2^(payload/2))*(K*payload) ≤ _
  nlinarith only [rows]

end OrdinaryLink
end
end Hierarchy.DescentSixParty.Chronology

end OAI
