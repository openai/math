import OAI.Hierarchy.DescentPrivateNativeDate
import OAI.Hierarchy.DescentDonorWindow

namespace OAI
/-! # The meter consumes exactly one upstream packed donor window per host and group batch -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentRawCablePanel.DepotRAM DescentHostDegree DescentPackedPrivateSum DescentRawCablePanel DescentSIMDLookup
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


namespace OrdinaryLink
variable (shortDigit : ℕ)
local notation "A" => source.placement
local notation "units" => normBits (A).cap G.b G.C G.k
local notation "names" => donorNameBits T.k T.Δ
local notation "inputBits" => bundleBits 3 names units
local notation "short" => 2+units
local notation "full" => max inputBits (short*11)
local notation "roles" => 2^k*(A).cap

def depotShape : DepotRAM.Shape :=
  let _ := ticket
  ⟨2^k,(A).degree,(A).cap,shortDigit,names,units⟩

def depotWidth := max (DepotRAM.totalBits (depotShape ticket shortDigit)) (roles*full)

variable (H : ℕ) (padded : Fintype.card source.V≤H) (base payload : ℕ)

def depotPort : MeterPort source :=
  ⟨H,padded,base,payload,lanes payload (depotWidth ticket shortDigit)⟩

local notation "unit" => depotWidth ticket shortDigit
local notation "groupLanes" => lanes payload unit
local notation "b" => depotPort ticket shortDigit H padded base payload

/-- The gather may reserve more bits per logical group to accommodate all input ROMs. -/
def sizedDepotPort (amount : ℕ) : MeterPort source :=
  ⟨H,padded,base,payload,lanes payload amount⟩

/-- One public register geometry simultaneously fits the complete local gather
and the eleven subroles of every old donor. -/
theorem sizedDepot_fit (amount : ℕ) (covers : unit≤amount) {header bw K : ℕ} (before : header≤base) (wide : 2*amount≤payload)
    (word : payload≤bw) (ratio : bw≤K*payload)
    (space : base+8*(H*chunks (S.groupCount i) (lanes payload amount))+2*2^(payload/2)+11<2^bw) :
    MeterPort.Fits ticket (sizedDepotPort H padded base payload amount) header bw K := by
  have rolesPos : 0<roles:=Nat.mul_pos (Nat.two_pow_pos _) (A).capPos
  have widths : 0<full:=lt_of_lt_of_le (by positivity : 0<short*11) (Nat.le_max_right ..)
  have positive : 0<amount:=(Nat.mul_pos rolesPos widths).trans_le ((Nat.le_max_right ..).trans covers)
  have groups:0<(lanes payload amount):=(occupancy payload amount positive wide).1
  have packed : ((lanes payload amount)*roles)*full≤payload/2 := by
    rw [Nat.mul_assoc]
    exact (Nat.mul_le_mul_left (lanes payload amount) ((Nat.le_max_right ..).trans covers)).trans (lanes_fit payload amount)
  refine ⟨before,groups,packed,word,ratio,?_⟩
  have extent:=DescentPackedDonorSpace.footprint base H (S.groupCount i*2^k*(A).cap)
    ((lanes payload amount)*roles) inputBits short (Nat.mul_pos groups rolesPos)
  have batches : chunks (S.groupCount i*2^k*(A).cap) ((lanes payload amount)*roles)=chunks (S.groupCount i) (lanes payload amount) := by
    rw [Nat.mul_assoc]
    exact chunks_group _ _ _ groups rolesPos
  obtain ⟨front,back⟩:=DescentPackedDonorTables.grouped_pages packed
  rw [batches] at extent
  exact lt_of_le_of_lt (le_trans extent (by omega)) space

theorem sizedDepot_price (amount : ℕ) (covers : unit≤amount) (bw K : ℕ) (wide : 2*amount≤payload) :
    MeterPort.price ticket (sizedDepotPort H padded base payload amount) bw K ≤
      K*((131+4*ProtocolRAMPortScale.bitWidth T.z)*payload+
        124*(H*payload+4*H*S.groupCount i*amount)+20*2^(payload/2)*payload)+11*bw := by
  have rolesPos : 0<roles:=Nat.mul_pos (Nat.two_pow_pos _) (A).capPos
  have widths : 0<full:=lt_of_lt_of_le (by positivity : 0<short*11) (Nat.le_max_right ..)
  have positive : 0<amount:=(Nat.mul_pos rolesPos widths).trans_le ((Nat.le_max_right ..).trans covers)
  have bill:=volume H (S.groupCount i) payload amount positive wide
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  change (131+4*ProtocolRAMPortScale.bitWidth T.z+124*(H*chunks (S.groupCount i) (lanes payload amount))+
    20*2^(payload/2))*payload≤_
  nlinarith only [Nat.mul_le_mul_left 124 bill]

/-- One public register geometry simultaneously fits the complete local gather
and the eleven subroles of every old donor. -/
theorem depot_fit {header bw K : ℕ} (before : header≤base) (wide : 2*unit≤payload)
    (word : payload≤bw) (ratio : bw≤K*payload)
    (space : base+8*(H*chunks (S.groupCount i) groupLanes)+2*2^(payload/2)+11<2^bw) :
    MeterPort.Fits ticket b header bw K :=
  sizedDepot_fit ticket shortDigit H padded base payload unit le_rfl before wide word ratio space

theorem depot_price (bw K : ℕ) (wide : 2*unit≤payload) :
    MeterPort.price ticket b bw K ≤
      K*((131+4*ProtocolRAMPortScale.bitWidth T.z)*payload+
        124*(H*payload+4*H*S.groupCount i*unit)+20*2^(payload/2)*payload)+11*bw :=
  sizedDepot_price ticket shortDigit H padded base payload unit le_rfl bw K wide

end OrdinaryLink
end
end Hierarchy.DescentSixParty.Chronology

end OAI
