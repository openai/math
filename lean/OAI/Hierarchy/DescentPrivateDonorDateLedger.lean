import OAI.Hierarchy.DescentPrivateDonorBillNumbers
import OAI.Hierarchy.DescentPrivateDepotNames
import OAI.Hierarchy.DescentPrivateDepotClock

namespace OAI
/-! # Charging the literal six-field donor and both recursive meter tables on the same date -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentHostDegree DescentPackedPrivateSum DescentRawCablePanel DescentSIMDLookup
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink source he T c n target)

namespace OrdinaryLink
open DescentCompiler.TerminalScale DescentStaticWordColumn

variable (shortDigit H : ℕ) (padded : Fintype.card source.V≤H) (base h amount header K : ℕ)
variable (tables : DepotRAM.Tables6) («fields» : DepotRAM.Fields) (banks : DescentSIMDLookup.Banks) (dest : ℕ)
local notation "port" => sizedDepotPort H padded base h amount
local notation "batch" => lanes h amount
local notation "groups" => S.groupCount i
local notation "cnt" => DepotRAM.fieldWork «fields»

/-- All physical work and all literal names for both native procedures, including the
header commit. The estimate is unconditional on the contents of the old word store. -/
def donorDateBill (bw : ℕ) :=
  DepotRAM.clocks tables «fields» H groups batch*bw+
  names (DepotRAM.program tables «fields» banks dest H groups batch bw)*bw+
  MeterPort.price ticket port bw K+names (MeterPort.program ticket port header bw)*bw

theorem donor_date_bill (bw : ℕ) (covers : depotWidth ticket shortDigit≤amount)
    (room : 2*amount≤h) (fit : MeterPort.Fits ticket port header bw K)
    (positive : 0<amount) (hosts : 0<H) (radix : 0<S.radix)
    (grain : ProtocolRAMPortScale.bitWidth T.z≤H) (pages : 2^(h/2)≤H) :
    donorDateBill ticket H padded base h amount header K tables «fields» banks dest bw ≤
      H*h*(K*(1274+6*cnt))+H*(groups*S.radix)*(K*(4*amount*(342+2*cnt))) := by
  unfold donorDateBill
  apply donor_row_bill hosts radix fit.overhead grain pages
  · exact DepotRAM.clock_cost tables «fields» H groups h amount bw K positive room fit.overhead
  · rw [DepotRAM.controller]
  · exact sizedDepot_price ticket shortDigit H padded base h amount covers bw K room
  · exact sizedDepot_names ticket shortDigit H padded base h amount covers room fit

end OrdinaryLink
end
end Hierarchy.DescentSixParty.Chronology

end OAI
