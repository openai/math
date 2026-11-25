import OAI.Hierarchy.DescentPublicMeterAny
import OAI.Hierarchy.DescentNamedMeterCode

namespace OAI
/-! # From the original per-date allocation to the public counter footprint -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Meter
open DescentSixParty DescentSixParty.Chronology DescentHostDegree DescentPackedPrivateSum
open DescentRawCablePanel DescentSIMDLookup Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q fee u : ℝ} {k i z D wire hist : ℕ}
variable {W : MarkedWorld F d P bits} {src : Reached W G q fee S k i z D wire hist}
variable {he : 0≤fee} {T : StageInput W G u fee} {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
variable {z' D' : ℕ} {dst : Reached n.result G q fee S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink src he T c n dst) (port : MeterPort src) (header : ℕ)

theorem ofTicket_room {w factor : ℕ} (safe : MeterPort.Fits ticket port header w factor) :
    (ofTicket (T:=T) port header).Room w := by
  obtain ⟨age,degree⟩:=ticket_shape ticket
  have digits : donorNameBits T.k T.Δ=donorNameBits k src.placement.degree := by rw [age,degree]
  let m:=ofTicket (T:=T) port header
  have width:=safe.packed.trans (Nat.div_le_div_right safe.word)
  have stop:=safe.room
  simp only [MeterPort.endAddr] at stop
  rw [digits] at stop width
  exact ⟨safe.before,Nat.mul_pos safe.positive (Nat.mul_pos (Nat.two_pow_pos _) src.placement.capPos),width,stop⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Meter

namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentHostDegree DescentRawCablePanel DescentSIMDLookup DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM DescentPackedZip DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε u : ℝ} {k i z D wire hist w : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he T c n target)
local notation "A" => prior.placement
local notation "H" => DescentCompiler.TerminalScale.hostRows (S.hostSize i)
local notation "J" => S.groupCount i
local notation "r" => 2^k
local notation "cm" => 2*(A).cap
local notation "K₀" => 2^(k+1)
local notation "dim" => (A).degree
local notation "short" => max (k+3) (Nat.clog 2 (dim+1))
local notation "profile" => DescentTerminalEpochBits.width G.C
local notation "fmt" => ticket.depotShape short
local notation "s" => shape r dim cm profile
local notation "amount" => ticket.installedDonorWidth short profile
variable (h base : ℕ)
local notation "M" => lanes h amount
local notation "rows" => H*chunks J M

open DescentPacking.PackedMatch.Local.Stage.Dated
theorem issued_counter_room (old : PriorBanks r dim (A).cap K₀) {header factor p : ℕ}
    (oldLow : header≤base) (live : 0<amount) (wide : 2*amount≤h) (size : h≤w)
    (ratio : w≤factor*h) (extent : ticket.wholeDonorEnd short profile H h base≤2^w)
    (grain : T.z=S.grainAt G.b p i) :
    let _visit:=ticket.issuedVisit h base old oldLow live wide size ratio extent grain
    let current:=ticket.donorDate.counter h base header
    current.Room w := by
  intro _visit current
  have id : Meter.ofTicket (T:=T) _visit.port header=current := by
    change Meter.mk _ _ _ _ _ _ _ _ T.z _ _ _ = Meter.mk _ _ _ _ _ _ _ _ (A).z _ _ _
    rw [ticket.quantum]
    rfl
  rw [←id]
  exact Meter.ofTicket_room ticket _visit.port header _visit.fits

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
