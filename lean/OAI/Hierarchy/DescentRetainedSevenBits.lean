import OAI.Hierarchy.DescentRetainedSevenVolume

namespace OAI
/-! # The bit cost of the seven original fields across the old and new host tables -/
namespace Hierarchy.DescentRetainedSeven.Chart
open DescentPlacedInvoiceVolume DescentResetRetainedSetup DescentSIMDLookup DescentPackedWalsh ProtocolRAM
open DescentStaticWordColumn (names)
noncomputable section
variable (c : DescentRetainedSeven.Chart)
local notation "L" => c.retained
local notation "P" => c.placement

def rowBits (h oldUnit decoder packetUnit successor : ℕ) :=
  let H:=(L).hosts
  let G:=(L).groups
  let H':=(P).newHosts
  let G':=(P).groups
  (Layout.halfLiteral h+1)*h + 6*(H*h)+H*G*(oldUnit+5*(16*decoder))+
    (H*(P).blocks*h+H*G*packetUnit)+(H*h+H*G*(16*decoder))+(H*h+H*G*(16*decoder))+
    (H*h+H*G'*successor)+H*h+(H'*h+H'*G'*successor)+(h+1)^3*2^(h/2)*h+h

/-- All full rows are paid for once at their actual incoming or outgoing precision.
Each short last row costs one bus-width per host. -/
theorem packed_bits {cut k h u oldUnit packetUnit successor : ℕ} (g : (L).CalendarPitch cut k h u)
    (groups : (L).groups=2^cut) (host : 0<(L).hosts) (uPos : 0<u) (old : 0<(L).previousLanes)
    (earlier : (L).groups≤(L).previousLanes ∨ h≤(L).previousLanes*oldUnit)
    (same : (P).oldHosts=(L).hosts) (split : (P).groups*(P).blocks=(L).groups)
    (pkt : 0<c.packetLanes) (packet : (L).groups≤c.packetLanes*(P).blocks ∨ h≤c.packetLanes*packetUnit)
    (blocks : 0<(P).blocks) (next : 0<(P).lanes) (nextRoom : (P).groups≤(P).lanes ∨ h≤(P).lanes*successor) :
    (c.packedMass h+1)*h≤c.rowBits h oldUnit u packetUnit successor:=by
  have move:=g.movement_rows groups host uPos old earlier
  simp only [Nat.add_mul, Nat.one_mul] at move
  have geq : (L).grouped=(L).groups:=by rw [Layout.grouped,g.cut,groups]
  have dPos : 0<(L).decodedLanes:=by rw [g.decoded,g.gather];exact Nat.two_pow_pos _
  have dec : (L).groups≤(L).decodedLanes ∨ h≤(L).decodedLanes*(16*u):=by
    obtain full | dense := DescentWalshDyadicBudget.laneBits_median cut h u uPos
    · left;rw [groups,g.decoded,g.gather,full]
    · right;simpa only [g.decoded,g.gather,Nat.mul_comm (16*u)] using dense
  have source : Overlap.rows (L).hosts (L).groups c.packetLanes*h≤
      (L).hosts*(P).blocks*h+(L).hosts*(L).groups*packetUnit :=by
    obtain few | full:=packet
    · have parts : chunks (L).groups c.packetLanes≤(P).blocks:=by
        change ((L).groups+c.packetLanes-1)/c.packetLanes≤(P).blocks
        apply Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul pkt).2 ?_)
        rw [Nat.succ_mul,Nat.mul_comm (P).blocks c.packetLanes];omega
      exact (Nat.mul_le_mul_right h (Nat.mul_le_mul_left (L).hosts parts)).trans (Nat.le_add_right ..)
    · have linear:=Layout.bounded_pitch_rows (H:=(L).hosts) (G:=(L).groups) pkt (.inr full)
      have copies:=(Nat.mul_le_mul_right h (Nat.le_mul_of_pos_right (L).hosts blocks))
      exact linear.trans (Nat.add_le_add_right copies _)
  have decoder:=Layout.bounded_pitch_rows (H:=(L).hosts) dPos dec
  have remixed:=Layout.bounded_pitch_rows (H:=(L).hosts) next nextRoom
  have issued:=Layout.bounded_pitch_rows (H:=(P).newHosts) next nextRoom
  simp only [Overlap.rows] at source decoder remixed issued
  simp only [packedMass,control,batch,DescentResetRetainedPlacement.Chart.rows,
    DescentResetRetainedPlacement.Chart.parts,same,split,geq,Nat.add_mul,Nat.one_mul,rowBits]
  omega

/-- The actual complete program and all of its printed labels are charged at full word width. -/
theorem invoice_bits (floor w h U cut k u oldUnit packetUnit successor ratio : ℕ) (ap : c.Apertures h)
    (g : (L).CalendarPitch cut k h u) (groups : (L).groups=2^cut) (host : 0<(L).hosts) (uPos : 0<u)
    (prior : 0<(L).previousLanes) (earlier : (L).groups≤(L).previousLanes ∨ h≤(L).previousLanes*oldUnit)
    (same : (P).oldHosts=(L).hosts) (split : (P).groups*(P).blocks=(L).groups)
    (packetRoom : (L).groups≤c.packetLanes*(P).blocks ∨ h≤c.packetLanes*packetUnit)
    (nextRoom : (P).groups≤(P).lanes ∨ h≤(P).lanes*successor) (word : w≤ratio*h) :
    c.invoice floor w U*w≤
      (c.units U*ratio)*c.rowBits h oldUnit u packetUnit successor:=by
  calc
    _ ≤ (c.units U*(c.packedMass h+1))*(ratio*h):=
      Nat.mul_le_mul (c.invoice_volume floor w h U ap) word
    _ = (c.units U*ratio)*((c.packedMass h+1)*h):=by ring
    _ ≤ _:=Nat.mul_le_mul_left _ (c.packed_bits g groups host uPos prior earlier same split ap.packet packetRoom ap.blocks ap.after_ nextRoom)


theorem native_bits (floor w h U cut k u oldUnit packetUnit successor ratio : ℕ) (which : c.control.Targets)
    (keep : Fin c.placement.shapes→Bool) (old : Fin (L).sources→Bank) (saved : Bank) (packet : Expr)
    (cnt inv : Bank) (work : packet.work≤U) (ap : c.Apertures h)
    (g : (L).CalendarPitch cut k h u) (groups : (L).groups=2^cut) (host : 0<(L).hosts) (uPos : 0<u)
    (prior : 0<(L).previousLanes) (earlier : (L).groups≤(L).previousLanes ∨ h≤(L).previousLanes*oldUnit)
    (same : (P).oldHosts=(L).hosts) (split : (P).groups*(P).blocks=(L).groups)
    (packetRoom : (L).groups≤c.packetLanes*(P).blocks ∨ h≤c.packetLanes*packetUnit)
    (nextRoom : (P).groups≤(P).lanes ∨ h≤(P).lanes*successor) (word : w≤ratio*h) :
    (c.ticks floor w which old saved packet cnt inv+7*names (c.program floor w which keep old saved packet cnt inv))*w≤
      (c.units U*ratio)*c.rowBits h oldUnit u packetUnit successor:=by
  have geom:=g.geometry
  have gp : 0<(L).gatherLanes:=g.gather ▸ Nat.two_pow_pos _
  have mp : 0<(L).matrixLanes:=geom.2.2.2.1 ▸ gp
  calc
    _ ≤ (c.units U*(c.packedMass h+1))*(ratio*h):=
      Nat.mul_le_mul (c.native_volume floor w h U which keep old saved packet cnt inv work ap prior gp mp) word
    _ = (c.units U*ratio)*((c.packedMass h+1)*h):=by ring
    _ ≤ _:=Nat.mul_le_mul_left _ (c.packed_bits g groups host uPos prior earlier same split ap.packet packetRoom ap.blocks ap.after_ nextRoom)

end
end Hierarchy.DescentRetainedSeven.Chart

end OAI
