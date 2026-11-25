import OAI.Hierarchy.DescentOrdinaryVenueClip
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Address range of the pitch-clipped ordinary receiver -/
namespace Hierarchy.DescentOrdinaryVenueIngress.Clip
open DescentSIMDLookup DescentRawCablePanel DescentPackedColony DescentSharedCableNames
open DescentHaloWalkRAM DescentScalarVenueMask DescentDyadicSpan ProtocolRAM
noncomputable section

private theorem retile_end (base H G A M bits h : ℕ) (shrink : M≤A)
    (width : (bits+1)*A≤h/2) :
    Overlap.endAddress base H G A M bits ≤ base+8*Overlap.rows H G M+12+2*2^(h/2) := by
  have pieces : Overlap.pieces G A M≤2 := by
    apply (Nat.min_le_right ..).trans
    have one : chunks M A<2 := by
      change (M+A-1)/A<2
      by_cases pos : 0 < A
      · apply (Nat.div_lt_iff_lt_mul pos).2
        omega
      · have empty : A=0 := by omega
        simp [empty]
    omega
  have addressBits : Overlap.keyBits bits A≤h/2 := by
    have ix : Nat.clog 2 (A+1)≤A := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self : A+1≤2^A)
    unfold Overlap.keyBits
    rw [Nat.add_mul,Nat.one_mul] at width
    omega
  have keys : 2^Overlap.keyBits bits A≤2^(h/2) := Nat.pow_le_pow_right (by decide) addressBits
  have rounded : 2^Overlap.mapBits H G M ≤ 2*(Overlap.rows H G M+1)+1 := span_le _
  have d := Nat.mul_le_mul (Nat.add_le_add_right pieces 1) rounded
  have k := Nat.mul_le_mul pieces keys
  unfold Overlap.endAddress Overlap.dest Overlap.dictBase
  omega

variable (c : Clip)
local notation "H₀" => c.venue.hosts
local notation "G₀" => c.venue.groups
local notation "P₀" => c.venue.paths
local notation "D₀" => c.venue.socket.degree
local notation "M₀" => c.working
local notation "N₀" => c.core.rows
local notation "C₀" => DepotRAM.ActorInputs.count c.venue.socket
local notation "A₀" => c.actorCount
local notation "E₀" => 2^(c.payload/2)

/-- Each retile reserves its destination directory, dictionaries and rounded
output bank, including both extra map pages of the physical layout. -/
theorem setup_extent_any (base : ℕ)
    (panelWidth : (c.peerBits+1)*c.panelPitch≤c.payload/2)
    (actorWidth : (c.actorBits+1)*c.actorPitch≤c.payload/2) :
    c.setupStart base ≤ base+16*N₀+24+4*E₀ := by
  have p := retile_end base H₀ G₀ c.panelPitch M₀ c.peerBits c.payload c.working_fields.1 panelWidth
  have a := retile_end (c.actorStart base) H₀ G₀ c.actorPitch M₀ c.actorBits c.payload c.working_fields.2.1 actorWidth
  change c.actorStart base≤base+8*N₀+12+2*E₀ at p
  change c.setupStart base≤c.actorStart base+8*N₀+12+2*E₀ at a
  omega

private theorem actor_extent (base : ℕ) :
    DepotRAM.ActorInputs.roof c.venue.socket H₀ G₀ M₀ base ≤
      base+2*E₀+4*N₀+6+2*C₀*(E₀+2*N₀+1)+2*C₀*N₀ := by
  let s:=c.venue.socket
  let e:=2^(DepotRAM.ActorInputs.bits s*M₀)
  have bits : DepotRAM.ActorInputs.bits s≤c.unit :=
    (le_max_left ..).trans ((le_max_right ..).trans (le_max_left ..))
  have fit : DepotRAM.ActorInputs.bits s*M₀≤c.payload/4 := by
    rw [Nat.mul_comm]; exact (Nat.mul_le_mul_left M₀ bits).trans c.working_fields.2.2
  have power : e≤E₀ := Nat.pow_le_pow_right (by decide) (fit.trans (by omega))
  have round := span_le N₀
  have round' := span_le (N₀+1)
  have copies := Nat.mul_le_mul_left C₀ (Nat.add_le_add power round)
  change base+2*e+DescentDyadicSpan.span (N₀+1)+C₀*(e+DescentDyadicSpan.span N₀)+C₀*N₀+C₀*(e+DescentDyadicSpan.span N₀)+C₀*N₀+DescentDyadicSpan.span (N₀+1) ≤ _
  nlinarith only [power,round',copies]

private theorem halo_extent (base : ℕ) : DescentScalarHaloProgram.stop H₀ G₀ M₀ D₀ base ≤
    base+15*(H₀*P₀)+4*N₀+P₀*N₀+3*H₀+6 := by
  have r := span_le (H₀*P₀)
  have pad := span_le (max (H₀*P₀) (max N₀ H₀)+1)
  have mx : max (H₀*P₀) (max N₀ H₀)≤H₀*P₀+N₀+H₀ :=
    max_le (by omega) (max_le (by omega) (by omega))
  change base+(6*(H₀*P₀)+N₀)+DescentDyadicSpan.span (H₀*P₀)+(P₀*N₀+(H₀+(N₀+H₀*P₀)))+
    DescentDyadicSpan.span (max (H₀*P₀) (max N₀ H₀)+1)+DescentDyadicSpan.span (H₀*P₀)+DescentDyadicSpan.span (H₀*P₀) ≤ _
  omega

private theorem receiver_extent (base : ℕ) :
    Raster.output P₀ c.venue.socket.blocks c.venue.socket.cap c.venue.raw c.venue.names H₀ G₀ M₀ base+DescentDyadicSpan.span N₀ ≤
      base+(7+2*A₀+2*P₀)*E₀+8*H₀+8*(H₀*P₀)+P₀*(H₀*P₀)+5*N₀+16 := by
  let v:=c.venue
  let Q:=DescentPackedChildNeighbor.SIMD.ROM.cells P₀ (Packed.bits P₀) 1 M₀ H₀ G₀
  let D:=DescentDyadicSpan.span (max H₀ (H₀*P₀)+1)
  let L:=Receiver.length v.raw v.names M₀ A₀
  have floorHalf : c.payload/4≤c.payload/2 := by omega
  have u : 2^(Receiver.unit v.raw v.names A₀*M₀)≤E₀ := Nat.pow_le_pow_right (by decide) (c.receiver_aperture.trans floorHalf)
  have len : L≤(2+A₀)*(2*E₀) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 u)
  have rd : D≤2*(H₀+H₀*P₀+1)+1 := (span_le _).trans (by
    have mx : max H₀ (H₀*P₀)≤H₀+H₀*P₀ := max_le (Nat.le_add_right ..) (Nat.le_add_left ..)
    omega)
  have bits : Packed.bits P₀+1≤c.localUnit :=
    (Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have pwidth := (Nat.le_succ (Packed.bits P₀)).trans (bits.trans (show c.localUnit≤c.unit from Nat.le_max_left ..))
  have two : 2≤c.unit := (show 2≤c.localUnit from Nat.le_max_left ..).trans (Nat.le_max_left ..)
  have busy : c.unit*M₀≤c.payload/2 := by rw [Nat.mul_comm]; exact c.working_fields.2.2.trans floorHalf
  have path : 2^(Packed.bits P₀*M₀)≤E₀ := Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul_right _ pwidth).trans busy)
  have twice : 2^(2*M₀)≤E₀ := Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul_right _ two).trans busy)
  have single : 2^M₀≤E₀ := (Nat.pow_le_pow_right (by decide : 0<2) (show M₀≤2*M₀ by omega)).trans twice
  have pages : Q≤(3+2*P₀)*E₀+N₀ := by
    simp only [Q,DescentPackedChildNeighbor.SIMD.ROM.cells, Nat.pow_succ, Nat.one_mul, show 1+1=2 by decide]
    change 2^(Packed.bits P₀*M₀)+(P₀*(2^(Packed.bits P₀*M₀)*2)+(2^M₀+(2^(2*M₀)+N₀))) ≤ _
    nlinarith only [path,twice,single,Nat.mul_le_mul_left P₀ (Nat.mul_le_mul_right 2 path)]
  have rounded:=span_le N₀
  have offset:=span_le (N₀+1)
  change base+L+3*D+P₀*(H₀*P₀)+D+Q+DescentDyadicSpan.span (N₀+1)+DescentDyadicSpan.span N₀≤_
  nlinarith only [len,rd,pages,rounded,offset]

/-- The public coefficient charges each pair of path indices for the dense
all-host header and each issued ticket column for its two physical copies. -/
def extentFactor := 64+24*P₀+P₀^2+6*C₀+2*A₀

def extentMass := 1+E₀+H₀+N₀+Overlap.rows H₀ G₀ c.panelPitch+Overlap.rows H₀ G₀ c.actorPitch

theorem fullEnd_le_any (base : ℕ)
    (panelWidth : (c.peerBits+1)*c.panelPitch≤c.payload/2)
    (actorWidth : (c.actorBits+1)*c.actorPitch≤c.payload/2) :
    c.fullEnd base ≤ base+c.extentFactor*c.extentMass := by
  let a:=c.setupStart base
  let b:=c.core.actorBase a
  let d:=c.core.haloBase a
  let r:=c.core.rasterBase a
  have input := c.setup_extent_any base panelWidth actorWidth
  have hub : b≤a+6*N₀+3 := by
    change a+3*DescentDyadicSpan.span N₀≤_; have bound:=span_le N₀; omega
  have act := c.actor_extent b
  change d≤b+2*E₀+4*N₀+6+2*C₀*(E₀+2*N₀+1)+2*C₀*N₀ at act
  have halo := c.halo_extent d
  change r≤d+15*(H₀*P₀)+4*N₀+P₀*N₀+3*H₀+6 at halo
  have recv := c.receiver_extent r
  change c.fullEnd base≤r+(7+2*A₀+2*P₀)*E₀+8*H₀+8*(H₀*P₀)+P₀*(H₀*P₀)+5*N₀+16 at recv
  change a≤base+16*N₀+24+4*E₀ at input
  calc
    _ ≤ base+16*N₀+24+4*E₀+(6*N₀+3)+(2*E₀+4*N₀+6+2*C₀*(E₀+2*N₀+1)+2*C₀*N₀)+
        (15*(H₀*P₀)+4*N₀+P₀*N₀+3*H₀+6)+
        ((7+2*A₀+2*P₀)*E₀+8*H₀+8*(H₀*P₀)+P₀*(H₀*P₀)+5*N₀+16) := by omega
    _ ≤ base+c.extentFactor*c.extentMass := by
      unfold extentFactor extentMass
      ring_nf
      omega

theorem setup_extent (base : ℕ) (_panelPos : 0<c.panelPitch) (_actorPos : 0<c.actorPitch)
    (panelWidth : (c.peerBits+1)*c.panelPitch≤c.payload/2)
    (actorWidth : (c.actorBits+1)*c.actorPitch≤c.payload/2) :
    c.setupStart base ≤ base+16*N₀+24+4*E₀ := c.setup_extent_any base panelWidth actorWidth

theorem fullEnd_le (base : ℕ) (_panelPos : 0<c.panelPitch) (_actorPos : 0<c.actorPitch)
    (panelWidth : (c.peerBits+1)*c.panelPitch≤c.payload/2)
    (actorWidth : (c.actorBits+1)*c.actorPitch≤c.payload/2) :
    c.fullEnd base ≤ base+c.extentFactor*c.extentMass := c.fullEnd_le_any base panelWidth actorWidth

end
end Hierarchy.DescentOrdinaryVenueIngress.Clip

end OAI
