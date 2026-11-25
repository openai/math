import OAI.Hierarchy.DescentOrdinaryVenueClipRun
import OAI.Hierarchy.DescentOrdinaryActorTariff
import OAI.Hierarchy.DescentOrdinaryRasterTariff
import OAI.Hierarchy.DescentDonorMatcherSpace

namespace OAI
/-! # Public cost of both incoming pitch changes and the complete ordinary receiving phase -/
namespace Hierarchy.DescentOrdinaryVenueIngress.Clip
open DescentSIMDLookup DescentRawCablePanel DescentHaloWalkRAM DescentScalarVenueMask DescentPackedColony DescentPacking.PackedMatch.Local
open DescentSixParty.Chronology DescentPaidResidentCount ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentStaticWordColumn (names names_seq)
open ThreeFlat.RAM PhysicalProcedure
set_option quotPrecheck false
noncomputable section

def fee {w : ℕ} (p : NativePhase w) :=p.ticks+7*names p.program
private theorem fee_seq {w : ℕ} (p q : NativePhase w) : fee (p.seq q)=fee p+fee q:=by
  simp only [fee,NativePhase.seq,names_seq];ring

private theorem shrink (G A B : ℕ) (apos : 0<A) (b : B≤A) : Overlap.pieces G A B≤2:=by
  apply (Nat.min_le_right ..).trans
  have n:chunks B A<2:=by
    change (B+A-1)/A<2
    apply (Nat.div_lt_iff_lt_mul apos).2;omega
  omega

private theorem tileFee (H G A B bits w home payload : ℕ) (src : Bank) (ap : 0<A) (bp : 0<B) (sh : B≤A)
    (width : (bits+1)*A≤payload/2) : fee (transfer H G A B bits w home src)≤
      2048*(3*2^(payload/2)+Overlap.rows H G A+Overlap.rows H G B+1) :=by
  have sourceCap : (A+1)*2^(bits*A)≤2^(payload/2) :=by
    calc
      _ ≤ 2^A*2^(bits*A):=Nat.mul_le_mul_right _ (Nat.lt_two_pow_self : A+1≤2^A)
      _ = 2^((bits+1)*A):=by rw [←pow_add];congr 1;ring
      _ ≤ _:=Nat.pow_le_pow_right (by decide) width
  have span:Overlap.pieces G A B+1≤3:=by have:=shrink G A B ap sh;omega
  have bound:(Overlap.pieces G A B+1)*(A+1)*2^(bits*A)≤3*2^(payload/2):=by
    rw [Nat.mul_assoc];exact Nat.mul_le_mul span sourceCap
  exact (Overlap.tariff home H G A B bits w src ap bp).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right bound _) _) _))

/-- Both actual donor fields have room for the old lane index in the overlap lookup. -/
theorem native_input_widths (d : DonorDate) (payload : ℕ) (cap : 0<d.cap) :
    let M:=lanes payload d.amount
    (DepotRAM.totalBits d.format+1)*M≤payload/2 ∧ (2^d.exponent+1)*M≤payload/2:=by
  intro M
  have packed:2*DepotRAM.totalBits d.format+1≤d.amount:=(le_max_right ..).trans (le_max_right ..)
  have blocks:2^d.exponent+(d.exponent+3)≤d.amount:=(d.matcher_widths 0 cap (Nat.zero_le _)).2.1
  have fit:=lanes_fit payload d.amount
  constructor <;> rw [Nat.mul_comm] <;> exact (Nat.mul_le_mul_left M (by omega)).trans fit

variable (c : Clip)
local notation "P₀" => c.venue.paths
local notation "D₀" => c.venue.socket.degree
local notation "H₀" => c.venue.hosts
local notation "G₀" => c.venue.groups
local notation "N₀" => (c.core).rows
local notation "A₀" => c.actorCount
local notation "E₀" => 2^(c.payload/2)

def mass := 1+2^(c.payload/2)+c.venue.hosts+(c.core).rows+Overlap.rows H₀ G₀ c.panelPitch+Overlap.rows H₀ G₀ c.actorPitch

private theorem mass_bounds :
    1≤c.mass ∧ H₀≤c.mass ∧ N₀≤c.mass ∧ E₀≤c.mass ∧
      Overlap.rows H₀ G₀ c.panelPitch≤c.mass ∧ Overlap.rows H₀ G₀ c.actorPitch≤c.mass ∧
      1+E₀+H₀+N₀≤c.mass := by
  unfold mass
  generalize E₀ = e
  omega

def haloUnit : ℕ :=
  let L:=6*P₀+1;let T:=P₀+1+(1+P₀)
  let walk:=40*(D₀+10)^4+4;let sort:=200*(P₀+1)^3+4
  (16+10*(L+T)+P₀*(walk+sort))+7*(15*(L+1)+15*(T+1)+(11+4*(20*(D₀+10)^4))+(11+4*(100*(P₀+1)^3)))

def factor : ℕ :=2*(2048*6)+640*4+8192*(DepotRAM.ActorInputs.count c.venue.socket+1)+c.haloUnit+
  8192*(P₀+1)^2*(A₀+1)

private theorem haloFee (B : Inputs) (base w : ℕ) : fee ((c.core).haloPhase B base w)≤c.haloUnit*c.mass:=by
  let m:=c.mass
  let q:=P₀;let z:=D₀;let n:=N₀
  obtain ⟨one,h,nr,_,_,_,_⟩ := c.mass_bounds
  change 1 ≤ m at one
  change H₀ ≤ m at h
  change n ≤ m at nr
  have host:H₀*q≤ m*q:=Nat.mul_le_mul_right _ h
  have a:=DescentScalarHaloProgram.resources H₀ G₀ c.working D₀ B.adjacency ((c.core).haloBase base) w
  have raw : RootTables.length H₀ G₀ c.working D₀≤(6*q+1)*m:=by change 6*(H₀*q)+n≤_;nlinarith only [nr,host]
  have stat : DescentScalarHaloPortROM.length H₀ G₀ c.working q≤(q+1+(1+q))*m:=by
    change q*n+(H₀+(n+H₀*q))≤_;nlinarith only [Nat.mul_le_mul_left q nr,h,nr,host]
  let b:=40*(z+10)^4+4;let s:=200*(q+1)^3+4
  have bnd:=Nat.add_le_add a.1 (Nat.mul_le_mul_left 7 a.2)
  apply bnd.trans
  unfold DescentScalarHaloProgram.namesTariff haloUnit
  let walkNames:=11+4*(20*(z+10)^4);let sortNames:=11+4*(100*(q+1)^3)
  change ((4+10*RootTables.length H₀ G₀ c.working D₀)+(4+10*DescentScalarHaloPortROM.length H₀ G₀ c.working q))+(4+H₀*q*b)+(4+H₀*q*s)+7*(15*(RootTables.length H₀ G₀ c.working D₀+1)+15*(DescentScalarHaloPortROM.length H₀ G₀ c.working q+1)+walkNames+sortNames)≤
    ((16 + 10*((6*q+1)+(q+1+(1+q))) + q*(b+s)) +
      7*(15*((6*q+1)+1)+15*((q+1+(1+q))+1)+walkNames+sortNames))*m
  have cheap₁:=Nat.mul_le_mul_left walkNames one;have cheap₂:=Nat.mul_le_mul_left sortNames one
  nlinarith only [raw,stat,Nat.mul_le_mul_right b host,Nat.mul_le_mul_right s host,one,cheap₁,cheap₂]

/-- The six counted programs separately pay for their tables, scans and scalar input/output rows. -/
theorem tariff (B : Inputs) (base w : ℕ) (ap : 0<c.actorPitch) (pp : 0<c.panelPitch) (wp : 0<c.working)
    (fieldRoom : (c.peerBits+1)*c.panelPitch≤c.payload/2) (actRoom : (c.actorBits+1)*c.actorPitch≤c.payload/2) :
    fee (c.phase B base w)≤c.factor*c.mass:=by
  let z:=c.mass;let core:=c.core;let I:=c.clipped base B;let at₀:=c.setupStart base
  obtain ⟨unity,hosts,rows,exp,old₁,old₂,combined⟩ := c.mass_bounds
  change 1≤z at unity
  change H₀≤z at hosts
  change N₀≤z at rows
  change E₀≤z at exp
  change Overlap.rows H₀ G₀ c.panelPitch≤z at old₁
  change Overlap.rows H₀ G₀ c.actorPitch≤z at old₂
  change 1+E₀+H₀+N₀≤z at combined
  have lowPow : 2^(c.payload/4)≤E₀:=Nat.pow_le_pow_right (by decide) (by omega)
  have first:=tileFee H₀ G₀ c.panelPitch c.working c.peerBits w base c.payload B.panel pp wp c.working_fields.1 fieldRoom
  have second:=tileFee H₀ G₀ c.actorPitch c.working c.actorBits w (c.actorStart base) c.payload B.actors ap wp c.working_fields.2.1 actRoom
  have bill1:fee (c.panelPhase B base w)≤(2048*6)*z:=first.trans (by change 2048*(3*E₀+_+N₀+1)≤_;omega)
  have bill2:fee (c.actorPhase B base w)≤(2048*6)*z:=second.trans (by change 2048*(3*E₀+_+N₀+1)≤_;omega)
  have padded : 2^Nat.clog 2 N₀≤2*N₀+1:=by
    by_cases small:N₀≤1
    · generalize N₀=a at *;interval_cases a <;> decide
    have lower:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<N₀ by omega)
    have pos:=Nat.clog_pos (by decide : 1<2) (show 1<N₀ by omega)
    cases dep : Nat.clog 2 N₀ with
    | zero=>omega
    | succ k=>rw [dep] at lower;simp only [Nat.pred_succ] at lower;rw [Nat.pow_succ];omega
  have three:=HubRepeat.tariff at₀ H₀ G₀ c.working I.hub w
  have bill3 : fee (core.hubPhase I at₀ w)≤(640*4)*z:=three.trans (by change 640*(2^Nat.clog 2 N₀+N₀+1)≤_; omega)
  have four:=c.actor_tariff I at₀ w
  have sized : 1+2^(c.payload/4)+N₀≤z:=by omega
  have bill4 := four.trans (Nat.mul_le_mul_left _ sized)
  have bill5:=c.haloFee I at₀ w
  have six:=c.raster_tariff at₀ w
  have size₂ : 1+2^(c.payload/4)+H₀+N₀≤z:=by omega
  have bill6:=six.trans (Nat.mul_le_mul_left _ size₂)
  unfold phase Chart.phase
  change fee (((c.panelPhase B base w).seq (c.actorPhase B base w)).seq ((((core.hubPhase I at₀ w).seq (core.pairedPhase I at₀ w)).seq (core.haloPhase I at₀ w)).seq (core.rasterPhase at₀ w)))≤_
  simp only [fee_seq]
  have total:=Nat.add_le_add (Nat.add_le_add bill1 bill2) (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add bill3 bill4) bill5) bill6)
  exact total.trans (by unfold factor;dsimp only [z];ring_nf;omega)

end
end Hierarchy.DescentOrdinaryVenueIngress.Clip

end OAI
