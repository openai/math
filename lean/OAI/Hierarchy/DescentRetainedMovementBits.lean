import OAI.Hierarchy.DescentRetainedMovementVolume
import OAI.Hierarchy.DescentDatedRetainedPitches
import OAI.Hierarchy.DescentWalshDyadicChosen
import OAI.Hierarchy.DescentPackedChunkWork

namespace OAI
/-! # Calendar bit cost of the authentic retained data shuffle -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentSIMDLookup.Overlap DescentPackedWalsh DescentGLPacked.BankImage
noncomputable section
variable {v : Layout}

theorem CalendarPitch.movement_aperture {c k h u : ℕ} (g : v.CalendarPitch c k h u)
    (pos : 0<u) (budget : 8*u≤h) (width : v.lookupUnit≤u)
    (old : v.wholeWord*v.previousLanes≤h/2) (oldPitch : v.previousLanes≤h)
    (control : (c+k)*(c+k)≤h/2) : v.MovementAperture h:=by
  obtain ⟨a,b,d,e,_⟩:=CalendarPitch.words v g pos budget width
  have geom:=CalendarPitch.geometry v g
  have gain : v.gatherLanes≤h:=by
    have enough:=keys_fit (m:=c) pos budget
    have mono : v.gatherLanes≤u*v.gatherLanes:=Nat.le_mul_of_pos_left _ pos
    change 1+(u+u)*2^(laneBits c h u)≤h/2 at enough
    rw [←g.gather,Nat.add_mul] at enough
    omega
  refine ⟨old,a,b,d,?_,e,oldPitch,gain,?_,?_⟩
  · simpa only [geom.1] using control
  · simpa only [geom.2.2.2.1] using gain
  · simpa only [g.decoded] using gain

/-- A last short row is paid by the host. Every complete row is paid from
the number of lanes times the local cost per lane. -/
theorem bounded_pitch_rows {H G M h u : ℕ} (pos : 0<M) (room : G≤M ∨ h≤M*u) :
    Overlap.rows H G M*h≤H*h+H*G*u:=by
  rcases room with all | dense
  · have small : chunks G M≤1:=by
      change (G+M-1)/M≤1
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul pos).2 (by omega))
    have lim:Overlap.rows H G M≤H:=by simpa [Overlap.rows] using Nat.mul_le_mul_left H small
    exact (Nat.mul_le_mul_right _ lim).trans (Nat.le_add_right ..)
  · exact DescentDatedSeedStartup.chunk_work H G M h u dense

theorem CalendarPitch.movement_rows {c k h u oldUnit : ℕ} (g : v.CalendarPitch c k h u)
    (groups : v.groups=2^c) (host : 0<v.hosts) (pos : 0<u)
    (prior : 0<v.previousLanes) (previous : v.groups≤v.previousLanes ∨ h≤v.previousLanes*oldUnit) :
    v.movementMass h*h≤(halfLiteral h+1)*h+6*(v.hosts*h)+v.hosts*v.groups*(oldUnit+5*(16*u)):=by
  have bits : laneBits c h u≤c:=Nat.min_le_left ..
  have nd:2^v.high=chunks v.groups v.gatherLanes:=by
    rw [g.high,groups,g.gather]
    exact (DescentWalshDyadicBudget.exact_batch c (laneBits c h u) bits).symm
  have sam : v.grouped=v.groups:=by rw [grouped,g.cut,groups]
  have hp : 0<v.gatherLanes:=g.gather ▸ Nat.two_pow_pos _
  have clamp : v.groups≤v.gatherLanes ∨ h≤v.gatherLanes*(16*u):=by
    obtain all | dense:=DescentWalshDyadicBudget.laneBits_median c h u pos
    · left;rw [groups,g.gather,all]
    · right;simpa only [g.gather,Nat.mul_comm (16*u)] using dense
  have new_:=bounded_pitch_rows (H:=v.hosts) hp clamp
  have old:=bounded_pitch_rows (H:=v.hosts) prior previous
  have index : 2^v.high*h≤v.rowCount*h:=Nat.mul_le_mul_right _
    (Nat.le_mul_of_pos_left _ host)
  have actual : v.rowCount=Overlap.rows v.hosts v.groups v.gatherLanes:=by rw [rowCount,nd]; rfl
  rw [actual] at index
  have geom:=CalendarPitch.geometry v g
  simp only [movementMass,Nat.add_mul,Nat.one_mul,sam,g.decoded,geom.2.2.2.1,actual]
  nlinarith only [new_,old,index]

/-- A single multiplication by the physical bus width pays compilation names and
each issued clock at full native width, including every printed table. -/
theorem CalendarPitch.movement_bits {c k h u oldUnit ratio w base : ℕ} (g : v.CalendarPitch c k h u)
    (groups : v.groups=2^c) (host : 0<v.hosts) (pos : 0<u) (budget : 8*u≤h) (width : v.lookupUnit≤u)
    (old : v.wholeWord*v.previousLanes≤h/2) (oldPitch : v.previousLanes≤h)
    (control : (c+k)*(c+k)≤h/2) (prior : 0<v.previousLanes)
    (previous : v.groups≤v.previousLanes ∨ h≤v.previousLanes*oldUnit) (word : w≤ratio*h) :
    v.movementFee base w*w≤(v.movementUnits*ratio)*((halfLiteral h+1)*h+6*(v.hosts*h)+
      v.hosts*v.groups*(oldUnit+5*(16*u))) :=calc
  _ ≤ (v.movementUnits*v.movementMass h)*(ratio*h) :=
    Nat.mul_le_mul (v.movement_volume base w h (g.movement_aperture pos budget width old oldPitch control)) word
  _ = (v.movementUnits*ratio)*(v.movementMass h*h) :=by ring
  _ ≤ _ :=Nat.mul_le_mul_left _ (g.movement_rows groups host pos prior previous)

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
