import OAI.Hierarchy.DescentResetControlRegisters
import OAI.Hierarchy.DescentVenueQuantityPrice

namespace OAI
namespace Hierarchy.DescentResetControlRegisters.Chart
open DescentSIMDLookup DescentVenueQuantityPlanes DescentSixParty.Chronology DescentDatedAddressBook ProtocolRAM Filter
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable (c : Chart) (base : ℕ) (earlier count inverse : Bank)
local notation "p" => c.dims
local notation "L" => State.layout p base earlier count inverse

def header (w : ℕ) : NativePhase w :=
  ⟨DescentStaticWordColumn.program w (c.first base) c.literal c.count,4+10*c.count,
    fun m=>DescentStaticWordColumn.image (c.first base) c.literal m c.count,DescentStaticWordColumn.cheap w (c.first base) c.literal c.count⟩
def phase (w : ℕ) :=(DescentVenueQuantityPlanes.phase p L w).seq (c.header base w)
theorem any {w used : ℕ} (m : Memory w) (ok : Room p L used w) (space : c.endAddress base<2^w) :
    (c.phase base earlier count inverse w).Runs m ∧
    ∀i,i<base ∨ c.endAddress base≤ i→(c.phase base earlier count inverse w).image m i=m i:=by
  have scan:=DescentVenueQuantityPlanes.any p L m ok
  have roof:=c.size base
  let mid:=(DescentVenueQuantityPlanes.phase p L w).image m
  have header : (c.header base w).Runs mid :=
    DescentStaticWordColumn.mount (c.first base) c.count c.literal mid (by omega : c.first base+c.count<2^w)
  refine ⟨NativePhase.seq_runs _ _ m scan.1 header,?_⟩
  intro i hi
  have afterBase : base≤c.first base:=by rw [first,State.shift p base];omega
  have cutoff : (L).out+(p).blocks*((p).hosts*chunks (p).groups (p).lanes)≤c.first base:=by
    exact Nat.add_le_add_left (Nat.le_pow_clog (by decide : 1 < 2) _) _
  have upper:=DescentStaticWordColumn.frame (c.first base) c.count c.literal mid i
    (by rcases hi with h|h <;>omega)
  exact upper.trans (scan.2 i (by change i<base ∨ _≤ i;omega))

def fee :=DescentVenueQuantityPlanes.fee p+4+10*c.count+7*(15*(c.count+1))
theorem billed (w : ℕ) (old : 0<(p).oldLanes) (new : 0<(p).lanes) (blocks : 0<(p).blocks) :
    let f:=c.phase base earlier count inverse w
    f.ticks+7*DescentStaticWordColumn.names f.program≤c.fee:=by
  intro f
  have prior:=DescentVenueQuantityPlanes.billed p L w old new blocks
  have header:=DescentStaticWordColumn.names_mount w (c.first base) c.literal c.count
  change (DescentVenueQuantityPlanes.phase p L w).ticks + (4+10*c.count)+
    7*DescentStaticWordColumn.names ((DescentVenueQuantityPlanes.phase p L w).program.seq _)≤_
  rw [DescentStaticWordColumn.names_seq]
  unfold fee
  change _ + 7*(_ + DescentStaticWordColumn.names (DescentStaticWordColumn.program w (c.first base) c.literal c.count))≤_
  omega

theorem rate {ι : ℕ→Type*} (v : ∀h,ι h→Chart) (r : State.ScalarRoom (fun h i=>(v h i).dims))
    (short : ∃K : ℕ,∀ᶠ h : ℕ in atTop,∀i,(v h i).bits+(v h i).dims.lanes≤K*h) :
    Bounded (fun h i=>(v h i).endAddress 0):=by
  obtain ⟨K,hK⟩:=short
  have table:=Bounded.pow_of_linear (K:=K) hK
  have scale:Bounded (fun h i=>2^(v h i).bits):=table.of_le fun h i=>Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)
  have chunks_:Bounded (fun h i=>chunks (v h i).dims.groups (v h i).dims.lanes):=
    (r.groups.add r.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows:=(r.hosts.mul chunks_).padded
  have raw:=(r.oldHosts.mul r.sheets).padded
  have area:=(((((State.extent_rate _ r).add rows).add raw).add raw).add scale).add table
  exact area
end
end Hierarchy.DescentResetControlRegisters.Chart

end OAI
