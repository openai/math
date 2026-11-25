import OAI.Hierarchy.DescentOperandLaneRead
import OAI.Hierarchy.DescentDepotPage
import OAI.Hierarchy.DescentOrdinaryRetainedPaths
import OAI.Hierarchy.DescentSignedRoleScans
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # The two endpoint paths in all eleven roles at a fixed public age -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Paths
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentHaloWalkRAM DescentSharedCableNames
open DescentPackedColony DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) {H J M w : ℕ}
def width := ParentIncidence.pathBits s.degree*(s.blocks*s.cap)
def id (side : Bool) (role : Fin 11) : Fin 22:=finProdFinEquiv (finTwoEquiv.symm side,role)
def slice (profile b slots : ℕ) (v : Parts s) (j : Fin 22) : Cell (width s) :=
  let pair : Fin 2×Fin 11:=finProdFinEquiv.symm j
  encode _ (s.blocks*s.cap) (fun t=>let q : Fin s.blocks×Fin s.cap:=finProdFinEquiv.symm t
    atSeat s profile b slots (finTwoEquiv pair.1) v q.1 q.2 pair.2)
def law (profile b slots j : ℕ) (v : Cell (totalBits s)) : Cell (width s) :=
  slice s profile b slots (separate s v) (Fin.ofNat 22 j)
@[simp] theorem of_index (j : Fin 22) : Fin.ofNat 22 j.val=j :=Fin.ext (Nat.mod_eq_of_lt j.isLt)

theorem lane_read (profile b slots : ℕ) (side : Bool) (role : Fin 11) (v : Parts s)
    (x : Fin s.blocks) (t : Fin s.cap) :
    (encode _ (s.blocks*s.cap)).symm (law s profile b slots (id side role).val (combine s v)) (finProdFinEquiv (x,t))=
      atSeat s profile b slots side v x t role :=by
  simp only [law,of_index,separate_combine,slice,id,Equiv.symm_apply_apply,Equiv.apply_symm_apply]

/-- One small path digit per old outgoing seat suffices in each of the 22
passes, even when one word cannot hold all eleven roles at once. -/
theorem width_le : width s≤2*totalBits s :=by
  let L:=Packed.bits s.degree
  have deg:s.degree+1≤2^L:=Nat.le_pow_clog (by decide) _
  have four:(s.degree+1)^4≤2^(4*L):=by
    have h:=Nat.pow_le_pow_left deg 4
    simpa only [←pow_mul,Nat.mul_comm L 4] using h
  have earlier:ParentIncidence.pathBits s.degree≤4*L+1:=by
    apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
    change (s.degree+1)^4+1≤2^(4*L+1)
    rw [pow_succ (2 : ℕ) (4*L)];have pos:=Nat.two_pow_pos (4*L);omega
  have wire:ParentIncidence.pathBits s.degree≤4*DescentSignedCableCodec.width s.degree s.cap :=by
    unfold DescentSignedCableCodec.width;dsimp only [L] at earlier;omega
  have tape:width s≤2*cableBits s:=by
    calc
      width s ≤ (4*DescentSignedCableCodec.width s.degree s.cap)*(s.blocks*s.cap):=Nat.mul_le_mul_right _ wire
      _=2*cableBits s:=by unfold cableBits;ring
  unfold totalBits;omega

theorem packed {amount : ℕ} (large : 2*totalBits s+1≤amount) (payment : M*amount≤w/2) :
    M*max (totalBits s) (width s)≤w/2 :=by
  exact (Nat.mul_le_mul_left _ (max_le (by omega) ((width_le s).trans (by omega)))).trans payment

def bank (H J M base : ℕ) (side : Bool) (role : Fin 11) : Bank :=
  ⟨RoleScans.home (totalBits s) H J M 22 base+(id side role).val*(H*chunks J M),Nat.clog 2 (H*chunks J M)⟩

def phase (profile b slots H J M w base : ℕ) (old : Bank) : NativePhase w :=
  let f:=law s profile b slots
  ⟨RoleScans.cpu f H J M w base 22 old,RoleScans.ticks (totalBits s) H J M 22,
    RoleScans.image f H J M base 22 old,
    cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@ProtocolRAM.program_cheap _ _)⟩

theorem any (profile b slots base : ℕ) (old : Bank) (m : Memory w) (lower : old.base+old.size≤base)
    (capacity : H*chunks J M≤old.size) {amount : ℕ} (large : 2*totalBits s+1≤amount) (pay : M*amount≤w/2)
    (room : RoleScans.limit (totalBits s) H J M base 22<2^w) :
    let stage:=phase s profile b slots H J M w base old
    stage.Runs m ∧ (∀x,x<base ∨ RoleScans.limit (totalBits s) H J M base 22≤x→stage.image m x=m x) :=by
  intro stage
  have actual:=RoleScans.any_run (law s profile b slots) base 22 old m lower capacity (packed s large pay) room
  exact ⟨actual.1,actual.2.1⟩

theorem emitted (profile b slots base : ℕ) (old : Bank) (m : Memory w) (lower : old.base+old.size≤base)
    (capacity : H*chunks J M≤old.size) {amount : ℕ} (large : 2*totalBits s+1≤amount) (pay : M*amount≤w/2)
    (room : RoleScans.limit (totalBits s) H J M base 22<2^w) (prior : Fin H→Fin J→Parts s)
    (source : Reads old (fun h g=>combine s (prior h g)) M m) (side : Bool) (role : Fin 11) :
    Reads (bank s H J M base side role) (fun h g=>slice s profile b slots (prior h g) (id side role)) M
      ((phase s profile b slots H J M w base old).image m) :=by
  intro p
  simpa only [phase,bank,law,separate_combine,of_index] using
    (RoleScans.read (law s profile b slots) base 22 old m lower capacity (packed s large pay) room _ source (id side role) p)

def readSlot (H J M base : ℕ) (side : Bool) (role : Fin 11) (m : Memory w) (positive : 0<M)
    (v : Fin H) (g : Fin J) (x : Fin s.blocks) (t : Fin s.cap) :=
  let source:=bank s H J M base side role
  digit (ParentIncidence.pathBits s.degree) (finProdFinEquiv (x,t)).val
    (digit (width s) (lane g positive).val (m (source.base+(row H J M (position v g positive)).val)).val)

theorem read_slot (profile b slots base : ℕ) (old : Bank) (m : Memory w) (lower : old.base+old.size≤base)
    (capacity : H*chunks J M≤old.size) {amount : ℕ} (large : 2*totalBits s+1≤amount)
    (pay : M*amount≤w/2) (room : RoleScans.limit (totalBits s) H J M base 22<2^w)
    (prior : Fin H→Fin J→Parts s) (source : Reads old (fun h g=>combine s (prior h g)) M m)
    (positive : 0<M) (side : Bool) (role : Fin 11) (v : Fin H) (g : Fin J) (x : Fin s.blocks) (t : Fin s.cap) :
    readSlot s H J M base side role ((phase s profile b slots H J M w base old).image m) positive v g x t=
    (atSeat s profile b slots side (prior v g) x t role).val :=by
  have sized : width s ≤ amount := (width_le s).trans ((Nat.le_add_right ..).trans large)
  have fit : width s*M ≤ w := by
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_left M sized).trans (pay.trans (Nat.div_le_self ..))
  have stored:=emitted s profile b slots base old m lower capacity large pay room prior source side role
  dsimp only [readSlot]
  rw [DescentOperandStateBanks.Reset.lane_read _ _ _ stored fit positive v g]
  unfold slice
  simp only [id,Equiv.symm_apply_apply,Equiv.apply_symm_apply,digit_encode]

/-- All 22 roles share the original batching parameter and the exponent of the
already charged donor lookup. Input and output strides are public. -/
theorem price (H J M amount : ℕ) (large : 2*totalBits s+1≤amount) :
    let n:=H*chunks J M
    RoleScans.ticks (totalBits s) H J M 22 ≤ 1600*(1+n+2^(amount*M)) ∧
      ∀base,RoleScans.limit (totalBits s) H J M base 22≤base+100*(1+n+2^(amount*M)) :=by
  intro n
  have ht : (2:ℕ)^(totalBits s*M) ≤ 2^(amount*M) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right M (show totalBits s≤amount by omega))
  have positive : 0 < (2:ℕ)^(amount*M) := Nat.two_pow_pos _
  have ceil:= (ceilPage n).2
  change (4+10*(22*(2^(totalBits s*M)+2^(Nat.clog 2 n))))+(4+22*(4+44*n))≤_ ∧ _
  constructor
  · omega
  · intro base;change base+22*(2^(totalBits s*M)+2^(Nat.clog 2 n))+22*n≤_;omega

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Paths

end OAI
