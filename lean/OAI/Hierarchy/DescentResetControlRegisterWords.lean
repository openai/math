import OAI.Hierarchy.DescentResetControlRegisterRun
import OAI.Hierarchy.DescentPackedZip

namespace OAI
namespace Hierarchy.DescentResetControlRegisters.Chart
open DescentSIMDLookup DescentPackedZip DescentVenueQuantityPlanes ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (c : Chart) (base : ℕ) {w : ℕ}
local notation "p" => c.dims
local notation "M" => c.dims.lanes
local notation "rows" => c.dims.hosts*chunks c.dims.groups M
local notation "raw" => c.dims.oldHosts*c.dims.shapes

/-- The packed one-bit occurrence mask may differ at every group of a single host. -/
def withMask (a : Cell (1*M)) (s : ℕ) : Cell (c.bits*M) :=
  encode c.bits M fun j=>if (encode 1 M).symm a j=0 then 0 else (s:Cell c.bits)

theorem mask_at (a : Cell (1*M)) (s : ℕ) :
    c.masked (s*2^M+a.val)=(c.withMask a s).val:=by
  have small:a.val<2^M:=by simpa using a.isLt
  have hdiv:(s*2^M+a.val)/2^M=s:=by
    rw [Nat.mul_comm s (2^M),Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt small,Nat.add_zero]
  have hmod:(s*2^M+a.val)%2^M=a.val:=by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt small]
  simp only [masked,withMask,hdiv,hmod,Fin.cast_val_eq_self]

theorem data_at (x : Fin (p).hosts→Fin (p).groups→Cell 1)
    (s : ℕ) (j : Row (p).hosts (p).groups M) :
    c.withMask (data x j) s=
      data (fun h g=>if x h g=0 then 0 else (s:Cell c.bits)) j:=by
  unfold withMask data
  apply congrArg (encode c.bits M)
  funext i
  simp only [Equiv.symm_apply_apply]
  split <;> simp_all

def Resident (m : Memory w) : Prop :=∀i,i<c.count→m (c.first base+i)=(c.literal i:Word w)

theorem resident (earlier count inverse : Bank) (m : Memory w) :
    c.Resident base ((c.phase base earlier count inverse w).image m):=
  fun _i small=>DescentStaticWordColumn.read _ _ _ _ small

theorem lookups {m : Memory w} (keep : c.Resident base m) :
    (∀i,i<rows→m ((c.first base)+i)=((i/chunks (p).groups M : ℕ):Word w)) ∧
    (∀i,i<raw→m (c.oldHost base+i)=((i/(p).shapes:ℕ):Word w)) ∧
    (∀i,i<raw→m (c.shape base+i)=((i%(p).shapes:ℕ):Word w)) ∧
    (∀i,i<2^c.bits→m (c.scale base+i)=((i*2^M:ℕ):Word w)) ∧
    (∀i,i<2^(c.bits+M)→m (c.table base+i)=(c.masked i:Word w)):=by
  have R:rows≤ span rows:=Nat.le_pow_clog (by decide : 1 < 2) _
  have O:raw≤ span raw:=Nat.le_pow_clog (by decide : 1 < 2) _
  have scalarPos := Nat.two_pow_pos c.bits
  have tablePos := Nat.two_pow_pos (c.bits+M)
  refine ⟨?_,?_,?_,?_,?_⟩ <;> intro i hi
  · rw [keep i (by unfold count;omega),literal,dite_eq_left (lt_of_lt_of_le hi R)]
  · simp only [oldHost,Nat.add_assoc]
    rw [keep _ (by unfold count;omega)]
    simp [literal,Nat.not_lt.mpr (Nat.le_add_right ..),lt_of_lt_of_le hi O]
  · simp only [shape,oldHost,Nat.add_assoc]
    rw [keep _ (by unfold count;omega)]
    simp [literal,Nat.not_lt.mpr (Nat.le_add_right ..),lt_of_lt_of_le hi O]
  · simp only [scale,shape,oldHost,Nat.add_assoc]
    rw [keep _ (by unfold count;omega)]
    simp [literal,Nat.not_lt.mpr (Nat.le_add_right ..),hi]
  · simp only [table,scale,shape,oldHost,Nat.add_assoc]
    rw [keep _ (by unfold count;omega)]
    simp [literal,Nat.not_lt.mpr (Nat.le_add_right ..)]

theorem broadcast_read (m : Memory w) (keep : c.Resident base m) (space : c.endAddress base<2^w)
    (x : ℕ) (scalar : Expr) (j : Word w) (a : Cell (1*M))
    (active : (c.active base x).eval m j=(a.val:Word w)) :
    let t :=(scalar.eval m j).val%2^c.bits
    (c.broadcast base x scalar).eval m j=((c.withMask a t).val:Word w):=by
  intro t
  have small:t<2^c.bits:=Nat.mod_lt _ (Nat.two_pow_pos _)
  have input:a.val<2^M:=by simpa using a.isLt
  have idx:t*2^M+a.val<2^(c.bits+M):=by
    rw [pow_add]
    calc
      _<(t+1)*2^M:=by simpa only [Nat.succ_mul] using Nat.add_lt_add_left input (t*2^M)
      _≤_:=Nat.mul_le_mul_right _ small
  have answers:=c.lookups base keep
  have tableRoom:(⟨c.table base,c.bits+M⟩:Bank).Fits w (c.endAddress base):=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt space,le_rfl⟩
  change (⟨c.table base,c.bits+M⟩:Bank).read m
    ((⟨c.scale base,c.bits⟩:Bank).read m (scalar.eval m j)+(c.active base x).eval m j)=_
  rw [active]
  change (⟨c.table base,c.bits+M⟩:Bank).read m (m (c.scale base+t)+(a.val:Word w))=_
  rw [answers.2.2.2.1 t small,←Nat.cast_add,bank_read _ m idx tableRoom,
    answers.2.2.2.2 _ idx,c.mask_at]

end
end Hierarchy.DescentResetControlRegisters.Chart

end OAI
