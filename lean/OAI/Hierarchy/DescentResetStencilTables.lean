import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentPackedSchedulePins

namespace OAI
/-! # One immutable public image for a finite list of packed field insertions -/
namespace Hierarchy.DescentPlainTerminal.StencilTables
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local DescentPackedColony.Phase
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {d N M w : ℕ}

def start (base d N M j : ℕ) := base+j*2^((d*N+d)*M)
def tabs (base d N M : ℕ) (j : Fin N) : Tables :=
  ⟨⟨base,d*N*M⟩,⟨start base d N M (j.val+1),(d*N+d)*M⟩⟩

def image (base d N M : ℕ) : Arena.Image w :=
  ⟨base,start base d N M (N+1),fun z=>
    let p:=2^((d*N+d)*M)
    let slab:=(z-base)/p
    let x:=(z-base)%p
    if slab=0 then (2^(d*M)*x:ℕ)
    else if h:slab-1<N then (DescentPackedZip.table (Gather.setField (d:=d) (⟨slab-1,h⟩ : Fin N))
      (⟨x,Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Cell ((d*N+d)*M))).val else 0⟩

theorem reads (base d N M : ℕ) (m : Memory w) (installed : (image base d N M).Resident m) (j : Fin N) :
    Static (tabs base d N M j) (Gather.setField (d:=d) j) M m := by
  let page:=2^((d*N+d)*M)
  have step := Nat.mul_le_mul_right M (Nat.le_add_right (d*N) d)
  have shiftSize : 2^(d*N*M)≤page:=Nat.pow_le_pow_right (by decide) step
  have stop (i : ℕ) (a : ℕ) (lo : i<N+1) (hi : a<page) : base+i*page+a<start base d N M (N+1) := by
    have bound:=Nat.mul_le_mul_right page lo
    dsimp [start]
    change base+i*page+a<base+(N+1)*page
    rw [Nat.succ_mul] at bound
    omega
  constructor
  · intro x
    have fits : x.val<2^((d*N+d)*M) := x.isLt.trans_le shiftSize
    have top:=stop 0 x.val (by omega) fits
    have rd:=installed (base+x.val) (by change base≤base+x.val; exact Nat.le_add_right ..)
      (by change base+x.val<start base d N M (N+1); simpa only [Nat.zero_mul,Nat.add_zero] using top)
    simpa only [image,tabs,Nat.add_sub_cancel_left,Nat.div_eq_of_lt fits,Nat.mod_eq_of_lt fits,ite_eq_left rfl,ite_true] using rd
  · intro x
    have rd:=installed (start base d N M (j.val+1)+x.val) (by change base≤base+_+_; omega)
      (by change start base d N M (j.val+1)+x.val<start base d N M (N+1)
          exact stop (j.val+1) x.val (by omega) x.isLt)
    have delta : start base d N M (j.val+1)+x.val-base=(j.val+1)*2^((d*N+d)*M)+x.val := by
      simp [start,Nat.add_assoc]
    have slab : ((j.val+1)*2^((d*N+d)*M)+x.val)/2^((d*N+d)*M)=j.val+1 := by
      rw [Nat.mul_comm (j.val+1),Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt x.isLt,Nat.add_zero]
    have offset : ((j.val+1)*2^((d*N+d)*M)+x.val)%2^((d*N+d)*M)=x.val := by
      rw [Nat.mul_comm (j.val+1),Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt x.isLt]
    simpa only [image,tabs,delta,slab,offset,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,
      dite_eq_left j.isLt] using rd

theorem footprint (base d N M h : ℕ) (short : (d*N+d)*M≤h/2) :
    start base d N M (N+1)-base≤(N+1)*2^(h/2) := by
  simpa [start] using Nat.mul_le_mul_left (N+1) (Nat.pow_le_pow_right (by decide : 0<2) short)


end
end Hierarchy.DescentPlainTerminal.StencilTables

end OAI
