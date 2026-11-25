import OAI.Hierarchy.DescentPackedWalshWeights
import OAI.Hierarchy.DescentPackedWalshLayout

namespace OAI
/-! # The fixed gain and normalization dictionaries of one local Walsh reduction -/
namespace Hierarchy.DescentPackedWalsh.Weight
open DescentPackedWalsh DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

def banks (root H u l b g : ℕ) (dep coef data : Bank) : Header :=
  ⟨⟨root,rowBits H u⟩,dep,coef,⟨root+page H u,g⟩,data,⟨root+page H u+2^g,g+b*2^l⟩⟩

def footprint (H u l b g : ℕ) := page H u+2^g+2^(g+b*2^l)

def contents (H u l b c g : ℕ) (n : ℕ) : Word w :=
  if n<page H u then ((n/2^u : ℕ) : Word w)
  else if n<page H u+2^g then ((2^(b*2^l)*(n-page H u) : ℕ) : Word w)
  else if h : n-(page H u+2^g)<2^(g+b*2^l) then
    (table (u+l) b c g l ⟨_,h⟩).val else 0

def install (root H u l b c g : ℕ) (m : Memory w) : Memory w := fun z=>
  if root≤z ∧ z<root+footprint H u l b g then contents H u l b c g (z-root) else m z

theorem reads (root H u l b c g : ℕ) (dep coef data : Bank) (m : Memory w) :
    Fixed (banks root H u l b g dep coef data) u l b c g H (install root H u l b c g m) := by
  have hk:=Nat.two_pow_pos (g+b*2^l)
  have hg:=Nat.two_pow_pos g
  constructor
  · intro v p
    have hp:=(row v p).isLt.trans_le (rows_le H u)
    have inRange : root+(row v p).val<root+footprint H u l b g:=by unfold footprint;omega
    change install root H u l b c g m (root+(row v p).val)=_
    rw [install,ite_eq_left ⟨Nat.le_add_right ..,inRange⟩,Nat.add_sub_cancel_left,contents,ite_eq_left hp]
    have addr : (row v p).val=(ordinal u p).val+2^u*v.val:=rfl
    rw [addr,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt (ordinal u p).isLt,Nat.zero_add]
  · intro x
    have inRange : root+page H u+x.val<root+footprint H u l b g:=by unfold footprint;omega
    change install root H u l b c g m (root+page H u+x.val)=_
    rw [install,ite_eq_left ⟨by omega,inRange⟩]
    have offset : root+page H u+x.val-root=page H u+x.val:=by omega
    rw [offset,contents,ite_eq_right (by omega),ite_eq_left (by omega),Nat.add_sub_cancel_left]
  · intro i
    have inRange : root+page H u+2^g+i.val<root+footprint H u l b g:=by unfold footprint;omega
    change install root H u l b c g m (root+page H u+2^g+i.val)=_
    rw [install,ite_eq_left ⟨by omega,inRange⟩]
    have offset : root+page H u+2^g+i.val-root=page H u+2^g+i.val:=by omega
    simp only [offset,contents,ite_eq_right (show ¬page H u+2^g+i.val<page H u by omega),
      ite_eq_right (show ¬page H u+2^g+i.val<page H u+2^g by omega),Nat.add_sub_cancel_left,
      dite_eq_left i.isLt]

theorem room (root dst H u l b g : ℕ) (dep coef data : Bank) (endBound : dst+H*2^u<2^w)
    (cover : root+footprint H u l b g≤dst) (_width : rowBits H u≤w)
    (_tableWidth : g+b*2^l≤w) (d : dep.Fits w dst) (k : coef.Fits w dst) (p : data.Fits w dst)
    (hosts : H≤dep.size ∧ H≤coef.size) (old : H*2^u≤data.size) :
    Room (banks root H u l b g dep coef data) dst H u l b g w := by
  have enough (A : Bank) (endAddress : A.base+A.size≤dst) : A.Fits w dst :=
    ⟨Nat.two_pow_pos _,by omega,endAddress⟩
  unfold footprint at cover
  have resultsEnd : root+page H u+2^g+2^(g+b*2^l)≤dst := by
    simpa only [Nat.add_assoc] using cover
  have shiftEnd : root+page H u+2^g≤dst := (Nat.le_add_right _ _).trans resultsEnd
  have ownerEnd : root+page H u≤dst := (Nat.le_add_right _ _).trans shiftEnd
  exact ⟨enough _ ownerEnd,d,k,enough _ shiftEnd,p,enough _ resultsEnd,hosts,
    ⟨rows_le H u,old⟩,le_rfl,le_rfl,endBound⟩

theorem frame (root H u l b c g : ℕ) (m : Memory w) {z : ℕ}
    (away : z<root ∨ root+footprint H u l b g≤z) : install root H u l b c g m z=m z := by
  simp only [install,ite_eq_right (show ¬(root≤z ∧ z<root+footprint H u l b g) by omega)]

end
end Hierarchy.DescentPackedWalsh.Weight

end OAI
