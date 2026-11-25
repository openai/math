import OAI.Hierarchy.DescentSharedLeafLookup
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # A shared literal broadcast of scalar ranks to live and padded replica lanes -/
namespace Hierarchy.DescentSharedLeafLookup.Public
open DescentSIMDLookup DescentPackedZip DescentPackedColony.Phase.Arena ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
def stride (H G M : ℕ) :=2^(Nat.clog 2 (H*chunks G M))
def words (d M : ℕ) :=(M+1)*2^d
def stop (base H G M d : ℕ) :=base+2*stride H G M+2^(Nat.clog 2 (words d M))
def header (base H G M d : ℕ) (ranks : Bank) : Header :=
  let b:=Nat.clog 2 (H*chunks G M)
  ⟨ranks,⟨base,b⟩,⟨base+stride H G M,b⟩,⟨base+2*stride H G M,Nat.clog 2 (words d M)⟩⟩
def literals (base N H G M d w : ℕ) : Image w :=
  let cnt:=H*chunks G M
  let pad:=stride H G M
  let start:=base+2*pad
  ⟨base,stop base H G M d,fun a=>
    if lo:a-base<cnt then
      ((((row H G M).symm ⟨_,lo⟩).1.val*N:ℕ):Word w)
    else if cut:base+pad≤a ∧ a-(base+pad)<cnt then
      (((usedRow ((row H G M).symm ⟨_,cut.2⟩)).val*2^d:ℕ):Word w)
    else if rep:a-start<words d M then
      let pair : Fin (M+1)×Cell d:=finProdFinEquiv.symm ⟨_,rep⟩
      ((repeated pair.1 pair.2).val:Word w)
    else 0⟩

theorem mounted {w : ℕ} (base N H G M d : ℕ) (ranks : Bank) (m : Memory w)
    (data : (literals base N H G M d w).Resident m) : Fixed (header base H G M d ranks) N H G M d m := by
  let pad:=stride H G M
  let rows:=H*chunks G M
  have room : rows≤pad:=Nat.le_pow_clog (by decide) _
  have repeatRoom : words d M≤2^(Nat.clog 2 (words d M)):=Nat.le_pow_clog (by decide) _
  have more : base+2*pad≤ stop base H G M d:=Nat.le_add_right ..
  constructor
  · intro p
    let j:=row H G M p
    have inside:j.val<rows:=j.isLt
    have read:=data (base+j.val) (by change base ≤ _; omega) (by change _ < stop base H G M d;omega)
    have low : base+j.val-base=j.val :=by omega
    change j.val < H*chunks G M at inside
    simp only [literals, low] at read
    rw [dite_eq_left inside] at read
    change m (base+j.val)=_
    change m (base+j.val)=((((row H G M).symm j).1.val*N:ℕ):Word w) at read
    simpa only [j,Equiv.symm_apply_apply] using read
  · intro p
    let j:=row H G M p
    have inside:j.val<rows:=j.isLt
    have read:=data (base+pad+j.val) (by change base ≤ _; omega) (by change _ < stop base H G M d;omega)
    have fst:¬(base+pad+j.val-base<H*chunks G M):=by change ¬(_<rows);omega
    have snd:base+pad≤base+pad+j.val ∧ base+pad+j.val-(base+pad)<H*chunks G M:=by change _∧_<rows;omega
    simpa [literals,header,fst,snd,pad,j,rows] using read
  · intro i x
    let j:=finProdFinEquiv (i,x)
    have val:j.val=repeatAddr i x:=by simp [j,repeatAddr,Nat.add_comm,Nat.mul_comm]
    have seg:j.val<words d M:=j.isLt
    let a:=base+2*pad+j.val
    have a1:base≤a:=by dsimp [a];omega
    have a2:a< stop base H G M d:=by change base+2*pad+j.val<base+2*pad+_;omega
    have read:=data a a1 a2
    have fst:¬a-base<rows:=by dsimp [a];omega
    have snd:¬(base+pad≤a ∧ a-(base+pad)<rows):=by dsimp [a];omega
    change m (base+2*pad+repeatAddr i x)=_
    rw [←val]
    have offset : a-(base+2*stride H G M)=j.val :=by dsimp only [a,pad];omega
    change ¬a-base < H*chunks G M at fst
    change ¬(base+stride H G M≤a ∧ a-(base+stride H G M)<H*chunks G M) at snd
    simp only [literals] at read
    rw [dite_eq_right fst, dite_eq_right snd] at read
    simp only [offset,dite_eq_left seg] at read
    change m a=((repeated (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2).val:Word w) at read
    simpa only [a,j,Equiv.symm_apply_apply] using read

end
end Hierarchy.DescentSharedLeafLookup.Public

end OAI
