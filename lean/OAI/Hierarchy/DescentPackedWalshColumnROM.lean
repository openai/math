import OAI.Hierarchy.DescentPackedWalshColumn

namespace OAI
/-! # Static extraction of the old ordinal's lane in a normalized spectrum -/
namespace Hierarchy.DescentPackedWalsh.Column
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w d k s l : ℕ}

def banks (root d _k s l : ℕ) (src : Bank) : Shelf :=
  ⟨⟨root,d⟩,⟨root+2^d,d⟩,src,⟨root+2*2^d,l+s*2^l⟩⟩

def size (d s l : ℕ) := 2*2^d+(if l=0 then 0 else 2^(l+s*2^l))

def fixedRow (slot : Fin (2^d)→Fin k) (fld : Fin (2^d)→Fin (2^l)) (s : ℕ) (j : ℕ) : Word w :=
  if lo : j<2^d then (slot ⟨_,lo⟩).val
  else if mid : j-2^d<2^d then 2^(s*2^l)*(fld ⟨_,mid⟩).val
  else if hx : j-2*2^d<2^(l+s*2^l) then readDigit s l ⟨_,hx⟩ else 0

theorem publish (src : Bank) (root out : ℕ) (slot : Fin (2^d)→Fin k) (fld : Fin (2^d)→Fin (2^l))
    (value : Fin (2^d)→ℕ) (mem : Memory w)
    (early : root+size d s l≤out)
    (input : src.Fits w out ∧ k≤ src.size) (space : out+2^d<2^w)
    (literal : ∀j<size d s l,mem (root+j)=fixedRow slot fld s j)
    (old : ∀i : Fin k,(mem (src.base+i.val)).val<2^(s*2^l))
    (values : ∀i,digit s (fld i).val (mem (src.base+(slot i).val)).val=value i) :
    let B:=banks root d k s l src
    let dst:=image out (2^d) (scanRow B l) mem
    (scan w out (2^d) (scanRow B l)).Exec mem dst (4+2^d*(2*(scanRow B l).work+4)) ∧
      (∀i : Fin (2^d),dst (out+i.val)=(value i:Word w)) ∧
      (∀z<out,dst z=mem z) ∧ ∀z,out+2^d≤z→dst z=mem z := by
  let B:=banks root d k s l src
  have minimum : 2*2^d≤ size d s l:=Nat.le_add_right ..
  have limit:=minimum.trans (show size d s l≤out by omega)
  have enough (A : Bank) (endAddress : A.base+A.size≤out) : A.Fits w out :=
    ⟨Nat.two_pow_pos _,by omega,endAddress⟩
  apply run B out mem slot fld value _ input _ old values _ _ space
  · change (Bank.mk root d).Fits w out ∧ (Bank.mk (root+2^d) d).Fits w out ∧ _ ∧ _
    exact ⟨enough _ (by change root+2^d≤_;omega),
      enough _ (by change root+2^d+2^d≤_;omega),le_rfl,le_rfl⟩
  · intro h
    have lt:=Nat.two_pow_pos (l+s*2^l)
    have tail : size d s l=2*2^d+2^(l+s*2^l):=by simp [size,h]
    exact ⟨enough _ (by change root+2*2^d+2^(l+s*2^l)≤_;omega),le_rfl⟩
  · intro i
    constructor
    · change mem (root+i.val)=_
      rw [literal _ (by omega)]
      simp [fixedRow,i.isLt]
    · change mem (root+2^d+i.val)=_
      rw [Nat.add_assoc,literal _ (by omega)]
      simp [fixedRow,show ¬2^d+i.val<2^d by omega,i.isLt]
  · intro h i
    have strict : 2*2^d+i.val<size d s l:=by simp [size,h]
    change mem (root+2*2^d+i.val)=_
    rw [Nat.add_assoc,literal _ strict]
    simp [fixedRow,show ¬2*2^d+i.val<2^d by omega,
      show ¬2*2^d+i.val-2^d<2^d by omega,i.isLt]

end
end Hierarchy.DescentPackedWalsh.Column

end OAI
