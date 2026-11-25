import OAI.Hierarchy.DescentPackedWalshWeights

namespace OAI
/-! # Publishing an accumulated spectrum in the original difference enumeration -/
namespace Hierarchy.DescentPackedWalsh.Column
open DescentPackedWalsh DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w n k s l : ℕ}

structure Shelf where
  chunks : Bank
  offsets : Bank
  data : Bank
  lut : Bank

def scanRow (B : Shelf) (l : ℕ) : Expr :=
  let word := Expr.lookup B.data (.lookup B.chunks .row)
  if l=0 then word else .lookup B.lut (.op .add word (.lookup B.offsets .row))

def key (s l : ℕ) (x : Cell (s*2^l)) (i : Fin (2^l)) : Cell (l+s*2^l) :=
  Weight.pair l (s*2^l) (i,x)

def readDigit (s l : ℕ) (z : Cell (l+s*2^l)) :=
  let p:=(Weight.pair l (s*2^l)).symm z
  digit s p.1.val p.2.val

theorem run (B : Shelf) (out : ℕ) (mem : Memory w)
    (slot : Fin n→Fin k) (field : Fin n→Fin (2^l)) (value : Fin n→ℕ)
    (ptrs : B.chunks.Fits w out ∧ B.offsets.Fits w out ∧ n≤B.chunks.size ∧ n≤B.offsets.size)
    (source : B.data.Fits w out ∧ k≤B.data.size)
    (LUT : l≠0→ B.lut.Fits w out ∧ 2^(l+s*2^l)≤B.lut.size)
    (narrow : ∀i : Fin k,(mem (B.data.base+i.val)).val<2^(s*2^l))
    (previous : ∀i,digit s (field i).val (mem (B.data.base+(slot i).val)).val=value i)
    (header : ∀i : Fin n,mem (B.chunks.base+i.val)=((slot i).val:Word w) ∧
      mem (B.offsets.base+i.val)=((2^(s*2^l)*(field i).val:ℕ):Word w))
    (lookup : l≠0→∀i : Cell (l+s*2^l),mem (B.lut.base+i.val)=(readDigit s l i:Word w))
    (space : out+n<2^w) :
    let target:=image out n (scanRow B l) mem
    (scan w out n (scanRow B l)).Exec mem target (4+n*(2*(scanRow B l).work+4)) ∧
      (∀i : Fin n,target (out+i.val)=(value i:Word w)) ∧
      (∀z<out,target z=mem z) ∧ ∀z,out+n≤z→target z=mem z := by
  let term:=Expr.lookup B.data (.lookup B.chunks .row)
  have sf : term.Fits w out:=⟨source.1,ptrs.1,trivial⟩
  have ok : (scanRow B l).Fits w out := by
    by_cases h : l=0
    · simpa only [scanRow,ite_eq_left h] using sf
    · rw [scanRow,ite_eq_right h]
      change B.lut.Fits w out ∧ (term.Fits w out ∧ (B.offsets.Fits w out ∧ True))
      exact ⟨(LUT h).1,sf,ptrs.2.1,trivial⟩
  refine ⟨(by intro P R K mach;exact scan_exec out n _ mem ok space mach),?_,
    fun z hz=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl hz),
    fun z hz=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr hz)⟩
  intro i
  rw [ProtocolRAMGeneratedWrite.read_image]
  have get : term.eval mem (i.val:Word w)=mem (B.data.base+(slot i).val) := by
    change B.data.read mem (B.chunks.read mem (i.val:Word w))=_
    rw [DescentPackedZip.bank_read _ _ (i.isLt.trans_le ptrs.2.2.1) ptrs.1,(header i).1,
      DescentPackedZip.bank_read _ _ ((slot i).isLt.trans_le source.2) source.1]
  by_cases one : l=0
  · rw [scanRow,ite_eq_left one,get,←previous i]
    have f : (field i).val=0 := Nat.lt_one_iff.mp <| calc
      (field i).val < 2^l := (field i).isLt
      _ = 1 := by rw [one,pow_zero]
    have bnd:=narrow (slot i)
    simp only [one,pow_zero,Nat.mul_one] at bnd
    simp [digit,f,Nat.mod_eq_of_lt bnd]
  · rw [scanRow,ite_eq_right one]
    let val:=mem (B.data.base+(slot i).val)
    let name : Cell (l+s*2^l):=key s l ⟨val.val,narrow (slot i)⟩ (field i)
    change B.lut.read mem (term.eval mem (i.val:Word w)+B.offsets.read mem (i.val:Word w))=_
    rw [get,DescentPackedZip.bank_read _ _ (i.isLt.trans_le ptrs.2.2.2) ptrs.2.1,(header i).2]
    have packed : (name.val:Word w)=val+((2^(s*2^l)*(field i).val:ℕ):Word w) := by
      change ((val.val+2^(s*2^l)*(field i).val:ℕ):Word w)=_
      rw [Nat.cast_add,Fin.cast_val_eq_self]
    rw [←packed,DescentPackedZip.bank_read _ _ (name.isLt.trans_le (LUT one).2) (LUT one).1,lookup one]
    simpa [name,key,readDigit,val] using congrArg (fun z : ℕ=>(z:Word w)) (previous i)

theorem clock (B : Shelf) (l : ℕ) : 2*(scanRow B l).work+4≤60 := by
  by_cases h : l=0
  · rw [scanRow,ite_eq_left h]
    change 28 ≤ 60
    decide
  · rw [scanRow,ite_eq_right h]
    change 54 ≤ 60
    decide

end
end Hierarchy.DescentPackedWalsh.Column

end OAI
