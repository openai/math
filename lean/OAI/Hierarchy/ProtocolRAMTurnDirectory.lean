import OAI.Hierarchy.ProtocolRAMScan
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Fixed ordinal tables for the terminal turn scatter -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnDirectory
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open ProtocolRAM
open scoped Fin.CommRing

variable {W : ℕ}

def bank (base bits : ℕ) (j : Fin 4) : Bank := ⟨base+j.val*2^bits,bits⟩

def store (base bits : ℕ) (word : Fin 4 → ℕ → Word W) (m : Memory W) : Memory W :=
  fillSegment base (4*2^bits) (fun a =>
    if h : (a-base)/2^bits<4 then word ⟨_,h⟩ ((a-base)%2^bits) else 0) m

theorem read_store (base bits : ℕ) (word : Fin 4 → ℕ → Word W) (m : Memory W)
    (j : Fin 4) (i : ℕ) (cap : i<2^bits) (wide : i<2^W) :
    (bank base bits j).read (store base bits word m) (i:Word W)=word j i := by
  let p := 2^bits
  have pos : 0<p := Nat.two_pow_pos _
  have less : j.val*p+i<4*p := by
    have h := Nat.mul_le_mul_right p j.isLt
    rw [Nat.succ_mul] at h
    omega
  have div : (j.val*p+i)/p=j.val := by
    rw [Nat.mul_comm j.val p,Nat.mul_add_div pos,Nat.div_eq_of_lt cap,Nat.add_zero]
  have rem : (j.val*p+i)%p=i := Nat.mul_add_mod_of_lt cap
  change store base bits word m (base+j.val*p+(i:Word W).val%p)=word j i
  rw [Fin.val_cast_of_lt wide,Nat.mod_eq_of_lt cap]
  have inside : base≤base+j.val*p+i ∧ base+j.val*p+i<base+4*p := by omega
  have idx : base+j.val*p+i-base=j.val*p+i := by omega
  change (if base≤base+j.val*p+i ∧ base+j.val*p+i<base+4*p then
    (if h : (base+j.val*p+i-base)/p<4 then word ⟨_,h⟩ ((base+j.val*p+i-base)%p) else 0)
    else m (base+j.val*p+i))=_
  simp only [ite_eq_left inside,idx,div,rem,dite_eq_left j.isLt]


def fieldWords (rows sites slots base : ℕ) (i : Fin rows) (f : Fin 5) : Fin 3 → ℕ :=
  ![i.val,base+f.val*(sites*slots),f.val*rows+i.val]

/-- The first three columns address the five writes of a chronological row.
The last column is a public multiplication table for the site stride. -/
def words (rows sites slots base : ℕ) (f : Fin 4) (t : ℕ) : Word W :=
  if hf : f.val<3 then
    if ht : t<rows*5 then
      let p : Fin rows × Fin 5 := finProdFinEquiv.symm ⟨t,ht⟩
      (fieldWords rows sites slots base p.1 p.2 ⟨f.val,hf⟩:Word W)
    else 0
  else ((t*slots:ℕ):Word W)

theorem packed (rows sites slots base : ℕ) (i : Fin rows) (f : Fin 5) (j : Fin 3) :
    words (W:=W) rows sites slots base (j.castLE (by decide)) (finProdFinEquiv (i,f)).val=
      (fieldWords rows sites slots base i f j:Word W) := by
  let t : Fin (rows*5) := finProdFinEquiv (i,f)
  change words rows sites slots base (j.castLE (by decide)) t.val=_
  unfold words
  rw [dite_eq_left (show (j.castLE (by decide : 3≤4)).val<3 from j.isLt),dite_eq_left t.isLt]
  change (fieldWords rows sites slots base (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 j:Word W)=_
  rw [show finProdFinEquiv.symm t=(i,f) from finProdFinEquiv.symm_apply_apply (i,f)]

theorem site (rows sites slots base x : ℕ) :
    words (W:=W) rows sites slots base 3 x=((x*slots:ℕ):Word W) := by
  simp [words]

theorem frame (base bits : ℕ) (word : Fin 4 → ℕ → Word W) (m : Memory W) (t : ℕ)
    (outside : t<base ∨ base+4*2^bits≤t) : store base bits word m t=m t := by
  simp [store,fillSegment,show ¬(base≤t ∧ t<base+4*2^bits) by omega]

end Hierarchy.ProtocolRAMTurnDirectory

end
end OAI
