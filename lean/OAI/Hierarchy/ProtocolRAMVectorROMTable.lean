import OAI.Hierarchy.ProtocolRAMBinarySpan
import OAI.Hierarchy.ProtocolRAMScan
import OAI.ThreeFlat.RAM.WordSegment
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Lattice.Fold

namespace OAI
/-! # Finite vector ROMs on the physical masked-address RAM -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DiscrepancyROM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {w p D : ℕ}

structure Table (p D : ℕ) where
  base : ℕ
  radix : ℕ
  word : Fin p→(Fin D→Fin radix)→ℕ

def Table.entries (t : Table p D) := t.radix^D
def Table.size (t : Table p D) := ProtocolRAMPurchaseSampler.span t.entries
def Table.stop (t : Table p D) := t.base+p*t.size
def Table.bank (t : Table p D) (u : Fin p) : Bank :=
  ⟨t.base+u.val*t.size,ProtocolRAMPurchaseSampler.bits t.entries⟩

def Table.words (t : Table p D) (rest : Memory w) : Memory w :=
  fillSegment t.base (p*t.size) (fun x=>
    let i:=x-t.base
    if h : i/t.size< p then
      if h' : i%t.size< t.entries then t.word ⟨i/t.size,h⟩ (finFunctionFinEquiv.symm ⟨i%t.size,h'⟩) else 0
    else 0) rest

def Table.Resident (t : Table p D) (m : Memory w) : Prop :=
  ∀ (u : Fin p) (key : Fin D→Fin t.radix),(t.bank u).read m ((finFunctionFinEquiv key).val:Word w)=
    (t.word u key:Word w)

theorem Table.resident (t : Table p D) (rest : Memory w) (room : t.entries≤2^w) :
    t.Resident (t.words rest) := by
  intro u key
  let v:=finFunctionFinEquiv key
  have small : v.val< t.entries := v.isLt
  have fit : v.val< t.size := small.trans (ProtocolRAMPurchaseSampler.lt_span _)
  have span : 0< t.size := Nat.zero_lt_of_lt fit
  have last:=Nat.mul_le_mul_right t.size u.isLt
  rw [Nat.succ_mul] at last
  have addr : t.base≤ t.base+u.val*t.size+v.val ∧ t.base+u.val*t.size+v.val< t.base+p*t.size := by omega
  have div : (u.val*t.size+v.val)/t.size=u.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ span,Nat.div_eq_of_lt fit,Nat.zero_add]
  have rem : (u.val*t.size+v.val)%t.size=v.val := Nat.mul_add_mod_of_lt fit
  change t.words rest (t.base+u.val*t.size+(v.val:Word w).val%t.size)=_
  rw [Fin.val_cast_of_lt (small.trans_le room),Nat.mod_eq_of_lt fit]
  simp only [Nat.add_assoc] at addr
  simp only [words,fillSegment,Nat.add_assoc,ite_eq_left addr,Nat.add_sub_cancel_left,div,rem,dite_eq_left u.isLt,dite_eq_left small]
  exact congrArg (fun z=>(t.word u z:Word w)) (finFunctionFinEquiv.symm_apply_apply key)

theorem Table.outside (t : Table p D) (rest : Memory w) {x : ℕ} (off : x< t.base ∨ t.stop≤ x) :
    t.words rest x=rest x := by
  simp only [words,fillSegment,ite_eq_right (show ¬(t.base≤ x ∧ x< t.base+p*t.size) by unfold stop at off;omega)]

theorem Table.Resident.frame {t : Table p D} {m finish : Memory w} (R : t.Resident m)
    (same : ∀x,t.base≤ x→x< t.stop→finish x=m x) : t.Resident finish := by
  intro u v
  let idx:=((finFunctionFinEquiv v).val:Word w).val%t.size
  have inside : idx< t.size := Nat.mod_lt _ (Nat.two_pow_pos _)
  have upper:=Nat.mul_le_mul_right t.size u.isLt
  rw [Nat.succ_mul] at upper
  change finish (t.base+u.val*t.size+idx)=_
  exact (same _ (by omega) (by unfold stop;omega)).trans (R u v)

def Table.maxWord (t : Table p D) := Finset.univ.sup (fun u : Fin p=>Finset.univ.sup (t.word u))

theorem Table.word_le (t : Table p D) (u : Fin p) (v : Fin D→Fin t.radix) : t.word u v≤ t.maxWord :=
  (Finset.le_sup (f:=t.word u) (Finset.mem_univ v)).trans
    (Finset.le_sup (f:=fun u : Fin p=>Finset.univ.sup (t.word u)) (Finset.mem_univ u))

theorem Table.charged_size (t : Table p D) : t.stop≤ t.base+p*(2*(t.radix^D+1)) :=
  Nat.add_le_add_left (Nat.mul_le_mul_left p (ProtocolRAMPurchaseSampler.span_le _)) _

def both {D E : ℕ} (a : Table p D) (b : Table p E) (rest : Memory w) := b.words (a.words rest)

theorem resident_both {D E : ℕ} (a : Table p D) (b : Table p E) (rest : Memory w)
    (apart : a.stop≤ b.base) (af : a.entries≤2^w) (bf : b.entries≤2^w) :
    a.Resident (both a b rest) ∧ b.Resident (both a b rest) :=
  ⟨(a.resident rest af).frame (fun _x _ hx=>b.outside _ (.inl (hx.trans_le apart))),
   b.resident _ bf⟩

end Hierarchy.ProtocolRAM.Calendar.DiscrepancyROM
end

end OAI
