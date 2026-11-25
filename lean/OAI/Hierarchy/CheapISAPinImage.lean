import OAI.Hierarchy.CheapISABanks
import OAI.ThreeFlat.Diagonal.TraceWordTests
import OAI.ThreeFlat.Diagonal.TraceBanks

namespace OAI
/-! # Fixed Boolean input pins and the observed low bits of the constant-ISA simulation -/
namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM ThreeFlat.Diagonal
open scoped Fin.CommRing
variable {w p u S : ℕ} {X Q : Type*}

def translatedAddr (p r : ℕ) (addr : Fin u→ Word w) (i : Fin u) : Word (width w) :=
  (dataAddr p r (addr i) : Word (width w))

def bitIndex (j : Fin (w+1)) : Fin (width w+1) := ⟨j.val,by have :=j.isLt;unfold width;omega⟩

def translatedPin (dataPin : Q→ X⊕(Fin u×Fin (w+1))) : Q→ X⊕(Fin u×Fin (width w+1)) :=
  Sum.map id (fun x=>(x.1,bitIndex x.2)) ∘ dataPin

/-- The instruction ROM and zeroed register bank are fixed bits. Original input
bits are translated by the data-bank offset, with zero extension at the top. -/
def headerPin (r : ℕ) (code : Fin p→ Fin 7→ Word (width w))
    (init : Fin S×Fin (w+1)→ X⊕Bool) (ij : Fin (dataBase p r+S)×Fin (width w+1)) : X⊕Bool :=
  if low : ij.1.val < dataBase p r then
    .inr ((bankHeader r code (fun _=>0) ij.1.val).val.testBit ij.2.val)
  else if bit : ij.2.val < w+1 then
    init (⟨ij.1.val-dataBase p r,by have :=ij.1.isLt;omega⟩,⟨ij.2.val,bit⟩)
  else .inr false

theorem headerPin_read (r : ℕ) (code : Fin p→ Fin 7→ Word (width w))
    (init : Fin S×Fin (w+1)→ X⊕Bool) (assign : X→ Bool) (header : ℕ→ Word w)
    (old : ∀i,Sum.elim assign id (init i)=TraceWords.bits (TraceBanks.wide (header i.1.val)) i.2)
    (ij : Fin (dataBase p r+S)×Fin (width w+1)) :
    Sum.elim assign id (headerPin r code init ij)=TraceWords.bits
      (TraceBanks.wide (bankHeader r code header ij.1.val)) ij.2 := by
  by_cases low : ij.1.val < dataBase p r
  · have same : bankHeader r code (fun _=>0) ij.1.val=bankHeader r code header ij.1.val := by
      by_cases rom : ij.1.val < regBase p <;> simp [bankHeader,rom,low]
    simp [headerPin,low,same,TraceWords.bits,TraceBanks.wide]
  · have above : ¬ij.1.val < regBase p :=
      fun h=>low (h.trans_le (Nat.le_add_right (regBase p) r))
    have room : ij.1.val-dataBase p r < S:=by have :=ij.1.isLt;omega
    by_cases bit : ij.2.val < w+1
    · simpa [headerPin,low,bit,bankHeader,above,TraceWords.bits,TraceBanks.wide] using
        old (⟨ij.1.val-dataBase p r,room⟩,⟨ij.2.val,bit⟩)
    · have fit:=(header (ij.1.val-dataBase p r)).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega : w ≤ ij.2.val))
      simp [headerPin,low,bit,bankHeader,above,TraceWords.bits,TraceBanks.wide,Nat.testBit_lt_two_pow fit]

theorem translated_bit (r : ℕ) (addr : Fin u→ Word w) (old : Memory w) (new : Memory (width w))
    (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1))
    (read : ∀a : Word w,new (dataAddr p r a)=wide (old a.val))
    (i : Fin u) (j : Fin (w+1)) :
    TraceWords.bits (TraceBanks.wide (new (translatedAddr p r addr i).val)) (bitIndex j)=
    TraceWords.bits (TraceBanks.wide (old (addr i).val)) j := by
  have loc : (translatedAddr p r addr i).val=dataAddr p r (addr i):=Fin.val_cast_of_lt (data_fits hp hr _)
  simp [loc,read,TraceWords.bits,TraceBanks.wide,bitIndex]

end Hierarchy.CheapISA

end OAI
