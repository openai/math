import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Direct indexing of a retained packed row bank, including its final partial word -/
namespace Hierarchy.DescentSixParty.Chronology.PackedSource
open Hierarchy.DescentSIMDLookup Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
noncomputable section
variable {bits H r M w : ℕ} (x : Fin H→Fin r→Cell bits) (mem : Memory w) (base : ℕ)

private theorem cell_digit (width : bits*M≤w) (reads : ∀p : Row H r M,
    mem (base+(row H r M p).val)=(((data (M:=M) x p).val : ℕ) : Word w)) (p : Row H r M)
    (lane : Fin M) (present : p.2.val*M+lane.val<r) :
    digit bits lane.val (mem (base+(row H r M p).val)).val=(x p.1 ⟨_,present⟩).val := by
  have small := (data (M:=M) x p).isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) width)
  rw [reads p,Fin.val_cast_of_lt small]
  simp only [data,digit_encode,dite_eq_left present]

theorem read (live : 0<M) (width : bits*M≤w) (reads : ∀p : Row H r M,
    mem (base+(row H r M p).val)=(((data (M:=M) x p).val : ℕ) : Word w)) (v : Fin H) (j : Fin r) :
    digit bits (j.val%M) (mem (base+(j.val/M+chunks r M*v.val))).val=(x v j).val := by
  let p:=position v j live
  let ℓ:=lane j live
  have index : p.2.val*M+ℓ.val=j.val:=Nat.div_add_mod' ..
  have counted:=cell_digit x mem base width reads p ℓ (index.trans_lt j.isLt)
  have consistent : (⟨p.2.val*M+ℓ.val,index.trans_lt j.isLt⟩ : Fin r)=j:=Fin.ext index
  change _=(x v ⟨p.2.val*M+ℓ.val,index.trans_lt j.isLt⟩).val at counted
  rw [consistent] at counted
  exact counted

end
end Hierarchy.DescentSixParty.Chronology.PackedSource

end OAI
