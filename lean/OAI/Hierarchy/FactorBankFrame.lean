import OAI.Hierarchy.FactorOwnerPass
import OAI.Hierarchy.FactorDigitPass

namespace OAI
/-! # Exact memory frames of the native threshold and owner scans -/

namespace Hierarchy.FactorBucketRAM

open FactorAllocation Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {width w N d T : ℕ}

def Outside (a base size : ℕ) := a<base ∨ base+size≤a

private theorem away {a base size i : ℕ} (h : Outside a base size) (hi : i<size) :
    a≠base+i := by
  rcases h with h|h
  · exact (h.trans_le (Nat.le_add_right _ _)).ne
  · omega

theorem digit_untouched (v : Parameters width) (m : Memory width) (rows s digitBase : ℕ)
    (pos : 0<s) (sFit : s<2^width) (nFit : rows*s<2^width) (addrFit : digitBase+rows≤2^width)
    (pChannels : v 1=(s:Word width)) (pd : v 7=(digitBase:Word width)) (n : ℕ) (hn : n≤rows*s)
    (a : ℕ) (ha : Outside a digitBase rows) : iterRows digitStep v m n a=m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have less : n<rows*s := by omega
    have rowBound : n/s<rows := (Nat.div_lt_iff_lt_mul pos).mpr less
    have ab : digitBase+n/s<2^width := by omega
    have dv := (div_mod_word (less.trans nFit) sFit).1
    simp only [iterRows,digitStep,pChannels,dv,pd,←Nat.cast_add]
    rw [GridPassageRAMRow.writeMemory_nat _ _ ab,Function.update_of_ne (away ha rowBound)]
    exact ih (by omega)

/-- The reads of the retained key table prove exactly which counter address
can be written, independently of the initial counter value. -/
theorem owner_untouched (v : Parameters width) (bank : OwnerLayout N ((20*(w+1)+2)^d))
    (m : Memory width) (tag : Fin N → Key w d) (pkeys : v 8=(bank.keys:Word width))
    (pcounts : v 9=(bank.counts:Word width)) (pout : v 10=(bank.output:Word width))
    (pt : v 4=(T:Word width)) (smallT : T<2^width) (fits : bank.output+N≤2^width)
    (keys : ∀ i : Fin N, m (bank.keys+i.val)=(classIndex (tag i):Word width)) (n : ℕ) (hn : n≤N) :
    ∀ a, Outside a bank.counts ((20*(w+1)+2)^d) → Outside a bank.output N →
      iterRows ownerStep v m n a=m a := by
  induction n with
  | zero => intro a _ _; rfl
  | succ n ih =>
    let i : Fin N := ⟨n,by omega⟩
    let mem := iterRows ownerStep v m n
    let g := tag i
    have ii := i.isLt
    have kb := bank.beforeCounts
    have cb := bank.beforeOutput
    have read : mem (bank.keys+i.val)=(classIndex g:Word width) :=
      (ih (by omega) _ (Or.inl (by omega)) (Or.inl (by omega))).trans (keys i)
    have run := owner_natural v mem bank i g pkeys pcounts pout pt smallT fits read
      (mem (bank.counts+classIndex g)).val rfl
    intro a hc ho
    change ownerStep v (i.val:Word width) mem a=m a
    have gi : classIndex g < (20*(w+1)+2)^d := (finFunctionFinEquiv g).isLt
    rw [run,Function.update_of_ne (away ho ii),Function.update_of_ne (away hc gi)]
    exact ih (by omega) a hc ho

end Hierarchy.FactorBucketRAM

end OAI
