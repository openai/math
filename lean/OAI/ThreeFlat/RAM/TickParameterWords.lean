import OAI.ThreeFlat.RAM.TickMountedPins
import Mathlib.Data.Nat.ModEq

namespace OAI
/-! # Placing the fixed navigation codebook and directory in public tick pins -/

namespace ThreeFlat.RAM.TickParameterWords
open Computability.VPVNP.BurstRAM Diagonal.ApproximateImage
open scoped Fin.CommRing
variable {w params a q nt ns : ℕ}

/-- Overlay one reserved subsegment of the public parameters with big-endian
bits of an actual fixed word table; all other parameters are copied. -/
def mount (offset len : ℕ) (word : ℕ → Word w) (initial : Fin params → Bool) (i : Fin params) :=
  if offset≤ i.val ∧ i.val<offset+w*len then
    (word ((i.val-offset)/w)).val.testBit (w-1-(i.val-offset)%w) else initial i

theorem outside (offset len : ℕ) (word : ℕ → Word w) (initial : Fin params → Bool)
    (i : Fin params) (h : i.val<offset ∨ offset+w*len ≤ i.val) :
    mount offset len word initial i=initial i := by
  simp [mount,show ¬(offset≤ i.val ∧ i.val<offset+w*len) by omega]

theorem coordinate (offset len i j : ℕ) (word : ℕ → Word w) (initial : Fin params → Bool)
    (fit : offset+w*len ≤ params) (hi : i<len) (hj : j<w) :
    let k := offset+w*i+j
    let bound : k < params := by
      have h := Nat.mul_le_mul_left w hi
      rw [Nat.mul_succ] at h
      dsimp [k]
      omega
    mount offset len word initial ⟨k,bound⟩=(word i).val.testBit (w-1-j) := by
  intro k bound
  have lim := Nat.mul_le_mul_left w hi
  rw [Nat.mul_succ] at lim
  have sub : k-offset = w*i+j := by dsimp [k]; omega
  have div : (w*i+j)/w=i := by
    rw [Nat.add_comm,Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt hj,Nat.zero_add]
  have rem : (w*i+j)%w=j := by
    rw [Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hj]
  simp only [mount,show offset≤k ∧ k<offset+w*len by dsimp [k]; omega,true_and,ite_true,sub,div,rem]

private def pin (q nt ns a : ℕ) (i : Fin params) : Fin (pinCount q nt ns params a) :=
  Fin.natAdd q (Fin.natAdd nt (Fin.natAdd ns (i.castAdd (a+(a+(a+a))))))

theorem memory_at (D : Fin q → Bool) (team : Fin nt → Bool) (step : Fin ns → Bool)
    (paramsBits : Fin params → Bool) (oa na oc nc : Fin a → Bool) (i : Fin params) :
    TickMountedPins.memory (w:=w) (fields D team step paramsBits oa na oc nc) (2+q+nt+ns+i.val) =
      BitLayout.bitWord w (paramsBits i) := by
  have addr : 2+q+nt+ns+i.val=2+(pin q nt ns a i).val := by
    simp only [pin,Fin.val_natAdd,Fin.val_castAdd]
    omega
  rw [addr,TickMountedPins.memory_at]
  simp only [pin,fields,Fin.append_left,Fin.append_right]

theorem source (D : Fin q → Bool) (team : Fin nt → Bool) (step : Fin ns → Bool)
    (initial : Fin params → Bool) (oa na oc nc : Fin a → Bool) (offset len : ℕ)
    (word : ℕ → Word w) (fit : offset+w*len ≤ params) (i : ℕ) (hi : i<len) (j : ℕ) (hj : j<w) :
    let par := mount offset len word initial
    let src := 2+q+nt+ns+offset
    TickMountedPins.memory (w:=w) (fields D team step par oa na oc nc) (src+w*i+j) =
      (((word i).val.testBit (w-1-j)).toNat : Word w) := by
  intro par src
  have h := Nat.mul_le_mul_left w hi
  rw [Nat.mul_succ] at h
  let k : Fin params := ⟨offset+w*i+j,by omega⟩
  have addr : src+w*i+j = 2+q+nt+ns+k.val := by dsimp [src,k]; omega
  rw [addr,memory_at]
  have b : par k=(word i).val.testBit (w-1-j) := coordinate offset len i j word initial fit hi hj
  rw [b]
  rfl

end ThreeFlat.RAM.TickParameterWords

end OAI
