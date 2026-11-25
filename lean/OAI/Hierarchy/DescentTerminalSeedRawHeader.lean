import OAI.Hierarchy.DescentTerminalSeedSelectors

namespace OAI
/-! # Physical seed input words for every bit string, including rejected count codes -/
namespace Hierarchy.DescentSeedRoot
open Hierarchy.DescentInitialHost Computability.BorderVNP.Crossing
open ThreeFlat Routing Catalyst Diagonal TraceBanks
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
    {R s r w : ℕ} {J : Type} [Fintype J] (digits : Fin R ≃ J × Fin (2^r))

def rawWord (w : ℕ) (z : Select X R s→Bool) (i : Fin (words X R)) : Word w :=
  let a:=(address X R).symm i
  ((sourceWord X (s:=s) digits a.1.1 a.1.2 a.2).elim (fun key=>(rawCount X z key).val) id : ℕ)

def rawBase (w : ℕ) (z : Select X R s→Bool) (a : ℕ) : Word w :=
  if h : a<words X R then rawWord X digits w z ⟨a,h⟩ else 0

theorem raw_header (z : Select X R s→Bool) (width : digitsNeeded s≤w)
    (i : Fin (words X R) × Fin (w+1)) :
    (headerPin X (s:=s) digits w i).elim z id=TraceWords.bits (wide (rawBase X digits w z i.1.val)) i.2 := by
  simp only [headerPin,rawBase,dite_eq_left i.1.isLt,rawWord]
  let a:=(address X R).symm i.1
  change (match sourceWord X (s:=s) digits a.1.1 a.1.2 a.2 with
    | .inr n=>Sum.inr (TraceWords.bits (wide (n : Word w)) i.2)
    | .inl key=>if t : i.2.val < min w (digitsNeeded s) then
        Sum.inl (key,(⟨i.2.val,(Nat.lt_min.mp t).2⟩ : Fin (digitsNeeded s)))
      else Sum.inr false : Select X R s ⊕ Bool).elim z id=
    TraceWords.bits (wide (((sourceWord X (s:=s) digits a.1.1 a.1.2 a.2).elim
      (fun key=>(rawCount X z key).val) id : ℕ) : Word w)) i.2
  generalize sourceWord X (s:=s) digits a.1.1 a.1.2 a.2 = entry
  cases entry with
  | inr n=>rfl
  | inl key=>
    have fit : (rawCount X z key).val<2^w :=
      (rawCount X z key).isLt.trans_le (Nat.pow_le_pow_right (by decide) width)
    simp only [Sum.elim_inl,TraceWords.bits,wide,Fin.val_cast_of_lt fit]
    split
    · rename_i hbit
      exact (raw_digits X z key ⟨_,(Nat.lt_min.mp hbit).2⟩).symm
    · rename_i hbit
      apply Eq.symm
      apply Nat.testBit_lt_two_pow
      exact (rawCount X z key).isLt.trans_le (Nat.pow_le_pow_right (by decide)
        (by simpa [min_eq_right width] using Nat.le_of_not_gt hbit))

theorem raw_base_selected (room : s<2^w) (c : (initialGroup X R s).Choice) :
    rawBase X digits w (selectBit X w c)=base X digits w c := by
  funext t
  unfold rawBase base
  split
  · rename_i h
    unfold rawWord wordAt
    rw [show (fun key=>(rawCount X (selectBit X w c) key).val)=selected X c from
      funext (raw_select X room c)]
  · rfl

theorem raw_observation (z : Select X R s→Bool) (j : Fin R) (v : Old X) (q : LocalPattern X v) :
    initialMemory (words X R) (rawBase X digits w z)
      (address X R ((j,.inr (.inr v)),code X q)).val=
        ((rawCount X z (j,⟨v,q⟩)).val : Word w) := by
  simp [initialMemory,rawBase,rawWord,sourceWord]

end
end Hierarchy.DescentSeedRoot

end OAI
