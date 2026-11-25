import OAI.Hierarchy.DescentPackedEpochLayout

namespace OAI
/-! # Literal latch projection for the complete packed profile checker -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentTerminalEpochChart DescentPackedProfileTape DescentPackedProfileInstall DescentPackedProfileValidity
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {A : Type} {w : ℕ}

def segmentPin (w r : ℕ) (s : Source A) (a j : ℕ) : A⊕Bool :=
  let n:=slots s.seats r
  let words:=DescentDyadicSpan.span n
  if a < words then bitPin s.pin r a j
  else if a-words < n then .inr (((startsWord r (a-words):Word w)).val.testBit j) else .inr false

private theorem segment_at (lo r : ℕ) (s : Source A) (z : A→Bool) (m : Memory w) (a j : ℕ)
    (_active : a < space r s) (positive : 0 < r) (fit : DescentTerminalEpochBits.width s.C*r ≤ w) :
    (segmentPin w r s a j).elim z id=(prepare lo r s.pin z m (lo+a)).val.testBit j := by
  let n:=slots s.seats r
  let step:=DescentDyadicSpan.span n
  have sh : (startsBank lo s.seats r).base=lo+step:=rfl
  have pin_eq : segmentPin w r s a j =
      (if a < step then bitPin s.pin r a j
       else if a-step < n then .inr ((startsWord r (a-step) : Word w).val.testBit j)
       else .inr false) := rfl
  by_cases inside : a < step
  · change _=(fillSegment (lo+step) n _ (memory s.pin z w lo r m) (lo+a)).val.testBit j
    rw [fillSegment,ite_eq_right (by omega : ¬(lo+step ≤ lo+a ∧ lo+a < lo+step+n)),at_any_word s.pin z w lo r a m positive,
      Fin.val_cast_of_lt ((packed s.pin z r a).isLt.trans_le (Nat.pow_le_pow_right (by decide) fit))]
    simpa only [pin_eq,ite_eq_left inside] using bits s.pin z r a j
  · by_cases used : a-step < n
    · have diff : lo+a-(lo+step)=a-step := by omega
      change _=(fillSegment (lo+step) n _ (memory s.pin z w lo r m) (lo+a)).val.testBit j
      rw [fillSegment,ite_eq_left (by omega : lo+step ≤ lo+a ∧ lo+a < lo+step+n)]
      simp only [pin_eq,ite_eq_right inside,ite_eq_left used,Sum.elim_inr,id_eq,sh,diff]
    · have away : ¬(lo+step ≤ lo+a ∧ lo+a < lo+step+n) := by omega
      change _=(fillSegment (lo+step) n _ (memory s.pin z w lo r m) (lo+a)).val.testBit j
      rw [fillSegment,ite_eq_right away]
      have range_:=DescentDyadicSpan.span_ge n
      have dataEnd : ¬lo+a < lo+slots s.seats r:=by change ¬lo+a < lo+n;omega
      simp [pin_eq,inside,used,memory,Computability.VPVNP.RAMMemory.initialMemory,dataEnd]

def rawPin (w r : ℕ) : List (Source A)→ℕ→ℕ→A⊕Bool
  | [],_,_=>.inr false
  | s::ss,a,j=>if a < space r s then segmentPin w r s a j else rawPin w r ss (a-space r s) j

theorem raw_bits (lo r : ℕ) (ss : List (Source A)) (z : A→Bool) (m : Memory w)
    (positive : 0 < r) (fits : ∀s∈ss,DescentTerminalEpochBits.width s.C*r ≤ w) {a : ℕ} (live : a < extent r ss)
    (j : ℕ) : (rawPin w r ss a j).elim z id=(rawTape r z lo ss m (lo+a)).val.testBit j := by
  induction ss generalizing lo m a with
  | nil=>exact False.elim ((Nat.not_lt_zero _) live)
  | cons s ss ih=>
    by_cases inside : a < space r s
    · rw [rawPin,ite_eq_left inside,rawTape,raw_low r z _ ss _ (by omega)]
      exact segment_at lo r s z m a j inside positive (fits s (by simp))
    · have size : a < space r s+extent r ss:=live
      rw [rawPin,ite_eq_right inside,rawTape,show lo+a=lo+space r s+(a-space r s) by omega]
      exact ih _ _ (fun v h=>fits v (by simp [h])) (by omega)

def headerPin (w lo C r : ℕ) (ss : List (Source A)) (old : ℕ→ℕ→A⊕Bool) (a j : ℕ) : A⊕Bool :=
  let table:=lo+extent r ss
  if a < lo then old a j
  else if a < table then rawPin w r ss (a-lo) j
  else .inr (((advice table C r a:Word w)).val.testBit j)

theorem header_pin (lo C r : ℕ) (ss : List (Source A)) (z : A→Bool) (m : Memory w)
    (old : ℕ→ℕ→A⊕Bool) (old_bits : ∀a < lo,∀j,(old a j).elim z id=(m a).val.testBit j)
    (positive : 0 < r) (fits : ∀s∈ss,DescentTerminalEpochBits.width s.C*r ≤ w)
    {a : ℕ} (reach : a < end_ (lo+extent r ss) C r) (j : ℕ) :
    (headerPin w lo C r ss old a j).elim z id=(header lo C r ss z m a).val.testBit j := by
  by_cases low : a < lo
  · rw [headerPin,ite_eq_left low,frame lo C r ss z m low]
    exact old_bits a low j
  · let tab:=lo+extent r ss
    by_cases mid : a < tab
    · rw [headerPin,ite_eq_right low,ite_eq_left mid,header,before _ _ _ _ mid]
      have got:=raw_bits lo r ss z m positive fits (a:=a-lo) (by unfold tab at mid;omega) j
      rwa [show lo+(a-lo)=a by omega] at got
    · change a < end_ tab C r at reach
      have ins : tab ≤ a ∧ a < tab+(end_ tab C r-tab) := by omega
      rw [headerPin,ite_eq_right low,ite_eq_right mid]
      change (advice tab C r a : Word w).val.testBit j =
        (fillSegment tab (end_ tab C r-tab) _ (rawTape r z lo ss m) a).val.testBit j
      rw [fillSegment,ite_eq_left ins]


end
end Hierarchy.DescentPackedEpochShelves

end OAI
