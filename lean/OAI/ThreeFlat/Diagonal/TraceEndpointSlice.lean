import OAI.ThreeFlat.Diagonal.TraceSuffixPins
import OAI.ThreeFlat.Diagonal.TraceSourceFibers

namespace OAI
/-! # Each true trace leaf has an even prefix of independent endpoint bits -/

namespace ThreeFlat.Diagonal.TraceSuffix
open TraceSourceOwner

/-- Only the first two bits of every genuine coordinate are external.
All installed text, public advice and field parameters are fixed. -/
def fullHeader {T S : ℕ} (_size : 2*T≤S) (pin : Fin (2*T)→Bool) (pub : ℕ→Bool) (j : Fin S) :=
  if h : j.val<2*T then pin ⟨j.val,h⟩ else pub j.val

def laneStart (low lane : ℕ) := lane*(2*2^low)
def pairs (T low lane : ℕ) := min (2^low) (T-lane*2^low)
def retained (T low lane : ℕ) := 2*pairs T low lane

theorem retained_eq (T low lane : ℕ) :
    retained T low lane=min (2*2^low) (2*T-laneStart low lane) := by
  unfold retained pairs laneStart
  rw [←Nat.mul_min_mul_left,Nat.mul_sub,Nat.mul_left_comm 2 lane]

theorem retained_le {T S low lane : ℕ} (span : 2*T≤S) :
    retained T low lane≤pinCount S 1 low lane := by
  rw [retained_eq]
  simp only [pinCount,pinSpan,Nat.one_mul,Nat.mul_one,laneStart]
  omega

theorem past_true {T low lane j S : ℕ} (_span : 2*T≤S)
    (inPin : j<pinCount S 1 low lane) (fixed : retained T low lane≤j) :
    2*T≤laneStart low lane+j := by
  rw [retained_eq] at fixed
  have room : j<2*2^low := inPin.trans_le (Nat.min_le_left ..)
  omega

theorem at_true {T low lane j : ℕ} (kept : j<retained T low lane) : laneStart low lane+j<2*T := by
  rw [retained_eq] at kept
  have room := kept.trans_le (Nat.min_le_right ..)
  omega

/-- Selecting the public suffix does not change any locally wired field. -/
theorem fullPin_append {old free ports : ℕ} (clip : free≤old) (start : ℕ)
    (pub : ℕ→Bool) (whole : Fin old→Bool) (part : Fin free→Bool) (wire : Fin ports→Bool)
    (live : ∀ j : Fin free, part j=whole (j.castLE clip))
    (fixed : ∀ j : Fin old, free≤j.val → whole j=pub (start+j.val)) :
    fullPin clip start pub (Fin.append part wire)=Fin.append whole wire := by
  funext j
  induction j using Fin.addCases with
  | left i =>
    by_cases keep : i.val<free
    · rw [Fin.append_left]
      have bound : (Fin.castAdd ports i).val<free := keep
      simp only [fullPin, bound, dite_true]
      let j : Fin free := ⟨i.val,keep⟩
      change Fin.append part wire (Fin.castAdd ports j)=whole i
      rw [Fin.append_left]
      exact live j
    · rw [Fin.append_left]
      have bound : ¬(Fin.castAdd ports i).val<free := keep
      have inside : (Fin.castAdd ports i).val<old := i.isLt
      simp only [fullPin,bound,inside,dite_false,dite_true]
      exact (fixed i (by omega)).symm
  | right i =>
    rw [Fin.append_right]
    have past : ¬(Fin.natAdd old i).val<free := by change ¬old+i.val<free; omega
    have outside : ¬(Fin.natAdd old i).val<old := by change ¬old+i.val<old; omega
    simp only [fullPin,past,outside,dite_false]
    have idx : (⟨free+((Fin.natAdd old i).val-old),by have := i.isLt; change free+(old+i.val-old)<free+ports;omega⟩ : Fin (free+ports)) = Fin.natAdd free i := by
      apply Fin.ext
      change free+(old+i.val-old)=free+i.val
      omega
    rw [idx,Fin.append_right]


end ThreeFlat.Diagonal.TraceSuffix

end OAI
