import OAI.ThreeFlat.Diagonal.LaneCursorCanonical
import OAI.ThreeFlat.Diagonal.TracePhysicalArrayLayout

namespace OAI
/-! # Word-address calculation for the public XOR-mask ordinals -/

namespace ThreeFlat.Diagonal.TracePhysical
open LaneCursor RowLayout

def maskNat (d i : ℕ) := if i=0 then 0 else if i≤d then 2^(i-1) else 2^(i-d)-1

theorem offset_nat (d : ℕ) (i : Fin (1+(d+d))) : (offset d i).val=maskNat d i.val := by
  refine Fin.addCases (fun z => ?_) (fun t => ?_) i
  · have hz : z=0 := Subsingleton.elim _ _
    subst z
    exact offset_zero d
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) t
    · rw [offset_single]
      have h := j.isLt
      simp [maskNat,Fin.val_natAdd,show 1+j.val≤d by omega]
    · rw [offset_low]
      have h := j.isLt
      simp [maskNat,Fin.val_natAdd,show ¬1+(j.val+d)≤d by omega,
        show 1+(j.val+d)-d=j.val+1 by omega]

private theorem pow_ne_prefix (a b : ℕ) : 2^a≠2^(b+2)-1 := by
  have hb := Nat.two_pow_pos b
  cases a <;> simp only [pow_zero,pow_succ] <;> omega

private theorem not_collision {d i j : ℕ} (lt : j < i) (good : i≠d+1) :
    maskNat d j ≠ maskNat d i := by
  have hi : i≠0 := by omega
  by_cases stop : i≤d
  · have sj : j≤d := by omega
    by_cases zero : j=0
    · simpa [maskNat,zero,hi,stop] using (Nat.ne_of_lt (Nat.two_pow_pos (i-1)))
    · simp only [maskNat,zero,hi,stop,sj,ite_false,ite_true]
      exact ne_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  · have big : d+2≤ i := by omega
    obtain ⟨b,hb⟩ : ∃ b, i-d=b+2 := ⟨i-d-2,by omega⟩
    by_cases zero : j=0
    · have hpow : 4≤2^(b+2) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2≤b+2)
      simp [maskNat,zero,hi,stop,hb]; omega
    · by_cases sj : j≤d
      · simpa only [maskNat,zero,hi,stop,sj,hb,ite_false,ite_true] using pow_ne_prefix (j-1) b
      · have smaller : 2^(j-d)<2^(i-d) := Nat.pow_lt_pow_right (by decide) (by omega)
        have positive := Nat.two_pow_pos (j-d)
        simp only [maskNat,zero,hi,stop,sj,ite_false]
        omega

/-- The only repeated mask is row displacement one. Its duplicate ordinal
is the first low-prefix mask, d+1. Thus every bucket stores one comparison
bit, independently of the requested row and cell. -/
theorem firstMask_eq (lane low : ℕ) (i : Fin (1+((lane+low)+(lane+low)))) :
    firstMask (fun j => (laneRow (offset (lane+low) j) : Row lane low)) i =
      decide (i.val≠(lane+low)+1) := by
  let d := lane+low
  change firstMask (fun j => (laneRow (offset d j) : Row lane low)) i = decide (i.val≠d+1)
  apply Bool.eq_iff_iff.mpr
  simp only [firstMask,decide_eq_true_eq]
  constructor
  · intro h bad
    have b := i.isLt
    have hd : 0<d := by omega
    let j : Fin (1+(d+d)) := ⟨1,by omega⟩
    apply h j (show j < i by change 1 < i.val; omega)
    apply Fin.ext
    change (offset d j).val=(offset d i).val
    rw [offset_nat,offset_nat]
    simp [j,bad,maskNat,show 1≤d by omega,show ¬d+1≤d by omega]
  · intro h j lt eq
    have raw : (offset d j).val=(offset d i).val :=
      congrArg (fun x : Row lane low => x.val) eq
    rw [offset_nat,offset_nat] at raw
    exact not_collision lt h raw

end ThreeFlat.Diagonal.TracePhysical

end OAI
