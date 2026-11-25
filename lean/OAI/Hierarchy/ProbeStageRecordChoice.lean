import OAI.Hierarchy.ProbeStageRecord
import OAI.Hierarchy.ProbeStageFastRefinement
import OAI.Hierarchy.ProbeStageFallbackRefinement

namespace OAI
/-! # The physical record chooses precisely its mask-greedy color -/

namespace Hierarchy.ProbeStage.Record
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing

/-- Read the actual literal string from the prepared row-offset cell and its immutable bank. -/
def stringWord {w : ℕ} (a : Advice) (s : Scratch) (m : Memory w) (i : Word w) : Word w :=
  m ((a.strings:Word w)+m (s.stringOffset:Word w).val+i).val

/-- In the actual output of the packed-bit scan, `i` may equal the sentinel. -/
def bootChoice {w : ℕ} (a : Advice) (s : Scratch) (m : Memory w) :=
  let i := m (s.bit:Word w).val
  if i=(a.length:Word w) then (a.degree:Word w) else stringWord a s m i

def bootCount {w : ℕ} (a : Advice) (s : Scratch) (m : Memory w) :=
  if m (s.bit:Word w).val=(a.length:Word w) then (a.degree:Word w) else (0:Word w)

theorem start_image {w : ℕ} (a : Advice) (r : Row) (s : Scratch) (m : Memory w)
    (disj : (s.bit:Word w).val≠r.chosen) :
    writes (start a r s) m=Function.update (Function.update m r.chosen (bootChoice a s m)) s.remaining (bootCount a s m) := by
  simp only [writes,start,RankUpdate.assign,WordStore.value,miss,RankUpdate.cell,Formula.value,Comparison.test,
    beq_iff_eq,BinaryOp.eval,bootChoice,bootCount,stringWord]
  let b := Function.update m r.chosen (bootChoice a s m)
  change Function.update b s.remaining (if b (s.bit:Word w).val=(a.length:Word w) then (a.degree:Word w) else 0)=_
  rw [show b (s.bit:Word w).val=m (s.bit:Word w).val from Function.update_of_ne disj _ _]
  rfl

/-- The packed chunks and the true words on the current string encode the actual two sets
of saturated endpoint colors. The `possible` condition is exactly the pair of counter reads. -/
structure ChoiceInput {w B ℓ : ℕ} (a : Advice) (r : Row) (s : Scratch) (m : Memory w)
    (row : Fin ℓ → Fin B) (L R good : Finset (Fin B)) : Prop where
  degree : a.degree=B
  length : a.length=ℓ
  pos : 0<a.width
  room : ℓ≤a.chunks*a.width
  avail : ∀ c,c∈good ↔ c∉L∪R
  packed : FastField.Represents (find a s) (writes (prepare a r s) m) row L R
  string : ∀ i : Fin ℓ,
    stringWord a s (FastField.image (find a s) (writes (prepare a r s) m)) (i.val:Word w)=((row i).val:Word w)
  counters : ∀ c : Fin B, Fallback.possible (fallback a r s) (scanInput a s r m) (c.val:Word w) ↔ c∈good
  frozen : ∀ c : Fin B, Fallback.Separate (fallback a r s) (scanInput a s r m) (c.val:Word w)
  degreeFit : B<2^w
  lengthFit : ℓ<2^w
  bitFit : s.bit<2^w
  chosenFit : r.chosen<2^w
  remainingFit : s.remaining<2^w
  bitChosen : s.bit ≠ r.chosen
  countChosen : s.remaining ≠ r.chosen

/-- Both cost and output are identified on the *same actual memory trace*. -/
theorem physical_choice {w B ℓ : ℕ} (a : Advice) (s : Scratch) (r : Row) (m : Memory w)
    (row : Fin ℓ → Fin B) (L R good : Finset (Fin B)) (posB : 0<B) (available : good.Nonempty)
    (input : ChoiceInput a r s m row L R good) :
    scans a s r m=(if (freeBits row good).Nonempty then 0 else B) ∧
      leftInput a s r m r.chosen=((maskedChoice posB row good).val:Word w) := by
  let bits := freeBits row good
  let prepared := writes (prepare a r s) m
  let fast := FastField.image (find a s) prepared
  let scan := scanInput a s r m
  let idx := PackedMask.firstIndex row good
  have eqBit : fast (s.bit:Word w).val=(idx:Word w) := by
    simp only [fast,FastField.image,Fin.val_cast_of_lt input.bitFit,find,Function.update_self]
    exact FastField.machine_choice (find a s) prepared row L R good input.packed input.length input.pos input.room input.avail
  have ready : scan=Function.update (Function.update fast r.chosen (bootChoice a s fast)) s.remaining (bootCount a s fast) :=
    start_image a r s fast (by simpa only [Fin.val_cast_of_lt input.bitFit] using input.bitChosen)
  have initial : scan r.chosen=bootChoice a s fast := by rw [ready,Function.update_of_ne (Ne.symm input.countChosen),Function.update_self]
  have count : scans a s r m=(bootCount a s fast).val := by
    change (scan (s.remaining:Word w).val).val=_
    rw [Fin.val_cast_of_lt input.remainingFit,ready,Function.update_self]
  by_cases h : bits.Nonempty
  · let i := bits.min' h
    have hi : idx=i.val := by simp only [idx,PackedMask.firstIndex,← show bits=freeBits row good from rfl,dite_eq_left h,i]
    have diff : (idx:Word w)≠(a.length:Word w) := by
      intro e
      rw [hi,input.length,Fin.ext_iff,Fin.val_cast_of_lt (i.isLt.trans input.lengthFit),Fin.val_cast_of_lt input.lengthFit] at e
      omega
    have zero : scans a s r m=0 := by rw [count,bootCount,eqBit,ite_eq_right diff];rfl
    refine ⟨by simpa [bits,h] using zero,?_⟩
    change WordStore.down (s.remaining:Word w) (Fallback.next (fallback a r s)) (scans a s r m) scan r.chosen=_
    rw [zero,WordStore.down,initial,bootChoice,eqBit,ite_eq_right diff,hi]
    rw [input.string i]
    simp [maskedChoice,←show bits=freeBits row good from rfl,h,i]
  · have hi : idx=ℓ := by simp only [idx,PackedMask.firstIndex,← show bits=freeBits row good from rfl,dite_eq_right h]
    have same : (idx:Word w)=(a.length:Word w) := by rw [hi,input.length]
    have sz : scans a s r m=B := by rw [count,bootCount,eqBit,ite_eq_left same,input.degree,Fin.val_cast_of_lt input.degreeFit]
    refine ⟨by simpa [bits,h] using sz,?_⟩
    let c := good.min' available
    let sF := fallback a r s
    have hN : (scan (sF.remaining:Word w).val).val = B := sz
    have arm := Fallback.chosen_value sF scan input.chosenFit
      (by simpa [sF,fallback,Fin.val_cast_of_lt input.remainingFit] using input.countChosen)
      (fun i hi => input.frozen ⟨i,by omega⟩)
    change Fallback.image sF scan sF.chosen = _
    rw [arm,hN]
    have hit : decide (Fallback.possible sF scan (c.val:Word w))=true :=
      decide_eq_true ((input.counters c).mpr (Finset.min'_mem good available))
    have prev (j : ℕ) (hj : j<c.val) : decide (Fallback.possible sF scan (j:Word w))=false := by
      apply decide_eq_false
      intro hp
      have hh := Finset.min'_le good ⟨j,hj.trans c.isLt⟩ ((input.counters ⟨j,hj.trans c.isLt⟩).mp hp)
      exact hj.not_ge hh
    rw [Fallback.pick_hit _ _ _ c.val c.isLt hit prev]
    simp [maskedChoice,←show bits=freeBits row good from rfl,h,Greedy.first,available,c]

end Hierarchy.ProbeStage.Record

end OAI
