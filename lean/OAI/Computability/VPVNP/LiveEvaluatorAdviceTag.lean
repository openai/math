import OAI.Computability.VPVNP.LiveEvaluatorAdvicePrepared

/-!
# The stage tag and the evaluator's advice banks

The linked program keeps its stage tag below the advice sources, destination
arrays and operand frames. Updating the tag therefore commutes with every
packed row write and with publication of the four operand frames.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.Advice

open BurstRAM LiveEvaluatorAdviceFrames LiveEvaluatorAdviceBanks PrimedStackRAM

variable {w : ℕ}

theorem write_tag_twice (m : Memory w) (tag v v' : Word w) :
    writeMemory (writeMemory m tag v) tag v' = writeMemory m tag v' := by
  funext k
  by_cases he : k = tag.val <;> simp [writeMemory, he]

/-- A packer's source array agrees before and after a lower tag write. -/
theorem packSource_write_tag (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w) (tag v : Word w)
    (ht : tag.val < (pub 0).val) :
    PackSource pub raw (writeMemory m tag v) ↔ PackSource pub raw m := by
  have h (i : ℕ) : (pub 0).val + i ≠ tag.val := by omega
  simp only [PackSource, writeMemory, h, ite_false]

/-- Any prefix of a packing sweep commutes with a write below its destination bank. -/
theorem packMemory_write_tag (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w)
    (tag v : Word w) (i : ℕ) (ht : tag.val < (pub 1).val) :
    packMemory pub raw (writeMemory m tag v) i = writeMemory (packMemory pub raw m i) tag v := by
  funext k
  by_cases he : k = tag.val
  · subst k
    rw [packMemory_outside _ _ _ _ _ (.inl ht)]
    simp [writeMemory]
  · simp [packMemory, writeMemory, he]

theorem actualLength_write_tag (fp : FramePub w) (m : Memory w) (tag v : Word w)
    (ht : tag.val < (fp 3).val) (hf : (fp 3).val+22 < 2^w) :
    actualLength fp (writeMemory m tag v) = actualLength fp m := by
  rw [actualLength_at fp _ hf, actualLength_at fp _ hf, writeMemory, ite_eq_right (by omega)]

theorem prefixFrame_write_tag (fp : FramePub w) (m : Memory w) (tag v : Word w)
    (ht : tag.val < (fp 3).val) (hf : (fp 3).val+22 < 2^w) :
    prefixFrame fp (writeMemory m tag v) = prefixFrame fp m := by
  simp only [prefixFrame, prefixRows, actualLength_write_tag fp m tag v ht hf]

/-- The frame builder reads the same validated length and writes the same
operand words, leaving the independent stage tag at the supplied value. -/
theorem published_write_tag (fp : FramePub w) (m : Memory w) (tag v : Word w)
    (ht : tag.val < (fp 3).val) (hw : 0 < w) (hf : (fp 3).val+22 < 2^w) :
    published fp (writeMemory m tag v) = writeMemory (published fp m) tag v := by
  funext k
  by_cases hk : k < (fp 3).val ∨ (fp 3).val + 22 ≤ k
  · rw [published_outside _ _ hw hf.le _ hk]
    by_cases he : k = tag.val
    · simp [writeMemory, he]
    · simp [writeMemory, he, published_outside _ _ hw hf.le _ hk]
  · let r := ready fp (fun _ => 0) m
    have he : ready fp (fun _ => 0) (writeMemory m tag v) = r :=
      ready_congr_length fp _ _ _ (actualLength_write_tag fp m tag v ht hf)
    have h1 : (r 1).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')
    have hfit : (r 22).val + slots.length ≤ 2^w := hf.le
    let j := k - (fp 3).val
    have hj : j < slots.length := by change k - (fp 3).val < 22; omega
    have hkj : k = (r 22).val+j := by change k = (fp 3).val+(k-(fp 3).val); omega
    have hne : k ≠ tag.val := by omega
    rw [published, he, writeMemory, ite_eq_right hne, published, hkj]
    rw [frameMemory_at slots r _ h1 hfit (by decide) j hj, frameMemory_at slots r m h1 hfit (by decide) j hj,
      ← hkj, writeMemory, ite_eq_right hne]

end LiveProgram.Advice

end VPVNP
end Computability
end OAI
