import OAI.Computability.VPVNP.LiveConfigGather
import OAI.Computability.VPVNP.LiveEvaluatorRAMImage
import OAI.Computability.VPVNP.PrimedInputRAMChoices
import OAI.Computability.VPVNP.RAMChain

/-!
# Memory image of gathered configuration words

A contiguous cut holds one zero-or-one word per bit. Each scheduled gather
call reconstructs one little-endian field word in a disjoint bank. Replaying
the reports installs the checked decoder's entire array of words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveConfigGather

open BurstRAM PrimedInputRAM RAMSerialization
open scoped Fin.CommRing

variable {k w extra M : ℕ}

/-- Every cut bit occupies one full machine word. -/
def ArrayBitImage (m : Memory w) (base : Word w) (bits : Fin (k*w) → Bool) : Prop :=
  ∀ i, m (base.val + i.val) = ((bits i).toNat : Word w)

private theorem offset_val (base : Word w) (n : ℕ) (h : base.val + n < 2 ^ w) :
    (base + (n : Word w)).val = base.val + n := by
  rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt h]

/-- Restricting a complete cut to a single word gives the exact input image
expected by the native gathering call. -/
theorem bitImage_word {pub : Pub → Word w} {m : Memory w} {bits : Fin (k*w) → Bool}
    (img : ArrayBitImage m (pub 0) bits) (srcFit : (pub 0).val + k*w ≤ 2^w)
    (hp : (pub 2).val = w) (i : Fin k) :
    BitImage m (pub 0 + (i.val : Word w) * pub 2) ((arrayBits k w).symm bits i) := by
  intro j
  let f := finProdFinEquiv (i,j)
  have hf : f.val = i.val * w + j.val := by simp [f, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  have hw : pub 2 = (w : Word w) :=
    (Fin.cast_val_eq_self (pub 2)).symm.trans (congrArg (fun n : ℕ => (n : Word w)) hp)
  have ha : pub 0 + (i.val : Word w) * pub 2 + (j.val : Word w) = pub 0 + (f.val : Word w) := by
    rw [hw, hf]
    push_cast
    ring
  rw [ha, offset_val _ _ (by have := f.isLt; omega), img]
  have hb := arrayBits_at ((arrayBits k w).symm bits) i j
  rw [Equiv.apply_symm_apply] at hb
  rw [← hb]

/-- A write to the disjoint destination bank leaves the complete source bit
image available to every later cursor. -/
theorem ArrayBitImage.after_write {m : Memory w} {base dst : Word w} {bits : Fin (k*w) → Bool}
    (img : ArrayBitImage m base bits) (destFit : dst.val + k ≤ 2^w)
    (hsep : base.val + k*w ≤ dst.val ∨ dst.val + k ≤ base.val) (i : Fin k) (v : Word w) :
    ArrayBitImage (writeMemory m (dst + (i.val : Word w)) v) base bits := by
  intro j
  have hn : base.val + j.val ≠ (dst + (i.val : Word w)).val := by
    rw [offset_val dst i.val (by have := i.isLt; omega)]
    have := i.isLt
    have := j.isLt
    omega
  simpa [writeMemory, hn] using img j

/-- The ordered destination writes from the actual native reports. -/
theorem replay_reports (pub : Pub → Word w) (fit : (pub 1).val + k ≤ 2^w)
    (rs : PrimedStackRAM.Regs w 32) (vals : Fin k → Word w) (cells : List (Fin k)) (m : Memory w) :
    after m (eventLog (cells.map fun i => report pub (i.val : Word w) rs (vals i))) =
      store (scratchAddress (pub 1).val fit) vals cells m := by
  induction cells generalizing m with
  | nil => rfl
  | cons i cells ih =>
    let r := report pub (i.val : Word w) rs (vals i)
    change after m (r.events ++ eventLog _) = store _ _ cells (writeMemory m _ _)
    have hd : pub 1 + (i.val : Word w) = scratchAddress (pub 1).val fit i :=
      Fin.ext (offset_val _ _ (by have := i.isLt; omega))
    rw [show after m (r.events ++ eventLog _) = after (after m r.events) (eventLog _) from List.foldl_append,
      show after m r.events = _ from report_memory pub _ rs m (vals i), hd, ih]

/-- Packed words after all destinations have been visited. -/
def gathered (dst : Word w) (fit : dst.val + k ≤ 2^w) (bits : Fin (k*w) → Bool) (m : Memory w) : Memory w :=
  store (scratchAddress dst.val fit) ((arrayBits k w).symm bits) (List.finRange k) m

theorem gathered_at (dst : Word w) (fit : dst.val + k ≤ 2^w) (bits : Fin (k*w) → Bool)
    (m : Memory w) (i : Fin k) :
    gathered dst fit bits m (dst + (i.val : Word w)).val = (arrayBits k w).symm bits i := by
  rw [offset_val _ _ (by have := i.isLt; omega)]
  exact store_at (scratchAddress dst.val fit) _ _ m (List.mem_finRange i)

theorem gathered_outside (dst : Word w) (fit : dst.val + k ≤ 2^w) (bits : Fin (k*w) → Bool)
    (m : Memory w) (j : ℕ) (hj : j < dst.val ∨ dst.val + k ≤ j) :
    gathered dst fit bits m j = m j := by
  apply store_outside
  intro i _
  change j ≠ dst.val + i.val
  have := i.isLt
  omega

open LiveEvaluatorEncoding (fieldWords stateField firstField secondField words format)
open LiveEvaluatorRAM (ConfigAt)

/-- The memory image characterizes every field of the checked decoder,
including every padding cell of a halt. -/
theorem configAt_iff_words (hw : 2 ≤ w) (hs : extra+2 ≤ 2^w) (dst : Word w) (m : Memory w)
    (c : LiveEvaluatorEncoding.Code extra M) :
    ConfigAt m dst c ↔ ∀ f, m (dst + (f.val : Word w)).val = (format hw hs).words c f := by
  refine ⟨?_, LiveEvaluatorRAM.configAt_of_words hw hs c⟩
  intro hc f
  apply Fin.ext
  change (m (dst + (f.val : Word w)).val).val = (words hw hs c f).val
  by_cases h0 : f.val = 0
  · have he : f = stateField M := Fin.ext h0
    rw [he, LiveEvaluatorEncoding.words_state]
    simpa [stateField] using hc.state
  by_cases hf : f.val < 1 + (2*M+1)
  · let i : Fin (2*M+1) := ⟨f.val - 1, by omega⟩
    have he : f = firstField i := by apply Fin.ext; change f.val = 1 + (f.val - 1); omega
    rw [he, LiveEvaluatorEncoding.words_first]
    simpa only [firstField, Nat.cast_add, Nat.cast_one, ← add_assoc] using hc.first i
  · have hlen : f.val < 1 + (2*M+1) + (2*M+1) := f.isLt
    let i : Fin (2*M+1) := ⟨f.val - (1+(2*M+1)), by omega⟩
    have he : f = secondField i := by
      apply Fin.ext; change f.val = 1 + (2*M+1) + (f.val - (1+(2*M+1))); omega
    rw [he, LiveEvaluatorEncoding.words_second]
    change (m (dst + ((1 + (2*M+1) + i.val : ℕ) : Word w)).val).val = _
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, ← add_assoc, ← add_assoc]
    exact hc.second i

/-- For arbitrary cut bits, the packed memory is the image of a configuration
exactly when the checked binary decoder returns that configuration. -/
theorem gathered_configAt_iff (hw : 2 ≤ w) (hs : extra+2 ≤ 2^w) (dst : Word w)
    (fit : dst.val + fieldWords M ≤ 2^w) (bits : Fin (fieldWords M*w) → Bool) (m : Memory w)
    (c : LiveEvaluatorEncoding.Code extra M) :
    ConfigAt (gathered dst fit bits m) dst c ↔ (format hw hs).decode bits = some c := by
  rw [configAt_iff_words hw hs, LiveEvaluatorEncoding.decode_iff]
  simp only [gathered_at]
  change (∀ f, (arrayBits (fieldWords M) w).symm bits f = (format hw hs).words c f) ↔
    bits = arrayBits (fieldWords M) w ((format hw hs).words c)
  exact ⟨fun h => (Equiv.symm_apply_eq _).mp (funext h),
    fun h => congrFun ((Equiv.symm_apply_eq _).mpr h)⟩

/-- A malformed cut cannot realize any canonical configuration in the destination bank. -/
theorem gathered_decode_none_iff (hw : 2 ≤ w) (hs : extra+2 ≤ 2^w) (dst : Word w)
    (fit : dst.val + fieldWords M ≤ 2^w) (bits : Fin (fieldWords M*w) → Bool) (m : Memory w) :
    (format hw hs).decode bits = none ↔
      ¬ ∃ c : LiveEvaluatorEncoding.Code extra M, ConfigAt (gathered dst fit bits m) dst c := by
  constructor
  · rintro h ⟨c, hc⟩
    have he := (gathered_configAt_iff hw hs dst fit bits m c).mp hc
    rw [h] at he
    cases he
  · intro h
    cases he : (format hw hs).decode bits with
    | none => rfl
    | some c => exact (h ⟨c, (gathered_configAt_iff hw hs dst fit bits m c).mpr he⟩).elim

end LiveConfigGather

end VPVNP
end Computability
end OAI
