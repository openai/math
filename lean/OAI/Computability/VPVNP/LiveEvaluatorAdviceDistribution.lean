import OAI.Computability.VPVNP.LiveHeaderAdvice
import OAI.Computability.VPVNP.LiveEvaluatorAdvicePackSweep

/-!
# The distributed advice used to initialize the evaluator

The copied header array carries the raw bit length as one little-endian word,
the raw payload in a padded region, and the ordinal lookup table. These are
precisely the three source regions of the native packing stages. The ordinal
region begins at the end of the allocated payload capacity, independently of
the actual raw length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorAdviceBanks

open BurstRAM CutSchedule ChainAssignments
open scoped Fin.CommRing

variable {w ordW t a d h Δ : ℕ}

/-- Little-endian length field of the raw evaluator input. -/
def lengthBits (w : ℕ) (raw : List Bool) : List Bool := wordBits (Fin.ofNat (2^w) raw.length : Word w)

/-- Little-endian, row-major ordinal table. -/
def ordinalBits (values : Fin t → Word ordW) := List.ofFn (RAMSerialization.arrayBits t ordW values)

/-- Complete advice layout with the two allocated padding regions. -/
def distribution (w capacity : ℕ) (raw : List Bool) (values : Fin t → Word ordW) (padding : ℕ) : List Bool :=
  lengthBits w raw ++ (raw ++ (List.replicate (capacity-raw.length) false ++
    (ordinalBits values ++ List.replicate padding false)))

@[simp] theorem length_lengthBits (w : ℕ) (raw : List Bool) : (lengthBits w raw).length = w := by
  simp [lengthBits]

@[simp] theorem length_ordinalBits (values : Fin t → Word ordW) :
    (ordinalBits values).length = t*ordW := by simp [ordinalBits]

theorem distribution_length (capacity padding : ℕ) (raw : List Bool) (values : Fin t → Word ordW)
    (hfit : raw.length ≤ capacity) :
    (distribution w capacity raw values padding).length = w + capacity + t*ordW + padding := by
  simp [distribution]
  omega

/-- A copied header array supplies every native word read of any contiguous
sublist, including a zero-length sublist. -/
theorem packSource_of_slice {m : Memory w} {advice : Bits a} {base : ℕ}
    (copied : ∀ i : Fin a, m (base+i.val) = PrimedInputRAM.encodeBit w (advice i))
    (pub : Fin 5 → Word w) (pre chunk tail : List Bool)
    (htape : List.ofFn advice = pre ++ (chunk ++ tail)) (hbase : (pub 0).val = base + pre.length) :
    PackSource pub chunk m := by
  intro j hj
  have hlen := congrArg List.length htape
  simp only [List.length_ofFn, List.length_append] at hlen
  let i : Fin a := ⟨pre.length + j, by omega⟩
  have he := congrArg (fun xs : List Bool => xs[pre.length+j]?) htape
  change (List.ofFn advice)[pre.length+j]? = (pre ++ (chunk ++ tail))[pre.length+j]? at he
  rw [List.getElem?_ofFn, dite_eq_left i.isLt, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left hj] at he
  have hbit : advice i = chunk[j]?.getD false := by rw [← he]; rfl
  simpa only [i, hbase, Nat.add_assoc, ← hbit] using copied i

/-- The copied advice bits suffice to identify the three source regions. -/
theorem distribution_sources_of_copied {advice : Bits a}
    {base capacity padding : ℕ} {m : Memory w} {raw : List Bool} {values : Fin t → Word ordW}
    (copied : ∀ i : Fin a, m (base+i.val) = PrimedInputRAM.encodeBit w (advice i))
    (lenPub rawPub ordPub : Fin 5 → Word w)
    (htape : List.ofFn advice = distribution w capacity raw values padding)
    (hraw : raw.length ≤ capacity) (hl : (lenPub 0).val = base)
    (hr : (rawPub 0).val = base+w) (ho : (ordPub 0).val = base+w+capacity) :
    PackSource lenPub (lengthBits w raw) m ∧ PackSource rawPub raw m ∧ PackSource ordPub (ordinalBits values) m := by
  have h₁ := packSource_of_slice copied lenPub [] (lengthBits w raw)
    (raw ++ (List.replicate (capacity-raw.length) false ++ (ordinalBits values ++ List.replicate padding false)))
    htape hl
  have h₂ := packSource_of_slice copied rawPub (lengthBits w raw) raw
    (List.replicate (capacity-raw.length) false ++ (ordinalBits values ++ List.replicate padding false))
    htape (by simpa using hr)
  let pre := lengthBits w raw ++ (raw ++ List.replicate (capacity-raw.length) false)
  have hpre : pre.length = w+capacity := by simp [pre]; omega
  have h₃ := packSource_of_slice copied ordPub pre (ordinalBits values) (List.replicate padding false)
    (by simpa [pre, distribution, List.append_assoc] using htape) (by rw [hpre, ho, Nat.add_assoc])
  exact ⟨h₁, h₂, h₃⟩

/-- The physical header copy supplies exactly the input required by each
native packing call. The source of the ordinal table is fixed by capacity. -/
theorem distribution_sources {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ} {g : Fin (2^(h+1))}
    {base capacity padding : ℕ} {m₀ m : Memory w} {raw : List Bool} {values : Fin t → Word ordW}
    (img : LiveHeader.AdviceImage (d := d) hw advice cuts g base m₀ m)
    (lenPub rawPub ordPub : Fin 5 → Word w)
    (htape : List.ofFn advice = distribution w capacity raw values padding)
    (hraw : raw.length ≤ capacity) (hl : (lenPub 0).val = base)
    (hr : (rawPub 0).val = base+w) (ho : (ordPub 0).val = base+w+capacity) :
    PackSource lenPub (lengthBits w raw) m ∧ PackSource rawPub raw m ∧ PackSource ordPub (ordinalBits values) m :=
  distribution_sources_of_copied img.copied lenPub rawPub ordPub htape hraw hl hr ho

/-- Packing the first full word recovers the actual raw length without truncation. -/
theorem packed_length (raw : List Bool) (hfit : raw.length < 2^w) :
    (packedWord w w (lengthBits w raw) 0).val = raw.length := by
  have he : packedWord w w (lengthBits w raw) 0 = Fin.ofNat (2^w) raw.length := by
    apply (RAMSerialization.wordBits w).injective
    funext i
    simp [packedWord, packedPrefix, lengthBits, wordBits]
  rw [he, Fin.val_ofNat, Nat.mod_eq_of_lt hfit]

/-- The native length sweep returns that length in the designated word. -/
theorem packMemory_length (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w)
    (hwidth : (pub 2).val = w) (hrows : 0 < (pub 4).val) (hfit : raw.length < 2^w) :
    (packMemory pub (lengthBits w raw) m (packCalls pub) (pub 1).val).val = raw.length := by
  have he := packMemory_full pub (lengthBits w raw) m 0 hrows
  rw [Nat.add_zero, hwidth] at he
  rw [he]
  exact packed_length raw hfit

/-- Each full-width raw payload row is the packed input word of initialization. -/
theorem packMemory_raw (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w)
    (hwidth : (pub 2).val = w) (j : ℕ) (hj : j < (pub 4).val) :
    packMemory pub raw m (packCalls pub) ((pub 1).val+j) = LiveEvaluatorInitialize.inputWord w raw j := by
  rw [packMemory_full pub raw m j hj, hwidth]
  exact packedWord_inputWord w raw j

/-- Each ordinal keeps its source value when extended to the working word width. -/
theorem packMemory_ordinal (pub : Fin 5 → Word w) (values : Fin t → Word ordW) (m : Memory w)
    (hwidth : (pub 2).val = ordW) (hw : ordW ≤ w) (hrows : t ≤ (pub 4).val) (j : Fin t) :
    packMemory pub (ordinalBits values) m (packCalls pub) ((pub 1).val+j.val) =
      (values j).castLE (Nat.pow_le_pow_right (by decide : 0 < 2) hw) := by
  rw [packMemory_full pub _ m _ (j.isLt.trans_le hrows), hwidth]
  exact packedWord_arrayBits hw values j

/-- Source bits for a later packing stage remain available after a disjoint
earlier stage, including after any partial prefix of its execution. -/
theorem PackSource.after_other_bank {m : Memory w} {pub : Fin 5 → Word w} {bits : List Bool}
    (hs : PackSource pub bits m) (other : Fin 5 → Word w) (raw : List Bool) (i : ℕ)
    (sep : (pub 0).val + bits.length ≤ (other 1).val ∨
      (other 1).val + (other 4).val ≤ (pub 0).val) :
    PackSource pub bits (packMemory other raw m i) := by
  intro j hj
  rw [packMemory_outside other raw m i _ (by omega), hs j hj]

end LiveEvaluatorAdviceBanks

end VPVNP
end Computability
end OAI
