import OAI.Computability.VPVNP.PairShrinkSurvivingFrames
import OAI.Computability.VPVNP.PairNodeChildSlots

/-!
# Reassembling a surviving wire in private memory

Writing the numbered subdivisions at their frame offsets stores the entire
unsplit word, including when some subdivisions have width zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSurvivingBuffer

open BurstRAM Compression Compression.ShrinkPayload ShrinkSurvivingFrames
open private append_store from OAI.Computability.VPVNP.PairNodeChildSlots
open scoped Fin.CommRing

variable {w : ℕ}

private theorem slice_eq (b q : ℕ) (pos : 0 < q) (word : Fin b → Bool) (j : Fin q) :
    List.ofFn (sliceWords b q pos word j) =
      ((List.ofFn word).drop (start b q j)).take (splitWidth b q j) := by
  have h := end_le b q pos j
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · intro i hi _
    have bound : i < splitWidth b q j := by simpa using hi
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    change word (sliceBits b q pos ⟨j, ⟨i, bound⟩⟩) = word _
    exact congrArg word (Fin.ext (bit_position b q pos j ⟨i, bound⟩))

/-- The scan deposits every subdivision at its own frame offset. -/
def fill (b q : ℕ) (pos : 0 < q) (word : Fin b → Bool) (dst : ℕ)
    (mem : Word w → Word w) : Word w → Word w :=
  (List.finRange q).foldl (fun m j ↦ PrivateFields.storeBits (dst + start b q j)
    (List.ofFn (sliceWords b q pos word j)) m) mem

/-- The private memory after the scan equals a single write of the unsplit word. -/
theorem fill_eq (b q : ℕ) (pos : 0 < q) (word : Fin b → Bool) (dst : ℕ)
    (mem : Word w → Word w) :
    fill b q pos word dst mem = PrivateFields.storeBits dst (List.ofFn word) mem := by
  let ws := List.ofFn (splitWidth b q)
  let bs := List.ofFn word
  let put (m : Word w → Word w) (j : Fin q) := PrivateFields.storeBits (dst + start b q j)
    (List.ofFn (sliceWords b q pos word j)) m
  have part (n : ℕ) (hn : n ≤ q) :
      ((List.finRange q).take n).foldl put mem =
        PrivateFields.storeBits dst (bs.take (ws.take n).sum) mem := by
    induction n with
    | zero => simp [PrivateFields.storeBits]
    | succ n ih =>
      let j : Fin q := ⟨n, hn⟩
      have hj : n < (List.finRange q).length := by simp; omega
      have hw : n < ws.length := by simp [ws]; omega
      rw [List.take_succ_eq_append_getElem hj, List.foldl_append, ih (by omega),
        List.sum_take_succ _ _ hw]
      simp only [List.foldl_cons, List.foldl_nil, List.getElem_finRange, ws, List.getElem_ofFn]
      change PrivateFields.storeBits (dst + start b q j) (List.ofFn (sliceWords b q pos word j))
        (PrivateFields.storeBits dst (bs.take (start b q j)) mem) =
        PrivateFields.storeBits dst (bs.take (start b q j + splitWidth b q j)) mem
      rw [List.take_add, append_store, slice_eq]
      have he := end_le b q pos j
      simp [bs, Nat.min_eq_left (show start b q j ≤ b by omega)]
  have tot : ws.sum = b := List.sum_ofFn.trans (sum_splitWidth b q pos)
  simpa [fill, put, List.take_of_length_le (show (List.finRange q).length ≤ q by simp),
    List.take_of_length_le (show ws.length ≤ q by simp [ws]), tot,
    List.take_of_length_le (show bs.length ≤ b by simp [bs]), bs] using part q le_rfl

/-- Reading any position of the completed destination buffer returns its bit. -/
theorem fill_read (b q : ℕ) (pos : 0 < q) (word : Fin b → Bool) (dst : ℕ)
    (mem : Word w → Word w) (fit : dst + b ≤ 2 ^ w) (i : Fin b) :
    fill b q pos word dst mem ((dst + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w (word i) := by
  rw [fill_eq]
  simpa only [List.getElem_ofFn] using PrivateFields.storeBits_read dst (List.ofFn word) mem
    (by simpa using fit) ⟨i.val, by simp⟩

end PairSimulation.ShrinkSurvivingBuffer

end VPVNP
end Computability
end OAI
