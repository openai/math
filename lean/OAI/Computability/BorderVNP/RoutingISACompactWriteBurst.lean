import OAI.Computability.BorderVNP.RoutingISACallModel
import OAI.Computability.BorderVNP.RoutingISACompactWrite

/-! # Fetching the packed descriptor written by the outer RAM

A directory entry names the first written word and the actual compact word count.
When its pointer and length fields are separate from the output interval, both
survive the stores and the native burst delivers exactly the new descriptor words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactWrite

open VPVNP.BurstRAM CellDispatch Packing.Directory.ISA

variable {w : ℕ}

/-- A contiguous native read of a word interval recovers the data written into that interval. -/
theorem previous_putWords (m : Memory w) (dst : ℕ) (xs : List (Word w)) :
    TeamRAM.previous (putWords m dst xs) (.burst dst xs.length) = xs := by
  change List.ofFn (fun j : Fin xs.length => putWords m dst xs (dst+j.val)) = xs
  simp_rw [putWords_read]
  exact List.ofFn_getElem ..

/-- The actual physical argument read of the specified directory row yields the canonical
packed payload. Only the pointer and word count need to be outside the write interval. -/
theorem row_burst_written (f : Frame) (m : Memory w) (i dst : ℕ) (xs : List Bool)
    (pointer : (m (f.address i+1)).val = dst)
    (count : (m (f.address i+2)).val = (CompactFrame.pack w xs).length)
    (apart : ∀ a ∈ [f.address i+1, f.address i+2], a < dst ∨ dst+(CompactFrame.pack w xs).length ≤ a) :
    let mt := putWords m dst (CompactFrame.pack w xs)
    TeamRAM.previous mt (f.burst mt i) = CompactFrame.pack w xs := by
  dsimp only
  rw [Frame.burst, putWords_outside _ _ _ _ (apart _ (by simp)),
    putWords_outside _ _ _ _ (apart _ (by simp)), pointer, count, previous_putWords]

/-- A live writer execution prepares the argument consumed by the actual indexed cell
call, keeping the public frame and the row's recorded owner intact. -/
theorem writer_row {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {src dst : ℕ}
    (s : Bank w) (m : Memory w) (xs : List Bool) (hw : 0 < w)
    (width : readings s 2 = w) (base : readings s 3 = src) (length : readings s 4 = xs.length)
    (destination : readings s 5 = dst) (source : Source m src xs)
    (separate : Disjoint src xs.length dst (CompactFrame.pack w xs).length)
    (srcFit : src+xs.length ≤ 2^w) (dstFit : dst+(CompactFrame.pack w xs).length ≤ 2^w)
    (i : ℕ) (pointer : (m ((Frame.ofMemory pub m).address i+1)).val = dst)
    (count : (m ((Frame.ofMemory pub m).address i+2)).val = (CompactFrame.pack w xs).length)
    (apart : ∀ a ∈ [(pub 0).val,(pub 0).val+14,(pub 0).val+15,(Frame.ofMemory pub m).address i,
      (Frame.ofMemory pub m).address i+1,(Frame.ofMemory pub m).address i+2],
      a < dst ∨ dst+(CompactFrame.pack w xs).length ≤ a) :
    ∃ es t mt, Runs pub macros writer s m es t mt ∧
      traceCost es ≤ setup.slots+(step.slots+1)*xs.length+2 ∧
      Frame.ofMemory pub mt = Frame.ofMemory pub m ∧
      mt ((Frame.ofMemory pub mt).address i) = m ((Frame.ofMemory pub m).address i) ∧
      TeamRAM.previous mt ((Frame.ofMemory pub mt).burst mt i) = CompactFrame.pack w xs := by
  let f := Frame.ofMemory pub m
  let mt := putWords m dst (CompactFrame.pack w xs)
  have stay (a : ℕ) (ha : a ∈ [(pub 0).val,(pub 0).val+14,(pub 0).val+15,
      f.address i,f.address i+1,f.address i+2]) : mt a = m a :=
    putWords_outside _ _ _ _ (apart a ha)
  have frame : Frame.ofMemory pub mt = f := by
    unfold f Frame.ofMemory
    rw [stay _ (by simp), stay _ (by simp), stay _ (by simp)]
  obtain ⟨es,t,run,cost⟩ := writer_runs (pub := pub) (macros := macros) s m xs hw width
    base length destination source separate srcFit dstFit
  refine ⟨es,t,mt,run,cost,frame,?_,?_⟩
  · rw [frame]
    exact stay _ (by simp)
  · rw [frame]
    apply row_burst_written f m i dst xs pointer count
    intro a ha
    exact apart a (by simpa only [List.mem_cons,List.mem_nil_iff,or_false] using
      (Or.inr (Or.inr (Or.inr (Or.inr ha)))))

end RoutingISA.CompactWrite

end BorderVNP
end Computability
end OAI
