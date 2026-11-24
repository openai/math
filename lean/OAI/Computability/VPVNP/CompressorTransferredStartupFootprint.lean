import OAI.Computability.VPVNP.CompressorTransferredStartup

/-!
# Protected low memory across the eight native startup calls

Each source report preserves every cell below the descriptor workspace. The
linker writes its tag after each report, so every other low cell retains its
initial value at all nine entries. These statements use the reports of the
linked machines on the actual intermediate memories.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.TransferredStartup

open BurstRAM DescriptorSpace
open scoped Fin.CommRing

variable {w d B n a lanes steps : ℕ} {D : CalendarRows.Spec} {L : Layout}
variable {pub : Fin 11 → Word w} {tag : Word w} {m : Memory w}

/-- The native source of every transfer keeps the protected low memory. -/
theorem Runs.source_below (h : Runs D d L B n a lanes steps pub tag m) (i : Fin 8)
    (x : ℕ) (hx : x < L.base) :
    let t := trace D d L B n a lanes steps pub tag m
    after (t.entry tag m i.castSucc) (t.source i).events x = t.entry tag m i.castSucc x := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := h.frame.source_below x hx
  obtain ⟨h₄,h₅,h₆,h₇⟩ := h.calendar.source_below x hx
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄
  · exact h₅
  · exact h₆
  · exact h₇

/-- Every prefix, including the last transfer to the online worker, preserves
all low cells outside the pair tag. -/
theorem Runs.entry_below (h : Runs D d L B n a lanes steps pub tag m) (i : Fin 9)
    (x : ℕ) (hx : x < L.base) (ht : x ≠ tag.val) :
    (trace D d L B n a lanes steps pub tag m).entry tag m i x = m x := by
  let t := trace D d L B n a lanes steps pub tag m
  change t.entry tag m i x = m x
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [t.transfer,writeMemory,ite_eq_right ht]
    exact (h.source_below i x hx).trans ih

/-- The post-memory of any of the eight source reports also agrees with the
original input on every protected address. -/
theorem Runs.after_source_below (h : Runs D d L B n a lanes steps pub tag m) (i : Fin 8)
    (x : ℕ) (hx : x < L.base) (ht : x ≠ tag.val) :
    let t := trace D d L B n a lanes steps pub tag m
    after (t.entry tag m i.castSucc) (t.source i).events x = m x :=
  (h.source_below i x hx).trans (h.entry_below i.castSucc x hx ht)

end CompressorRecords.TransferredStartup

end VPVNP
end Computability
end OAI
