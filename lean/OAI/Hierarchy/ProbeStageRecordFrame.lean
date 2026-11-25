import OAI.Hierarchy.ProbeStageRecordPrepare
import OAI.Hierarchy.ProbeStageFallbackRefinement

namespace OAI
/-! # Physical frame before the two endpoint commits -/

namespace Hierarchy.ProbeStage.Record
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

/-- The candidate search and optional fallback may modify only the bit result, chosen color and
loop counter. They preserve all six prepared block/string pointers. -/
theorem left_prepared {w : ℕ} (a : Advice) (s : Scratch) (r : Row) (m : Memory w) (x : ℕ)
    (bit : x≠s.bit) (chosen : x≠r.chosen) (count : x≠s.remaining) (fit : s.remaining<2^w) :
    leftInput a s r m x=writes (prepare a r s) m x := by
  let mem := scanInput a s r m
  let cfg := fallback a r s
  have fr := Fallback.frame cfg (mem (cfg.remaining:Word w).val).val mem x
    (by simpa [cfg,fallback,Fin.val_cast_of_lt fit] using count) chosen
  change leftInput a s r m x=mem x at fr
  rw [fr]
  change writes (start a r s) _ x=_
  rw [writes_frame]
  · exact Function.update_of_ne bit _ _
  · intro z hz
    simp only [start,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> assumption

theorem left_unchanged {w : ℕ} (a : Advice) (s : Scratch) (r : Row) (m : Memory w) (x : ℕ)
    (bit : x≠s.bit) (chosen : x≠r.chosen) (count : x≠s.remaining) (fit : s.remaining<2^w)
    (outside : ∀ d∈dirs a r s,x≠d.dst) : leftInput a s r m x=m x := by
  rw [left_prepared _ _ _ _ _ bit chosen count fit,prepare_eq,writes_frame]
  intro d hd
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
  exact outside e he

end Hierarchy.ProbeStage.Record

end OAI
