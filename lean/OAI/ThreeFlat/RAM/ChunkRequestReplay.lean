import OAI.ThreeFlat.RAM.ChunkRequestScan
import OAI.ThreeFlat.RAM.ChunkRequestCursor

namespace OAI
/-! # Semantics of a complete interval of chunk requests -/

namespace ThreeFlat.RAM.ChunkRequests

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical

variable {w p r k : ℕ}

theorem allRows_iff (m : Memory w) (tag oldBase newBase stride cursor : Word w) (n : ℕ) :
    allRows m tag oldBase newBase stride n cursor ↔
      ∀ i : Fin n, rowMatches m (readRow m (cursorAt stride i.val cursor)) tag oldBase newBase := by
  induction n generalizing cursor with
  | zero => simp [allRows]
  | succ n ih =>
    rw [allRows, Fin.forall_fin_succ, ih]
    rfl

/-- With a prepared starting pointer and no address wrap, the scan checks precisely
the finite set of four-word records belonging to this chunk. -/
theorem scan_flag_iff (D : Fin k → Word w) (R : Registers w k r) (L : Labels w k p)
    (n : ℕ) (c : Config w p r) (m : Memory w) :
    (scan D R L n c m).1.reg (R.slot 4) =
      if ∀ i : Fin n, rowMatches m
        (readRow m (cursorAt (c.reg (R.slot 5)) i.val (c.reg (R.slot 0))))
        (c.reg (R.slot 1)) (c.reg (R.slot 2)) (c.reg (R.slot 3))
      then c.reg (R.slot 4) else 0 := by
  rw [scan_flag]
  exact ite_congr (propext (allRows_iff ..)) (fun _ => rfl) (fun _ => rfl)

theorem allRows_prepared (m : Memory w) (tag oldBase newBase stride cursor : Word w) (n : ℕ) :
    allRows m tag oldBase newBase stride n cursor ↔
      ∀ row ∈ preparedRows m cursor stride n, rowMatches m row tag oldBase newBase := by
  rw [allRows_iff, preparedRows, List.forall_mem_ofFn_iff]

end ThreeFlat.RAM.ChunkRequests

end OAI
