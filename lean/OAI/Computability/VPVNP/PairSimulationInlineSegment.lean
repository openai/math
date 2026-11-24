import OAI.Computability.VPVNP.PairSimulationInlinePrefix
import OAI.Computability.VPVNP.PairVertexImage

/-!
# Installing a lowered native table in the final-vertex image

Accepting source exits point directly to the caller's continuation. A failing source
exit addresses a native rejecting opcode. The interior of each block is the width-two
static-bank compiler, widened to the literal format of the enclosing vertex image.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.InlinePublic

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {p r k P R K w : ℕ}

/-- The source table's allocated code and register ranges. -/
abbrev blockCount (T : Template p r k) (bank : Fin k → ℕ) := p * (capacity T bank + 3)

private def success {v : ℕ} : Instr v p r k → Bool
  | .accept => true
  | _ => false

/-- Every successful source exit uses the caller's continuation label. -/
def linkedPlacement (T : Template p r k) (bank : Fin k → ℕ)
    (loc : Fin (blockCount T bank) → Fin P) (reg : Fin (r + 2) ↪ Fin R) (done : Fin P) :
    Placement (capacity T bank) p r P R :=
  (embedding (capacity T bank) p r loc reg).withExits fun j =>
    if success (T.code j) then some done else none

/-- Every register outside the physical local bank belongs to the caller frame. -/
theorem linked_privateReg (T : Template p r k) (bank : Fin k → ℕ)
    (loc : Fin (blockCount T bank) → Fin P) (reg : Fin (r + 2) ↪ Fin R) (done : Fin P)
    {i : Fin R} (outside : i ∉ Set.range reg) :
    (linkedPlacement T bank loc reg done).privateReg i :=
  ⟨fun h => outside ⟨_, h.symm⟩, fun h => outside ⟨_, h.symm⟩,
    fun ⟨_, h⟩ => outside ⟨_, h⟩⟩

theorem success_entry (T : Template p r k) (bank : Fin k → ℕ)
    (loc : Fin (blockCount T bank) → Fin P) (reg : Fin (r + 2) ↪ Fin R) (done : Fin P)
    {j : Fin p} (hj : T.code j = .accept) :
    (linkedPlacement T bank loc reg done).entry j = done := by
  simp [linkedPlacement, hj, success]

private theorem code_at {T : Template p r k} {bank : Fin k → ℕ}
    {loc : Fin (blockCount T bank) → Fin P} {reg : Fin (r + 2) ↪ Fin R} {done : Fin P}
    {j : Fin p} (hn : success (T.code j) = false) (t : Fin (capacity T bank + 3)) :
    (linkedPlacement T bank loc reg done).pc j t = loc (finProdFinEquiv (j, t)) := by
  by_cases he : t = 0
  · subst t
    simp [linkedPlacement, Placement.withExits, hn, Placement.entry, embedding, canonical]
  · simp [linkedPlacement, Placement.withExits, he, embedding, canonical]

/-- The table rows are physically consecutive in the local label bank. The unreachable
accept rows also transfer to the caller when entered directly. -/
def linkedRows (T : Template p r k) (bank : Fin k → ℕ)
    (loc : Fin (blockCount T bank) → Fin P) (reg : Fin (r + 2) ↪ Fin R) (done : Fin P)
    (a : Fin (blockCount T bank)) : Instr 2 P R K :=
  let jt := finProdFinEquiv.symm a
  let D := linkedPlacement T bank loc reg done
  match T.code jt.1 with
  | .accept => .jumpEq D.acc D.acc done done
  | .reject => .reject
  | _ => row T bank D jt.1 jt.2

/-- Every nonterminal row of the physically installed array satisfies the native
prefix theorem's code hypothesis. -/
theorem contains_linkedRows (T : Template p r k) (bank : Fin k → ℕ)
    (loc : Fin (blockCount T bank) → Fin P) (reg : Fin (r + 2) ↪ Fin R) (done : Fin P)
    (M : Machine w P R K)
    (installed : ∀ a, M.code (loc a) = (linkedRows T bank loc reg done a).resize w)
    (j : Fin p) (live : continues (T.code j) = true) :
    ContainsAt M T bank (linkedPlacement T bank loc reg done) j := by
  have hs : success (T.code j) = false := by
    cases he : T.code j <;> first | rfl | simp [he, continues] at live
  intro t
  rw [code_at hs, installed]
  simp only [linkedRows, Equiv.symm_apply_apply]
  cases he : T.code j <;> first | rfl | simp [he, continues] at live

theorem rejecting_entry (T : Template p r k) (bank : Fin k → ℕ)
    (loc : Fin (blockCount T bank) → Fin P) (reg : Fin (r + 2) ↪ Fin R) (done : Fin P)
    (M : Machine w P R K)
    (installed : ∀ a, M.code (loc a) = (linkedRows T bank loc reg done a).resize w)
    {j : Fin p} (hj : T.code j = .reject) :
    M.code ((linkedPlacement T bank loc reg done).entry j) = .reject := by
  unfold Placement.entry
  rw [code_at (by rw [hj]; rfl), installed]
  simp [linkedRows, hj, Instr.resize]

private theorem resize_image (op : Instr 2 P R K) : (op.resize 5).resize w = op.resize w := by
  cases op <;> try rfl
  case constant dst val next => simp only [Instr.resize, resize_literal (by decide : 2 ≤ 5)]

/-- The fixed public table occupies a native vertex segment with its own two scratch
registers. The DFS registers and saved bootstrap registers can be framed by the caller. -/
def segment (T : Template p r k) (bank : Fin k → ℕ) : VertexImage.Segment where
  count := blockCount T bank
  privateRegs := r + 2
  entry := finProdFinEquiv (T.entry, (0 : Fin (capacity T bank + 3)))
  row loc _ _ reg done a := (linkedRows T bank loc reg done a).resize 5

theorem segment_entry (T : Template p r k) (bank : Fin k → ℕ)
    (loc : Fin (blockCount T bank) → Fin P) (reg : Fin (r + 2) ↪ Fin R) (done : Fin P)
    (entryLive : continues (T.code T.entry) = true) :
    (linkedPlacement T bank loc reg done).entry T.entry = loc (segment T bank).entry := by
  apply code_at
  cases he : T.code T.entry <;> first | rfl | simp [he, continues] at entryLive

/-- Extract the installed width-two rows from the actual five-bit image. -/
theorem segment_rows (T : Template p r k) (bank : Fin k → ℕ)
    (loc : Fin (blockCount T bank) → Fin P) (dfs : Fin 9 ↪ Fin R)
    (saved : VertexImage.Saved ↪ Fin R) (reg : Fin (r + 2) ↪ Fin R) (done : Fin P)
    (M : Machine w P R 11)
    (installed : ∀ a, M.code (loc a) =
      ((segment T bank).row loc dfs saved reg done a).resize w) (a : Fin (blockCount T bank)) :
    M.code (loc a) = (linkedRows T bank loc reg done a).resize w :=
  (installed a).trans (resize_image _)

end PairSimulation.InlinePublic

end VPVNP
end Computability
end OAI
