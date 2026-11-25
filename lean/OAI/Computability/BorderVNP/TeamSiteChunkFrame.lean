import OAI.Computability.BorderVNP.TeamSiteChunk
import OAI.Computability.BorderVNP.TeamLocalClockFinish

/-!
# Greedy finite-PC chunks and the transmitted word-sized register frame

A locally executed prefix evolves the architectural registers and cumulative
clock exactly as the word-PC replay used by the global handoff chain. At its
boundary, a remaining instruction yields a live handoff precisely when its full
charge exceeds the residual local budget. A terminal instruction yields the
canonical accepted frame even if the local countdown has reached zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamTapeHandoff TeamRAM
open TeamLocalClock

variable {w p r k m : ℕ}

/-- End-of-block status on a valid native continuation. -/
def chunkMode (tail : List (TeamRAM.Event w)) (s : TeamOpcode.State w p r) : Finish.Mode p :=
  if tail.isEmpty then .accepted else .live s.pc

/-- Physical pre-callback clock exit for a completed block. -/
def chunkExit (tail : List (TeamRAM.Event w)) (s : TeamOpcode.State w p r) : TeamLocalClock.Loop.Exit p r m :=
  if tail.isEmpty then .accepted else .handoff s.pc

/-- The word-sized register replay on every actual locally charged chunk returns the
encoded finite-PC state reached by the very same guessed words and branch bits. -/
theorem Chunk.word_advance {P : TeamOpcode.Program p r k m} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w m} {s z : TeamOpcode.State w p r} {c fin : Window w}
    {es : List (TeamRAM.Event w)} (run : Chunk (P.fetch pub lib) s c es z fin) (fits : p ≤ 2^w) :
    TeamTapeHandoff.advance (Model.wordFetch P pub lib) (Model.encode s) es = some (Model.encode z) := by
  induction run with
  | nil => rfl
  | cons action step budget bound rest ih =>
    simp only [TeamTapeHandoff.advance, Model.fetch_encode P pub lib fits, Model.advance_mapControl,
      step, Option.map_some, ih]

/-- Capturing the word-sized continuation transmits exactly its finite PC and registers
until the residual native path is empty, when it transmits the canonical halt. -/
theorem capture_local (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w m) (z : TeamOpcode.State w p r) (fits : p ≤ 2^w)
    (tail : List (TeamRAM.Event w)) (valid : Local (P.fetch pub lib) z tail) (elapsed : Word w) :
    capture (Model.wordFetch P pub lib) (Model.encode z) elapsed =
      Finish.frame (chunkMode tail z) z.reg elapsed := by
  rw [capture, Model.fetch_encode P pub lib fits]
  cases tail with
  | nil =>
    change P.fetch pub lib z = .accept at valid
    rw [valid]; rfl
  | cons e es =>
    have ha := valid.1
    cases h : P.fetch pub lib z <;> first | rfl | simp [h, TeamRAM.Instr.action] at ha

/-- The full-word handoff chain tests the exact outcome produced by the finite-PC
signed local execution, including the non-wrapping cumulative elapsed clock. -/
theorem Chunk.nextFrame {P : TeamOpcode.Program p r k m} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w m} {s z : TeamOpcode.State w p r} {c fin : Window w}
    {es tail : List (TeamRAM.Event w)} (run : Chunk (P.fetch pub lib) s c es z fin)
    (valid : Local (P.fetch pub lib) z tail) (fits : p ≤ 2^w) (limit : Word w)
    (total : limit.val = c.elapsed.val+c.global.val) :
    TeamTapeHandoff.nextFrame (Model.wordFetch P pub lib) limit
      (.live (packed w s.pc.val) s.reg c.elapsed) es =
      some (Finish.frame (chunkMode tail z) z.reg fin.elapsed) := by
  have safe : c.Safe := by change c.elapsed.val + c.global.val < 2^w; rw [← total]; exact limit.isLt
  obtain ⟨_,hg,_,_,_,ht,_⟩ := run.clock safe
  have cap : c.elapsed.val + cost es ≤ limit.val := by omega
  have he : packed w (c.elapsed.val+cost es) = fin.elapsed := by
    apply Fin.ext
    rw [packed_val (lt_of_le_of_lt cap limit.isLt), ht]
  change (if c.elapsed.val + cost es ≤ limit.val then
    (TeamTapeHandoff.advance (Model.wordFetch P pub lib) (Model.encode s) es).map
      (fun a => capture (Model.wordFetch P pub lib) a (packed w (c.elapsed.val+cost es))) else none) = _
  simp only [cap, ite_true, run.word_advance fits, Option.map_some, he, capture_local P pub lib z fits tail valid]

/-- A locally charged chunk has the prescribed physical end exit exactly when it is greedy.
The residual path's first opcode is inspected with its full burst before any mutation. -/
theorem Chunk.close_iff_maximal {P : TeamOpcode.Program p r k m} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w m} {s z : TeamOpcode.State w p r} {c fin : Window w}
    {es tail : List (TeamRAM.Event w)} (run : Chunk (P.fetch pub lib) s c es z fin)
    (valid : Local (P.fetch pub lib) z tail) (safe : c.Safe)
    (burst : ∀ e ∈ tail, e.action.extra ≤ fin.cap.val) :
    TeamLocalClock.Loop.result P pub z fin.block fin.global fin.elapsed fin.cap =
      (chunkExit tail z, fin.bank pub z) ↔ Team.MaximalBlock (fun e => e.action.extra) c.block.val es tail := by
  obtain ⟨hb,_,_,hfin,_,_,_⟩ := run.clock safe
  cases tail with
  | nil =>
    change P.fetch pub lib z = .accept at valid
    have hk := (accept_iff P pub lib z).mp valid
    simp [TeamLocalClock.Loop.result, hk, chunkExit, Window.bank, Team.MaximalBlock, hb]
  | cons e xs =>
    have act := valid.1
    have eq := opcodeBurst_eq P pub lib z _ act
    have hr := result_action P pub lib z fin _ act (burst e (by simp))
    have max : Team.MaximalBlock (fun e : TeamRAM.Event w => e.action.extra) c.block.val es (e::xs) ↔
        fin.block.val < 1 + (opcodeBurst P z).val := by
      simp [Team.MaximalBlock, hb, eq]
      unfold TeamTapeHandoff.cost at hfin hb
      omega
    rw [hr, max, ← decision_handoff_iff fin.block.val fin.global.val (opcodeBurst P z).val]
    cases hd : decision fin.block.val fin.global.val (opcodeBurst P z).val <;>
      simp [TeamLocalClock.Loop.afterGuard, hd, chunkExit, Window.bank]

/-- A greedy valid processor block closes with exactly the frame expected by the global
word-PC chain. The bank returned by its physical preflight is the complete end bank
of this signed local chunk. -/
theorem Chunk.scheduled {P : TeamOpcode.Program p r k m} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w m} {s z : TeamOpcode.State w p r} {c fin : Window w}
    {es tail : List (TeamRAM.Event w)} (run : Chunk (P.fetch pub lib) s c es z fin)
    (valid : Local (P.fetch pub lib) z tail) (fits : p ≤ 2^w) (limit : Word w)
    (total : limit.val = c.elapsed.val+c.global.val) (burst : ∀ e ∈ tail, e.action.extra ≤ fin.cap.val)
    (greedy : Team.MaximalBlock (fun e => e.action.extra) c.block.val es tail) :
    TeamLocalClock.Loop.result P pub z fin.block fin.global fin.elapsed fin.cap = (chunkExit tail z, fin.bank pub z) ∧
      TeamTapeHandoff.nextFrame (Model.wordFetch P pub lib) limit
        (.live (packed w s.pc.val) s.reg c.elapsed) es =
        some (Finish.frame (chunkMode tail z) z.reg fin.elapsed) :=
  ⟨(run.close_iff_maximal valid (by change c.elapsed.val + c.global.val < 2^w; rw [← total]; exact limit.isLt) burst).mpr greedy, run.nextFrame valid fits limit total⟩

end TeamSite

end BorderVNP
end Computability
end OAI
