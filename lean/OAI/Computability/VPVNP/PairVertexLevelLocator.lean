import OAI.Computability.VPVNP.PairVertexLevelBoot
import OAI.Computability.VPVNP.PairVertexLevelFinish
import OAI.Computability.VPVNP.PairVertexImage

/-!
# The hosted level locator for a nonleaf visit

The popped row selects the level and the packed site. The only shared register read
by the locator is DFS register seven. Its 35 fixed instructions obtain the old header
and the child directory from the eleven actual public words and the published tables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexLevel

open BurstRAM BurstRAM.PrivateRAM TraversalControllerInputs TraversalRoles TraversalRows
open NodeArguments.ChildScan VertexLevelBounds
open scoped Fin.CommRing

variable {w p r : ℕ}

/-- Place the 24 bootstrap instructions at the start of the level locator's program-counter
range. -/
def bootPC (loc : Fin 35 → Fin p) (i : Fin 24) := loc (i.castAdd 11)
/-- Place the six descending-scan instructions immediately after the level bootstrap. -/
def scanPC (loc : Fin 35 → Fin p) (i : Fin 6) := loc ((i.castAdd 5).natAdd 24)
/-- Place the five locator finishing instructions after both bootstrap and scan. -/
def finishPC (loc : Fin 35 → Fin p) (i : Fin 5) := loc ((i.natAdd 6).natAdd 24)

/-- The 35-instruction, fourteen-register level locator used by a noninitial DFS role. -/
def segment : VertexImage.Segment where
  count := 35
  privateRegs := 14
  entry := 0
  row loc dfs _ reg done i :=
    Fin.addCases (motive := fun _ => Instr 5 _ _ 11) (boot (bootPC loc) reg (dfs 7) (scanPC loc 0))
    (fun t => Fin.addCases (motive := fun _ => Instr 5 _ _ 11)
      (scan (scanPC loc) reg (finishPC loc 0)) (finish (finishPC loc) reg done) t) i

variable (M : Machine w p r 11) (loc : Fin 35 → Fin p) (dfs : Fin 9 ↪ Fin r)
    (saved : VertexImage.Saved ↪ Fin r) (reg : Fin 14 ↪ Fin r) (done : Fin p)

theorem segment_linked (rows : ∀ i, M.code (loc i) =
    (segment.row loc dfs saved reg done i).resize w) :
    (∀ i, M.code (bootPC loc i) = boot (bootPC loc) reg (dfs 7) (scanPC loc 0) i) ∧
    (∀ i, M.code (scanPC loc i) = scan (scanPC loc) reg (finishPC loc 0) i) ∧
    (∀ i, M.code (finishPC loc i) = finish (finishPC loc) reg done i) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · simpa only [segment, bootPC, Fin.addCases_left, resize_boot] using rows (i.castAdd 11)
  · simpa only [segment, scanPC, Fin.addCases_right, Fin.addCases_left, resize_scan] using
      rows ((i.castAdd 5).natAdd 24)
  · simpa only [segment, finishPC, Fin.addCases_right, resize_finish] using
      rows ((i.natAdd 6).natAdd 24)

/-- Full trace of a level lookup, combining header initialization, descending tests, and five
finishing ticks. -/
def trace (pub : Fin 11 → Word w) (m : Memory w) (level later : ℕ) : List (Event w) :=
  bootEvents pub m ++ scanEvents pub m level later ++ List.replicate 5 .tick

theorem trace_cost (pub : Fin 11 → Word w) (m : Memory w) (level later : ℕ) :
    (trace pub m level later).length = 32 + 6 * later ∧
    countProbes (trace pub m level later) = 5 + later ∧
    choiceBits (trace pub m level later) = [] := by
  obtain ⟨bl, bp, bc⟩ := bootEvents_cost pub m
  simp [trace, bl, bp, bc, CompressorRecords.Greedy.probes_append,
    PrimedInputRAM.Flow.choiceBits_append, countProbes, choiceBits]
  omega

/-- On a selected noninitial level, the actual finite locator recovers both indices and
the exact header. All private cells, all enclosing registers and the pending choice stream
are preserved. -/
theorem run (rows : ∀ i, M.code (loc i) = (segment.row loc dfs saved reg done i).resize w)
    {m : Memory w} {H first pitch offset cap base : ℕ} {old : TaggedLayer} {ls : List (Fiber w)}
    (d : Resident M.publicData m H first pitch offset cap base old ls)
    (j : Fin (old :: ls.map Prod.fst).length) (level : ℕ) (hj : j.val = level + 1)
    (id : Fin (old :: ls.map Prod.fst)[j].layer.count)
    (c : Config w p r) (hc : c.pc = loc segment.entry)
    (node : (c.reg (dfs 7)).val = address cap (layerBase cap base (old :: ls.map Prod.fst) j) id)
    (fit : layerBase cap base (old :: ls.map Prod.fst) (ls.length + 1) < 2 ^ w) :
    ∃ out, Prefix M m c out [] (trace M.publicData m (level + 1) (ls.length - (level + 1))) ∧
      out.pc = done ∧ Located M.publicData m reg (c.reg (dfs 7)) level (id.val : Word w) out ∧
      Frame reg c out := by
  obtain ⟨hb, hs, hf⟩ := segment_linked M loc dfs saved reg done rows
  obtain ⟨mid, ready, hbRun⟩ := boot_run hb c hc m
  obtain ⟨hlen, _, _, _⟩ := resident_geometry d
  have countEq : terminalField M.publicData m 1 = ((ls.length + 1 : ℕ) : Word w) := by
    rw [← hlen]
    exact Fin.ext (Nat.mod_eq_of_lt (terminalField M.publicData m 1).isLt).symm
  have hcount : terminalField M.publicData m 1 - 1 = (ls.length : Word w) := by
    simp [countEq]
  obtain ⟨bound, start, later, quotient⟩ := resident_locates d j id (c.reg (dfs 7)) node fit
  rw [hlen] at bound later
  rw [hj] at bound start later
  conv at quotient => lhs; rw [hj]
  have eq : level + 1 + (ls.length - (level + 1)) = ls.length := by omega
  have state : ScanState M.publicData m reg (c.reg (dfs 7)) ls.length mid :=
    ⟨ready.node, ready.header, ready.pitch, ready.index.trans hcount,
      by rw [ready.current, hcount]; rfl, ready.stride, ready.one, ready.offset14⟩
  have bootPre : Prefix M m c mid [] (bootEvents M.publicData m) := by
    intro fuel bs
    simpa only [(bootEvents_cost _ _).1, List.nil_append] using hbRun fuel bs
  have bootFrame : Frame reg c mid := ⟨fun i hi => ready.outside i
    (fun l e => hi ⟨l, e.symm⟩), ready.privateMem, ready.persistent⟩
  obtain ⟨endScan, sp, atEnd, value, state', scanFrame⟩ :=
    scan_run hs (level + 1) (ls.length - (level + 1)) mid ready.pc (by rw [eq]; exact state) start
      (fun i hi hl => later i hi (by omega))
  obtain ⟨out, fp, outPC, result, finishFrame⟩ := finish_run hf endScan atEnd state' value quotient
  exact ⟨out, (bootPre.trans sp).trans fp, outPC, result,
    bootFrame.trans (scanFrame.trans finishFrame)⟩

end PairSimulation.VertexLevel

end VPVNP
end Computability
end OAI
