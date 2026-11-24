import OAI.Computability.VPVNP.CompressorRegisterSetupTrace
import OAI.Computability.VPVNP.PairSimulationTerminalSplice
import OAI.Computability.VPVNP.PairTraversalControllerOrdinal
import OAI.Computability.VPVNP.PairTraversalReferenceFootprint
import OAI.Computability.VPVNP.PairTraversalControllerPrepare

/-!
# External addresses read by the native traversal setup

The register bank loads six terminal scalars and seven kinds of level scalar.
Even when the persistent state is the final sentinel, taking its phase-level
modulo the resident level count selects an allocated level. Its predecessor
saturates at zero. The entry and dispatch ticks introduce no further reads.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM PrivateRAM CompressorRecords PhaseRecipe TraversalControllerInputs TraversalRoles
open scoped Fin.CommRing

variable {w : ℕ} {pub : Fin 11 → Word w} {m : Memory w}
variable {H first stride offset cap base : ℕ} {old : TaggedLayer} {ls : List (Fiber w)}

/-- Scalar fields loaded from the initial, current or preceding level. -/
def levelScalars : Finset ℕ := {14, 21, 22, 24, 25, 26, 27}

private theorem levelScalar_lt {f : ℕ} (hf : f ∈ levelScalars) : f < 28 := by
  simp only [levelScalars, Finset.mem_insert, Finset.mem_singleton] at hf
  omega

private theorem terminalScalar_bounds {f : ℕ} (hf : f ∈ terminalScalars) : 0 < f ∧ f < 31 := by
  simp only [terminalScalars, Finset.mem_insert, Finset.mem_singleton] at hf
  omega

/-- The resident positive level count confines all formula loads, including
those issued while computing another load's address, to the designated scalars. -/
theorem formulas_reads (d : Resident pub m H first stride offset cap base old ls)
    (data : ℕ → Prop) (terms : ∀ f ∈ terminalScalars, data (H + f))
    (fields : ∀ j ≤ ls.length, ∀ f ∈ levelScalars, data (first + j * stride + f)) (s : Word w)
    (t : Fin 18) : (formulas t).ReadsFrom data (recipePub pub) s m := by
  let safe := Expr.ReadsFrom data (recipePub pub) s m
  let ev := Expr.eval (recipePub pub) s m
  have terminalSafe : safe terminal := by
    simp [safe, terminal, Expr.add, Expr.mul, Expr.sub, Expr.ReadsFrom]
  have termSafe (f : ℕ) (hf : f ∈ terminalScalars) : safe (term f) := by
    refine ⟨⟨terminalSafe, trivial⟩, ?_⟩
    change data (terminalHead pub + (f : Word w)).val
    rw [d.header, ← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt]
    · exact terms f hf
    · have := terminalScalar_bounds hf
      have := d.headerFits
      omega
  have levelSafe (x : Expr) (j : ℕ) (read : safe x) (val : ev x = (j : Word w))
      (hj : j ≤ ls.length) (f : ℕ) (hf : f ∈ levelScalars) : safe (level x f) := by
    refine ⟨⟨⟨termSafe 16 (by decide), read, termSafe 17 (by decide)⟩, trivial⟩, ?_⟩
    change data (terminalField pub m 16 + ev x * terminalField pub m 17 + (f : Word w)).val
    rw [val, terminal_read d 16 (by decide), terminal_read d 17 (by decide), d.firstHead,
      d.levelPitch, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, Fin.val_natCast,
      Nat.mod_eq_of_lt]
    · exact fields j hj f hf
    · exact (Nat.add_lt_add_left (levelScalar_lt hf) _).trans_le (d.levelFits j hj)
  have initialField := levelSafe (.lit 0) 0 trivial rfl (Nat.zero_le _)
  have layers : safe levels := termSafe 1 (by decide)
  have sites : safe initialSites :=
    ⟨initialField 21 (by decide), ⟨trivial, layers⟩,
      termSafe 7 (by decide), initialField 21 (by decide)⟩
  have radix : safe pitch := ⟨sites, trivial⟩
  have phase : safe phaseLevel := ⟨trivial, radix⟩
  have current : safe index := ⟨phase, layers⟩
  have pos : safe positiveIndex := ⟨current, current⟩
  have predSafe : safe previous := ⟨current, pos⟩
  let L := ls.length + 1
  let p := (ev phaseLevel).val
  have hL : (ev levels).val = L :=
    (congrArg Fin.val (terminal_read d 1 (by decide))).trans d.levels
  have heL : ev levels = (L : Word w) := hL ▸ (Fin.ofNat_val_eq_self _).symm
  have heP : ev phaseLevel = (p : Word w) := (Fin.ofNat_val_eq_self _).symm
  have positive : 0 < L := Nat.succ_pos _
  have fit := hL ▸ (ev levels).isLt
  obtain ⟨idx, _, pred⟩ := TraversalControllerOrdinal.index_words positive fit (ev phaseLevel).isLt
  have currentVal : ev index = ((p % L : ℕ) : Word w) := by
    change BinaryOp.mod.eval (ev phaseLevel) (ev levels) = _
    rw [heP, heL]
    exact idx
  have predVal : ev previous = ((p % L - 1 : ℕ) : Word w) := by
    change BinaryOp.sub.eval (BinaryOp.mod.eval (ev phaseLevel) (ev levels))
      (BinaryOp.div.eval (BinaryOp.mod.eval (ev phaseLevel) (ev levels))
        (BinaryOp.mod.eval (ev phaseLevel) (ev levels))) = _
    rw [heP, heL]
    exact pred
  have bound : p % L ≤ ls.length := Nat.lt_succ_iff.mp (Nat.mod_lt p positive)
  have currentField := levelSafe index _ current currentVal bound
  have predField := levelSafe previous _ predSafe predVal ((Nat.sub_le ..).trans bound)
  have num : safe count := ⟨sites, pos, predField 22 (by decide), sites⟩
  have siteSafe : safe site := ⟨trivial, radix⟩
  have twice : safe (levels.add levels) := ⟨layers, layers⟩
  have next : safe (Expr.state.add (.lit 1)) := ⟨trivial, trivial⟩
  have reset : safe ((phaseLevel.add (.lit 1)).mul pitch) := ⟨⟨phase, trivial⟩, radix⟩
  fin_cases t <;> first
    | exact siteSafe | exact phase | exact layers | exact twice | exact num | exact current
    | exact next | exact reset | trivial
    | exact termSafe _ (by decide) | exact initialField _ (by decide)
    | exact currentField _ (by decide) | exact predField _ (by decide)

/-- The two terminal control cells are excluded when each physical level
header precedes the terminal header. The conclusion holds for every state word. -/
theorem formulas_worker_reads (d : Resident pub m H first stride offset cap base old ls)
    (beforeH : ∀ j ≤ ls.length, first + j * stride + 28 ≤ H) (s : Word w) (t : Fin 18) :
    (formulas t).ReadsFrom (TerminalLink.workerCell (TerminalLink.header pub))
      (recipePub pub) s m := by
  have header : TerminalLink.header pub = (H : Word w) := d.header
  have fit := d.headerFits
  have hval : (TerminalLink.header pub).val = H := by
    rw [header, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have last : (TerminalLink.header pub + 31).val = H + 31 := by
    rw [header, show (31 : Word w) = ((31 : ℕ) : Word w) from rfl, ← Nat.cast_add, Fin.val_natCast,
      Nat.mod_eq_of_lt (by omega)]
  apply formulas_reads d
  · intro f hf
    have := terminalScalar_bounds hf
    simp only [TerminalLink.workerCell, hval, last]
    omega
  · intro j hj f hf
    have := beforeH j hj
    have := levelScalar_lt hf
    simp only [TerminalLink.workerCell, hval, last]
    omega

/-- All reads in the actual native setup and guard trace avoid both terminal
control cells. The worker that follows the setup uses the resulting bank. -/
theorem Native.prefixTrace_reads (d : Resident pub m H first stride offset cap base old ls)
    (beforeH : ∀ j ≤ ls.length, first + j * stride + 28 ≤ H)
    (s : Word w) (rs : PrimedStackRAM.Regs w R) :
    SourceTransport.Reads (TerminalLink.workerCell (TerminalLink.header pub))
      (Native.prefixTrace pub s m rs) := by
  have safe := RegisterSetup.lines_reads formulas _ (recipePub pub) s m
    (formulas_worker_reads d beforeH s) ((Native.loaded pub s).reg ∘ vm)
  intro a v read
  simp only [Native.prefixTrace, List.mem_append, List.mem_cons, List.not_mem_nil, reduceCtorEq,
    false_or, List.mem_replicate] at read
  exact safe a v (by simpa using read)

open Compression LocalHistory TraversalRows DirectoryRun

variable {k A : Type*} [Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) {n : ℕ} (T : ℕ)
variable (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices) (base : ℕ) (raw : Memory w)
variable (ds : let vs := executeLevels B f hf T hT X z
  (i : Fin vs.length) → LevelDirectory vs[i] raw base)

/-- Every native setup issued on the selected reference run reads worker
cells, also after any prefix of tag and row writes. -/
theorem selected_prefix_setup_reads
    (d : Resident pub raw H first stride offset B.recordLimit base
      ⟨leafLayer (siteOrder X), .cursor⟩ (levelFibers (executeLevels B f hf T hT X z) ds))
    (headersBefore : ∀ j ≤ (executeLevels B f hf T hT X z).length, first + j * stride + 28 ≤ base)
    (ts rs : List (Report w))
    (tags : RolePasses offset B.recordLimit base (selected B f hf T hT X z) raw ts)
    (rows : Segments (selectedJobs B f hf T hT X z base raw ds) (after raw (eventLog ts)) rs)
    (belowHeader : offset + base + tagWords B.recordLimit (selected B f hf T hT X z) ≤ H) :
    ∀ q ≤ (ts ++ rs).length, ∀ s regs,
      SourceTransport.Reads (TerminalLink.workerCell (TerminalLink.header pub))
        (Native.prefixTrace pub s (after raw (eventLog ((ts ++ rs).take q))) regs) := by
  have hh : H < 2 ^ w := by have := d.headerFits; omega
  have frame := selected_reference_frame B f hf T hT X z base raw ds offset ts rs tags rows
    (belowHeader.trans_lt hh)
  have size := congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  change offset + base + words B.recordLimit ((selected B f hf T hT X z).map TaggedLayer.layer) ≤ H
    at belowHeader
  rw [size] at belowHeader
  have headers : ∀ j ≤ (levelFibers (executeLevels B f hf T hT X z) ds).length,
      first + j * stride + 28 ≤ base := by
    simpa only [levelFibers, List.length_ofFn] using headersBefore
  intro q hq s regs
  have d' := d.transfer headers (fun x hx =>
    frame q hq x (Or.inl (hx.trans_le (Nat.le_add_left _ _))) (Or.inl hx))
    (fun field _ => frame q hq _ (Or.inr (by omega)) (Or.inr (by omega)))
  exact Native.prefixTrace_reads d' (fun j hj => (headers j hj).trans (by omega)) s regs

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
