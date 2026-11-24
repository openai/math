import OAI.Computability.VPVNP.PairTraversalWorkerMemory
import OAI.Computability.VPVNP.PrimedCounterRenameRun
import OAI.Computability.VPVNP.PrimedCounterAdminExec

/-!
# Uniform site worker for the traversal descriptor table

One burst starts with zero registers and the site number in persistent state.
Six public words specify the counts, identifier rows and two descriptor layers.
The worker fetches its count, writes the two header words, translates its row
of identifiers, and returns the next site number.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows.SiteWorker

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM PrimedCounter
open scoped Fin.CommRing

variable {w : ℕ}

/-- Address of the selected site's preimage-count word in the traversal worker's public count
array. -/
def counter (pub : Fin 6 → Word w) (i : Word w) := pub 0 + i
/-- Start address of the selected site's fixed-pitch preimage list in the source directory. -/
def source (pub : Fin 6 → Word w) (i : Word w) := pub 1 + i * pub 2
/-- Destination DFS row address for the current site in the new traversal layer. -/
def node (pub : Fin 6 → Word w) (i : Word w) := pub 4 + i * pub 5

private def setupOps : List (Op 7 6) :=
  [.stateWord 6, .publicWord 0 2, .binary .mul 0 6 0, .publicWord 1 1,
   .binary .add 0 1 0, .publicWord 1 0, .binary .add 1 1 6, .read 1 1,
   .publicWord 4 5, .binary .mul 6 6 4, .publicWord 2 4, .binary .add 6 2 6,
   .constant 5 2, .binary .add 2 6 5, .write 6 2, .constant 5 1,
   .binary .add 6 6 5, .write 6 1, .binary .add 1 0 1, .publicWord 3 3]

private def finishOps : List (Op 7 6) :=
  [.stateWord 6, .constant 5 1, .binary .add 6 6 5]

/-- The instruction table has fixed shape for every word width and every layer size. -/
def program : Flow 7 6 :=
  .seq (lines setupOps (by decide)) <|
    .seq (renameFlow (Function.Embedding.refl (Fin 7)) Fin.elim0 DescriptorRows.scan)
      (lines finishOps (by decide))

private def headerMemory (pub : Fin 6 → Word w) (i : Word w) (m : Memory w) : Memory w :=
  writeMemory (writeMemory m (node pub i) (node pub i + 2)) (node pub i + 1)
    (m (counter pub i).val)

private theorem setup_exec (pub : Fin 6 → Word w) (i : Word w) (m : Memory w) (input : Regs w 7) :
    ∃ es rs, Flow.Exec pub i (lines setupOps (by decide)) input m es rs
        (headerMemory pub i m) ∧
      rs 0 = source pub i ∧ rs 1 = source pub i + m (counter pub i).val ∧
      rs 2 = node pub i + 2 ∧ rs 3 = pub 3 ∧ rs 4 = pub 5 ∧ rs 5 = 1 ∧
      countProbes es = 3 ∧ es.length = 20 ∧ choiceBits es = [] := by
  simp only [Admin.exec_lines_iff_trace]
  simp (config := { decide := true }) [setupOps, trace, Op.effect, BinaryOp.eval, Function.update,
    counter, source, node, headerMemory, countProbes, choiceBits]

private theorem finish_exec (pub : Fin 6 → Word w) (i : Word w) (m : Memory w) (rs : Regs w 7) :
    ∃ out, Flow.Exec pub i (lines finishOps (by decide)) rs m [.tick, .tick, .tick] out m ∧
      out 6 = i + 1 := by
  simp only [Admin.exec_lines_iff_trace]
  simp (config := { decide := true }) [finishOps, trace, Op.effect, BinaryOp.eval, Function.update]

open private replay_exec count_append from OAI.Computability.VPVNP.PairTraversalRowExecution

private theorem worker_exec (pub : Fin 6 → Word w) (i : Word w) (mem : Memory w)
    (src nodeAddr count : ℕ) (hs : source pub i = (src : Word w))
    (hn : node pub i = (nodeAddr : Word w)) (hc : (mem (counter pub i).val).val = count)
    (before : src + count ≤ nodeAddr) (fit : nodeAddr + 2 + count < 2 ^ w)
    (input : Regs w 7 := fun _ => 0) :
    let image := DescriptorRows.rowMemory src (nodeAddr + 2) count (pub 3) (pub 5)
      (headerMemory pub i mem)
    ∃ es out, Flow.Exec pub i program input mem es out image ∧ out 6 = i + 1 ∧
      countProbes es = 2 * count + 3 ∧ es.length = 7 * count + 24 ∧ choiceBits es = [] := by
  intro image
  obtain ⟨ss, rs, setup, h0, h1, h2, h3, h4, h5, sp, sl, sb⟩ := setup_exec pub i mem input
  have countWord : mem (counter pub i).val = (count : Word w) := by
    apply Fin.ext
    exact hc.trans (Nat.mod_eq_of_lt (by omega)).symm
  have stop : rs 1 = ((src + count : ℕ) : Word w) := by rw [h1, hs, countWord, Nat.cast_add]
  have dst : rs 2 = ((nodeAddr + 2 : ℕ) : Word w) := by rw [h2, hn, Nat.cast_add, Nat.cast_ofNat]
  obtain ⟨ts, last, loop, probes, steps, bits⟩ := DescriptorRows.scan_exec
    (pub ∘ Fin.elim0) i rs (headerMemory pub i mem) src (nodeAddr + 2) count (pub 3) (pub 5)
    (h0.trans hs) stop dst h3 h4 h5 fit (by omega)
  obtain ⟨afterScan, lifted, _, _⟩ :=
    liftExec (Function.Embedding.refl (Fin 7)) Fin.elim0 pub loop rs rfl
  obtain ⟨out, advance, ret⟩ := finish_exec pub i image afterScan
  let fs : List (Event w) := [.tick, .tick, .tick]
  refine ⟨ss ++ (ts ++ fs), out, setup.seq (lifted.seq advance), ret, ?_, ?_, ?_⟩
  · rw [count_append, count_append, sp, probes]
    change 3 + (2 * count + 0) = _
    omega
  · simp only [List.length_append, sl, steps, fs, List.length_cons, List.length_nil]
    omega
  · simp only [Flow.choiceBits_append, sb, bits, List.nil_append]
    rfl

/-- One native call computes every address from the current site and its six
layout words. It costs two probes per identifier and three for the header. -/
theorem native (pub : Fin 6 → Word w) (i : Word w) (mem : Memory w)
    (src nodeAddr count fuel : ℕ) (hs : source pub i = (src : Word w))
    (hn : node pub i = (nodeAddr : Word w)) (hc : (mem (counter pub i).val).val = count)
    (before : src + count ≤ nodeAddr) (fit : nodeAddr + 2 + count < 2 ^ w)
    (clock : 7 * count + 24 < fuel) :
    let M := (program.template (some 6)).instantiate w pub
    ∃ es, execute M.program fuel (M.program.start i) mem [] = some ⟨es, some (i + 1)⟩ ∧
      after mem es = DescriptorRows.passMemory mem nodeAddr src (nodeAddr + 2)
        (counter pub i) (pub 3) (pub 5) count ∧
      countProbes es = 2 * count + 3 ∧ es.length = 7 * count + 24 := by
  obtain ⟨es, out, run, ret, probes, steps, bits⟩ :=
    worker_exec pub i mem src nodeAddr count hs hn hc before fit
  refine ⟨es, ?_, ?_, probes, steps⟩
  · apply (Flow.template_execute_iff program (some 6) pub i (fun _ => 0) (fun _ => 0) mem
      fuel [] _).mpr
    exact ⟨out, _, run, by simp only [Option.map_some, ret], steps.trans_lt clock, bits⟩
  · rw [replay_exec run]
    simpa only [headerMemory, hn, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
      DescriptorRows.headers_then_scan mem nodeAddr src (counter pub i) (pub 3) (pub 5) count
        before fit

end PairSimulation.TraversalRows.SiteWorker

end VPVNP
end Computability
end OAI
