import OAI.Computability.VPVNP.PairTraversalRows
import OAI.Computability.VPVNP.PrimedCounterAdminExec
import OAI.Computability.VPVNP.PrimedScheduleRAM
import OAI.Computability.VPVNP.RAMProcessorReportPrefix

/-!
# Writing the source-free leaf headers

The initial layer has no children. Its fixed worker computes the header address
from the site cursor, base and descriptor stride. It writes the pointer and a
zero count directly. Padding and other external words keep their old contents.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows.LeafWorker

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM PrimedCounter LocalHistory
open scoped Fin.CommRing

variable {w : ℕ}

private def ops : List (Op 4 2) :=
  [.stateWord 0, .publicWord 1 1, .binary .mul 1 1 0, .publicWord 2 0,
   .binary .add 1 2 1, .constant 2 2, .binary .add 2 1 2, .write 1 2,
   .constant 2 1, .binary .add 1 1 2, .constant 3 0, .write 1 3, .binary .add 0 0 2]

/-- Fixed native instruction program that writes the empty child row for one cursor leaf. -/
def program : Flow 4 2 := lines ops (by decide)

/-- Encode the leaf layer's row base and per-site pitch as the worker's two directory words. -/
def directory (w cap base : ℕ) : Fin 2 → Word w :=
  ![(base : Word w), ((cap + 2 : ℕ) : Word w)]

private def events (node : Word w) : List (Event w) :=
  [.tick, .tick, .tick, .tick, .tick, .tick, .tick, .write node (node + 2),
   .tick, .tick, .tick, .write (node + 1) 0, .tick]

/-- From the reset entry, emit exactly the two leaf header writes. -/
theorem native (cap base j fuel : ℕ) (mem : Memory w) (clock : 13 < fuel) :
    let pub := directory w cap base
    let M := (program.template (some 0)).instantiate w pub
    let node := (address cap base j : Word w)
    execute M.program fuel (M.program.start (j : Word w)) mem [] =
      some ⟨events node, some ((j + 1 : ℕ) : Word w)⟩ := by
  let pub := directory w cap base
  let node := (address cap base j : Word w)
  have h : ∃ rs, Flow.Exec pub (j : Word w) program (fun _ => 0) mem (events node) rs
      (writeMemory (writeMemory mem node (node + 2)) (node + 1) 0) ∧
      rs 0 = ((j + 1 : ℕ) : Word w) := by
    simp only [program, Admin.exec_lines_iff_trace]
    simp (config := { decide := true }) [ops, trace, Op.effect, BinaryOp.eval, Function.update,
      pub, node, directory, address, Nat.cast_add, Nat.cast_mul, events]
  obtain ⟨rs, run, ret⟩ := h
  apply (Flow.template_execute_iff program (some 0) pub (j : Word w) (fun _ => 0) (fun _ => 0)
    mem fuel [] _).mpr
  exact ⟨rs, _, run, by simp only [Option.map_some, ret], clock, rfl⟩

open private cell layer_at row_end_le from OAI.Computability.VPVNP.PairTraversalRows

private theorem padding {I : Type} (old : Order I) (cap previous base : ℕ) (mem : Memory w)
    (i : Fin old.length) (x : ℕ) (lo : address cap base i.val + 2 ≤ x)
    (hi : x < address cap base (i.val + 1)) :
    writeLayer cap previous base (leafLayer old) mem x = mem x := by
  let n := address cap base i.val
  have bound : x < n + (cap + 2) := by simpa only [n, address, Nat.mul_succ, Nat.add_assoc] using hi
  obtain ⟨z, hz⟩ := Nat.exists_eq_add_of_le lo
  have eqn : x = address cap base i.val + (z + 2) := by omega
  rw [eqn, layer_at cap previous base (leafLayer old) mem i (z + 2)
    (by change x < address cap base i.val + (cap + 2) at bound; omega)]
  simp [cell, childWords, leafLayer]

/-- A complete leaf pass from site zero on arbitrary initial external memory. -/
theorem run_layer {I : Type} (initial : Order I) (cap previous base : ℕ)
    (mem : Memory w) (fuel : ℕ) (fit : endPos cap base (leafLayer initial) < 2 ^ w)
    (clock : 13 < fuel) :
    let M := (program.template (some 0)).instantiate w (directory w cap base)
    ∃ rs, runSegment M.program fuel (some 0) mem (List.replicate initial.length []) = some rs ∧
      endState (some 0) rs = some (initial.length : Word w) ∧
      after mem (eventLog rs) = writeLayer cap previous base (leafLayer initial) mem ∧
      rs.length = initial.length ∧ countProbes (eventLog rs) = 2 * initial.length ∧
      ∀ rep ∈ rs, rep.probes = 2 ∧ rep.events.length = 13 := by
  let M := (program.template (some 0)).instantiate w (directory w cap base)
  let L := leafLayer initial
  let target := writeLayer cap previous base L mem
  change endPos cap base L < 2 ^ w at fit
  have rows : L.Rows w target cap previous base :=
    writeLayer_rows cap previous base L mem (fun _ => Nat.zero_le _) fit
  have work (k : ℕ) (hk : k ≤ initial.length) :
      ∃ rs, runSegment M.program fuel (some 0) mem (List.replicate k []) = some rs ∧
        endState (some 0) rs = some (k : Word w) ∧
        (∀ x, after mem (eventLog rs) x =
          if x < address cap base k then target x else mem x) ∧
        rs.length = k ∧ countProbes (eventLog rs) = 2 * k ∧
        ∀ rep ∈ rs, rep.probes = 2 ∧ rep.events.length = 13 := by
    induction k with
    | zero =>
      refine ⟨[], rfl, rfl, ?_, rfl, rfl, by simp⟩
      intro x
      change mem x = _
      by_cases hx : x < base
      · rw [ite_eq_left (by simpa [address] using hx)]
        apply (writeLayer_unchanged cap previous base L mem x _).symm
        rintro ⟨i, lo, _⟩
        exact hx.not_ge ((Nat.le_add_right _ _).trans lo)
      · rw [ite_eq_right (by simpa [address] using hx)]
    | succ k ih =>
      obtain ⟨rs, prev, endAt, contents, calls, probes, per⟩ := ih (Nat.le_of_succ_le hk)
      let m := after mem (eventLog rs)
      let n := address cap base k
      let i : Fin initial.length := ⟨k, hk⟩
      let next := address cap base (k + 1)
      let rep : Report w := ⟨events (n : Word w), some ((k + 1 : ℕ) : Word w)⟩
      have nativeCall : execute M.program fuel (M.program.start (k : Word w))
          (after mem (eventLog rs)) [] = some rep := native cap base k fuel m clock
      have inc : next = n + (cap + 2) := by simp [next, n, address, Nat.mul_succ, Nat.add_assoc]
      have room : n + (cap + 2) ≤ endPos cap base L := row_end_le cap base L i
      have nodeVal : (n : Word w).val = n := Nat.mod_eq_of_lt (by omega)
      have nextVal : ((n : Word w) + 1).val = n + 1 := by
        rw [← Nat.cast_one (R := Word w), ← Nat.cast_add]
        exact Nat.mod_eq_of_lt (by omega)
      refine ⟨rs ++ [rep], ?_, ?_, ?_, by simp [calls], ?_, ?_⟩
      · rw [List.replicate_succ', PrimedSchedule.runSegment_append, prev]
        simp only [Option.bind_some, endAt, runSegment, nativeCall, Option.map_some]
      · rw [endState_append]
        rfl
      · intro x
        have replay : after mem (eventLog (rs ++ [rep])) = after m rep.events := by
          simp only [eventLog, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, after, List.foldl_append, m]
        rw [replay]
        change writeMemory (writeMemory m (n : Word w) ((n : Word w) + 2))
          ((n : Word w) + 1) 0 x = if x < next then target x else mem x
        have row := (rows i).2
        by_cases h₁ : x = n + 1
        · subst x
          rw [ite_eq_left (by omega), writeMemory, nextVal, ite_eq_left rfl]
          exact row.2.2.2.1.symm
        rw [writeMemory, nextVal, ite_eq_right h₁]
        by_cases h₀ : x = n
        · subst x
          rw [ite_eq_left (by omega), writeMemory, nodeVal, ite_eq_left rfl]
          simpa only [Nat.cast_add, Nat.cast_ofNat] using row.2.2.1.symm
        rw [writeMemory, nodeVal, ite_eq_right h₀, show m x = _ from contents x]
        by_cases below : x < n
        · rw [ite_eq_left below, ite_eq_left (by omega)]
        · rw [ite_eq_right below]
          split
          · rename_i inside
            exact (padding initial cap previous base mem i x
              (by change n + 2 ≤ x; omega) inside).symm
          · rfl
      · have es : eventLog (rs ++ [rep]) = eventLog rs ++ rep.events := by
          simp [eventLog]
        rw [es, countProbes_append, probes]
        change 2 * k + 2 = 2 * (k + 1)
        omega
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact per _ hr
        · obtain rfl := List.mem_singleton.mp hr
          exact ⟨rfl, rfl⟩
  obtain ⟨rs, run, endAt, contents, calls, probes, per⟩ := work initial.length le_rfl
  refine ⟨rs, run, endAt, ?_, calls, probes, per⟩
  funext x
  rw [contents]
  split
  · rfl
  · rename_i beyond
    apply (writeLayer_unchanged cap previous base L mem x _).symm
    rintro ⟨i, _, last⟩
    have room := row_end_le cap base L i
    change x < address cap base i.val + 2 + 0 at last
    change address cap base i.val + (cap + 2) ≤ address cap base initial.length at room
    omega

end PairSimulation.TraversalRows.LeafWorker

end VPVNP
end Computability
end OAI
