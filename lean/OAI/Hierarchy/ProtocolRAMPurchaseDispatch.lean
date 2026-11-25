import OAI.Hierarchy.ProtocolRAMMarkLoad
import OAI.Hierarchy.ProtocolRAMPurchaseGateColumns

namespace OAI
/-! # Native DFS path decoding followed by the greedy purchase scan

The program reads both the path table and signed mark words from external memory.
Only the number of candidates, path length, and physical layout occur in its code.
-/

namespace Hierarchy.ProtocolRAM.PurchaseStage

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open GateColumns
open scoped Classical Fin.CommRing

structure Dispatch where
  candidates : ℕ
  depth : ℕ
  tiles : ℕ
  first : ℕ
  tape : ℕ
  work : ℕ
  source : Bank
  directory : Directory
  marks : Bank

def paths (L : Dispatch) (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) :=
  List.ofFn (fun i => List.ofFn (rows i))

def dispatch (L : Dispatch) (w : ℕ) : Procedure w :=
  (ProtocolRAMPurchaseGateColumns.code w L.candidates L.depth L.source L.directory L.work L.tape).seq
    ((MarkTape.load w L.tiles L.work L.first L.candidates L.marks).seq
      (MarkTape.procedure w L.tape (L.candidates*(4*L.depth+3))))

def dispatchClock (L : Dispatch) :=
  clock (passes L.source L.directory L.work (L.candidates*(4*L.depth+3)) L.tape) +
    (MarkTape.loadClock L.tiles L.first L.candidates L.marks + (3+17*(L.candidates*(4*L.depth+3))))

def dispatchMemory {w : ℕ} (L : Dispatch) (rows : Fin L.candidates → Fin L.depth → Fin L.tiles)
    (m : Memory w) : Memory w :=
  let generated := ProtocolRAMPurchaseGateColumns.output L.candidates L.depth L.source L.directory L.work L.tape m
  MarkTape.eval (MarkTape.compilePaths L.tiles L.work L.first (paths L rows))
    (MarkTape.loaded L.tiles L.work L.first L.candidates L.marks generated)

def decisionBase (L : Dispatch) := L.work+4+L.tiles+L.first

structure DispatchReady (L : Dispatch) (w : ℕ) : Prop where
  width : 0 < w
  length : L.depth*L.candidates ≤ L.source.size
  source : L.source.Fits w L.tape
  directory : ∀ j, j<6 → (L.directory.bank j).Fits w L.tape
  marks : L.marks.Fits w L.tape
  separate : L.tape+3*(L.candidates*(4*L.depth+3)) ≤ L.work
  room : decisionBase L+L.candidates < 2^w

def PathTable {w : ℕ} (L : Dispatch) (rows : Fin L.candidates → Fin L.depth → Fin L.tiles)
    (m : Memory w) :=
  ProtocolRAMPurchaseGateColumns.TileRows L.source rows m ∧
    Mounted L.directory (ProtocolRAMPurchaseGateColumns.spec
      (R := L.candidates) (H := L.depth) L.tiles L.work L.first) m

/-- The actual mark bank of an input configuration. -/
noncomputable def marked {w : ℕ} (L : Dispatch) (m : Memory w) : Finset (Fin L.tiles) :=
  Finset.univ.filter fun v => L.marks.read m (v.val : Word w) ≠ 0

def SignedWords {w : ℕ} (L : Dispatch) (m : Memory w) : Prop :=
  ∀ v : Fin L.tiles, L.marks.read m (v.val : Word w) = 0 ∨ L.marks.read m (v.val : Word w) = 1

theorem dispatch_exec {w : ℕ} (L : Dispatch) (rows : Fin L.candidates → Fin L.depth → Fin L.tiles)
    (m : Memory w) (ready : DispatchReady L w) (table : PathTable L rows m) (signed : SignedWords L m) :
    let out := dispatchMemory L rows m
    (dispatch L w).Exec m out (dispatchClock L) ∧
    (∀ v : Fin L.tiles, out (L.work+4+v.val) =
      MarkTape.encode w (decide (v ∈ (AdaptiveProbe.scanPaths (paths L rows) (marked L m)).2))) ∧
    ∀ i : Fin L.candidates, out (decisionBase L+i.val) =
      MarkTape.encode w ((MarkTape.decisions (paths L rows) (marked L m))[i.val]'(by simp [paths])) := by
  let gen := ProtocolRAMPurchaseGateColumns.output L.candidates L.depth L.source L.directory L.work L.tape m
  have room := ready.room
  dsimp [decisionBase] at room
  have separate := ready.separate
  obtain ⟨materialize, packed, _, _, frame⟩ := ProtocolRAMPurchaseGateColumns.execute L.source
    L.directory L.work L.first L.tape rows m table.1 table.2 ready.width ready.length ready.source
    ready.directory (by simpa [ProtocolRAMPurchaseGateColumns.gates] using (show L.tape+3*(L.candidates*(4*L.depth+3))<2^w by omega))
  have before : L.tape ≤ L.work := by omega
  have deps : L.marks.Fits w L.work := ⟨ready.marks.1, ready.marks.2.1, ready.marks.2.2.trans before⟩
  have bit (v : Fin L.tiles) : L.marks.read gen (v.val : Word w) =
      MarkTape.encode w (decide (v ∈ marked L m)) := by
    have addr := Nat.mod_lt ((v.val : Word w).val) ready.marks.1
    have bank := ready.marks.2.2
    rw [show L.marks.read gen (v.val : Word w) = L.marks.read m (v.val : Word w) from
      frame _ (Or.inl (by omega))]
    rcases signed v with hz | ho
    · simp [marked, MarkTape.encode, hz]
    · have ne : (1 : Word w) ≠ 0 := by
        intro eqn
        have hn := congrArg Fin.val eqn
        rw [show (1 : Word w).val = 1 from Fin.val_cast_of_lt (Nat.one_lt_two_pow ready.width.ne')] at hn
        exact Nat.one_ne_zero hn
      simp [marked, MarkTape.encode, ho, ne]
  have fixed : ∀ p ∈ paths L rows, p.length = L.depth := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    simp
  obtain ⟨scan, remaining, picks⟩ := MarkTape.load_and_run L.tiles L.work L.first L.tape L.depth
    (paths L rows) L.marks gen (marked L m) fixed bit deps packed
    (by simpa [paths] using separate) (by simpa [paths] using room)
  have length : (paths L rows).length = L.candidates := by simp [paths]
  simp only [length] at scan remaining picks
  exact ⟨Procedure.Exec.then (A:=ProtocolRAMPurchaseGateColumns.code w L.candidates L.depth L.source L.directory L.work L.tape)
    materialize scan,remaining,fun i=>picks i.val i.isLt⟩

private theorem cheap_of_mark {w P R K : ℕ} (i : Instr w P R K)
    (h : MarkTape.markInstruction i) : TaggedShorterCheapCPU.Cheap i := by
  cases i <;> first | trivial | exact False.elim h | (rcases h with rfl | rfl | rfl <;> trivial)

private theorem columns_cheap (L : Dispatch) (w : ℕ) :
    CheapCode (ProtocolRAMPurchaseGateColumns.code w L.candidates L.depth L.source L.directory L.work L.tape) := by
  unfold ProtocolRAMPurchaseGateColumns.code
  generalize passes L.source L.directory L.work (ProtocolRAMPurchaseGateColumns.gates L.candidates L.depth) L.tape=ps
  exact @program_cheap w ps

private theorem mark_cheap (w tape n : ℕ) : CheapCode (MarkTape.procedure w tape n) := by
  intro P R K pc reg pub exit i
  exact cheap_of_mark _ (MarkTape.cheap w tape n pc reg pub exit i)

set_option maxHeartbeats 1200000 in
theorem dispatch_cheap (L : Dispatch) (w : ℕ) : CheapCode (dispatch L w) := by
  let N:=L.candidates*(4*L.depth+3)
  let init:=MarkTape.load w L.tiles L.work L.first L.candidates L.marks
  let gate:=MarkTape.procedure w L.tape N
  let generate:=ProtocolRAMPurchaseGateColumns.code w L.candidates L.depth L.source L.directory L.work L.tape
  have stage : CheapCode init:=@scan_cheap w L.work (4+L.tiles+L.first+L.candidates) (MarkTape.loadTerm L.tiles L.marks)
  have run : CheapCode (init.seq gate):=@cheap_seq w init gate (@stage) (@mark_cheap w L.tape N)
  exact @cheap_seq w generate (init.seq gate) (@columns_cheap L w) (@run)

theorem dispatchClock_le (L : Dispatch) :
    dispatchClock L ≤ 16+3*(L.candidates*(4*L.depth+3))*64 +
      (MarkTape.loadClock L.tiles L.first L.candidates L.marks + (3+17*(L.candidates*(4*L.depth+3)))) :=
  Nat.add_le_add_right (GateColumns.ticks _ _ _ _ _) _

end Hierarchy.ProtocolRAM.PurchaseStage

end OAI
