import OAI.Computability.VPVNP.PrimedStackRAMCode
import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.RAMRecords

/-!
# Native initialization of cursor incidence records

A call visits one actual outgoing port in site-major order. The two address blocks
are numbered by the ordinary binary values of the corresponding bits of the physical
address. The call advances the cursor and translates the appropriate block on port one.
It writes the inverse incidence at the computed destination. Parallel copies retain
their own slot numbers. Lanes over a common base arc repeat the same three base writes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CursorRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Public words are the degree, cursor count, two binary radices, real arc width,
and the six column starts. The persistent word is the site-major outgoing port. -/
def visit : List (Op 20 11) :=
  [.stateWord 0, .publicWord 1 0, .publicWord 2 1, .publicWord 3 2, .publicWord 4 3,
   .binary .div 5 0 1, .binary .mod 6 0 1,
   .binary .mod 7 5 4, .binary .div 8 5 4, .binary .mod 9 8 3, .binary .div 10 8 3,
   .constant 11 1, .constant 12 2,
   .binary .add 13 6 11, .binary .div 13 12 13, .binary .mod 14 13 12,
   .binary .shiftLeft 14 14 10, .binary .mod 15 14 3, .binary .div 16 14 3,
   .binary .bitXor 9 9 15, .binary .bitXor 7 7 16,
   .binary .add 10 10 11, .binary .mod 10 10 2, .binary .mul 10 10 3, .binary .add 10 10 9,
   .binary .mul 8 8 1, .binary .add 8 8 6, .binary .mul 15 10 1, .binary .add 15 15 6,
   .binary .mul 10 10 4, .binary .add 10 10 7, .binary .mul 10 10 1, .binary .add 10 10 6,
   .binary .add 13 13 11, .binary .div 13 13 12, .publicWord 14 4, .binary .mul 13 13 14,
   .publicWord 17 5, .binary .add 17 17 8, .write 17 15,
   .publicWord 17 6, .binary .add 17 17 15, .write 17 8,
   .publicWord 17 7, .binary .add 17 17 8, .write 17 16,
   .publicWord 17 8, .binary .add 17 17 0, .write 17 10,
   .publicWord 17 9, .binary .add 17 17 10, .write 17 0,
   .publicWord 17 10, .binary .add 17 17 0, .write 17 13,
   .binary .add 0 0 11]

/-- Values appearing in the six writes. -/
structure Row (α : Type) where
  /-- Outgoing port index at the source base vertex, before the residual lane is included. -/
  sourceBase : α
  /-- Incoming port index at the destination base vertex, used for the inverse base-incidence
  write. -/
  targetBase : α
  /-- The mask XORed into the residual lane when lifting this base arc to its actual
  destination. -/
  displacement : α
  /-- Destination port index after the cursor advance and lane translation, including the
  actual site's residual lane. -/
  targetActual : α
  /-- Number of payload bits carried by the outgoing port, with zero width for padding. -/
  width : α

/-- Decode one site-major outgoing port using word arithmetic and compute its base endpoints,
lane translation, actual destination and payload width. -/
def wordRow (p : Fin 11 → Word w) (i : Word w) : Row (Word w) :=
  let div := @BinaryOp.eval w .div
  let mod := @BinaryOp.eval w .mod
  let xor := @BinaryOp.eval w .bitXor
  let site := div i (p 0)
  let port := mod i (p 0)
  let base := div site (p 3)
  let cursor := div base (p 2)
  let gate := div 2 (port + 1)
  let mask := BinaryOp.shiftLeft.eval (mod gate 2) cursor
  let shift := div mask (p 2)
  let dest := mod (cursor + 1) (p 1) * p 2 + xor (mod base (p 2)) (mod mask (p 2))
  ⟨base * p 0 + port, dest * p 0 + port, shift,
   (dest * p 3 + xor (mod site (p 3)) shift) * p 0 + port, div (gate + 1) 2 * p 4⟩

/-- Directly addressed outgoing and incoming columns, followed by the payload column
at each of the two granularities. -/
def writes (p : Fin 11 → Word w) (i : Word w) (r : Row (Word w)) : List (Word w × Word w) :=
  [(p 5 + r.sourceBase, r.targetBase), (p 6 + r.targetBase, r.sourceBase),
   (p 7 + r.sourceBase, r.displacement), (p 8 + i, r.targetActual),
   (p 9 + r.targetActual, i), (p 10 + i, r.width)]

/-- The native trace for one outgoing port, with the arithmetic ticks and six writes populating
the base and actual incidence columns. -/
def events (p : Fin 11 → Word w) (i : Word w) : List (Event w) :=
  let r := wordRow p i
  List.replicate 39 .tick ++ [.write (p 5 + r.sourceBase) r.targetBase,
   .tick, .tick, .write (p 6 + r.targetBase) r.sourceBase,
   .tick, .tick, .write (p 7 + r.sourceBase) r.displacement,
   .tick, .tick, .write (p 8 + i) r.targetActual,
   .tick, .tick, .write (p 9 + r.targetActual) i,
   .tick, .tick, .write (p 10 + i) r.width, .tick]

theorem events_after (p : Fin 11 → Word w) (i : Word w) (m : Memory w) :
    after m (events p i) =
      (writes p i (wordRow p i)).foldl (fun mem av ↦ writeMemory mem av.1 av.2) m := rfl

theorem events_work (p : Fin 11 → Word w) (i : Word w) :
    (events p i).length = visit.length ∧ countProbes (events p i) = 6 := ⟨rfl, rfl⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem visit_trace (p : Fin 11 → Word w) (m : Memory w) (i : Word w) (rs : Regs w 20) :
    ∃ rs', trace p i visit rs m = some (events p i, rs', after m (events p i)) ∧ rs' 0 = i + 1 := by
  simp (config := {decide := true}) [visit, events, wordRow, trace, Op.effect, BinaryOp.eval,
    Function.update, after, update]
  have h1 : (Fin.ofNat (2 ^ w) (1 : Word 2).val) = (1 : Word w) := by apply Fin.ext; rfl
  simp only [Fin.ofNat_eq_cast, Fin.val_one] at h1
  simp only [h1]
  repeat' apply And.intro
  all_goals first | rfl | trivial

/-- The same instruction table runs at every input length and visits every slot. -/
theorem visit_native (p : Fin 11 → Word w) (m : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w p
    execute M.program (1 + visit.length) (M.program.start i) m [] =
      some ⟨events p i, some (i + 1)⟩ := by
  obtain ⟨rs, ht, hr⟩ := visit_trace p m i (fun _ ↦ 0)
  let M := (template visit 0).instantiate w p
  change execute M.program (1 + visit.length) ⟨M.entry, i, fun _ ↦ 0, fun _ ↦ 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [hr]

end CompressorRecords.CursorRAM

end VPVNP
end Computability
end OAI
