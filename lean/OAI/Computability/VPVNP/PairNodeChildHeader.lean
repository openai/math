import OAI.Computability.VPVNP.PairNodeChildAddress
import OAI.Computability.VPVNP.PairSimulationDFS

/-!
# Loading a placement row and the old layer's parameter directory

The popped descriptor supplies a child-list pointer and count. A seven-word
directory supplies the geometry of the old descriptors, the private argument
arena, and the inverse-incidence and width columns. These words are read
once before the child scan enters its loop.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildHeader

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.tick ReadPrefix.read ReadPrefix.nil ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {w p r k : ℕ}

/-- The directory words, in their stored order. -/
structure Fields (w : ℕ) where
  /-- External address of the first descriptor row in the older layer. The child scan subtracts
  this address from the child's row address to recover its offset. -/
  olderBase : Word w
  /-- Distance in words between successive older-layer descriptor rows. Dividing a row offset
  by this stride gives the child's site ordinal. -/
  stride : Word w
  /-- Number of outgoing slots per older-layer site. Multiplying the site ordinal by this
  degree gives the index of its first port. -/
  degree : Word w
  /-- Base address of the private arena where the child scan stores guessed half-wire
  arguments. -/
  argumentStart : Word w
  /-- Distance in private words between argument buffers indexed by consecutive node addresses.
  A child at address `node` uses the buffer at `argumentStart + node * argumentStride`. -/
  argumentStride : Word w
  /-- Base address of the inverse-incidence table. At an incoming port, this table gives the
  source port whose wire width the scan needs. -/
  actualIn : Word w
  /-- Base address of the wire-width table indexed by actual outgoing ports. Each width tells
  the scan how many argument bits to guess for that wire. -/
  width : Word w

/-- Seven words in the order read by the child scan. They contain the descriptor base and
stride, degree, private argument base and stride, inverse-incidence base, and width-table
base. -/
def Fields.words (f : Fields w) : Fin 7 → Word w :=
  ![f.olderBase, f.stride, f.degree, f.argumentStart, f.argumentStride, f.actualIn, f.width]

/-- The seven directory words occupy consecutive external memory cells beginning at `base`,
using word-address arithmetic. -/
def Fields.Stored (f : Fields w) (m : Memory w) (base : Word w) : Prop :=
  ∀ j : Fin 7, m (base + (j.val : Word w)).val = f.words j

/-- The 17 instructions that load the child-list pointer and count from the popped row, read
the seven older-layer directory words, and pass control to `done`. -/
def instruction (pc : Fin 17 → Fin p) (reg : Fin 16 ↪ Fin r) (done : Fin p) :
    Fin 17 → Instr w p r k :=
  ![.constant (reg 3) 1 (pc 1), .readExternal (reg 9) (reg 7) (pc 2),
    .binary .add (reg 10) (reg 7) (reg 3) (pc 3), .readExternal (reg 10) (reg 10) (pc 4),
    .readExternal (reg 11) (reg 8) (pc 5), .binary .add (reg 7) (reg 8) (reg 3) (pc 6),
    .readExternal (reg 12) (reg 7) (pc 7), .binary .add (reg 7) (reg 7) (reg 3) (pc 8),
    .readExternal (reg 13) (reg 7) (pc 9), .binary .add (reg 7) (reg 7) (reg 3) (pc 10),
    .readExternal (reg 14) (reg 7) (pc 11), .binary .add (reg 7) (reg 7) (reg 3) (pc 12),
    .readExternal (reg 15) (reg 7) (pc 13), .binary .add (reg 7) (reg 7) (reg 3) (pc 14),
    .readExternal (reg 6) (reg 7) (pc 15), .binary .add (reg 7) (reg 7) (reg 3) (pc 16),
    .readExternal (reg 7) (reg 7) done]

theorem resize_instruction (pc : Fin 17 → Fin p) (reg : Fin 16 ↪ Fin r) (done : Fin p)
    (i : Fin 17) : (instruction (w := 2) (k := k) pc reg done i).resize w =
      instruction pc reg done i := by fin_cases i <;> rfl

/-- The machine contains the header's 17 instructions at the specified program counters, with
the supplied register assignment and continuation. -/
def Linked (M : Machine w p r k) (pc : Fin 17 → Fin p) (reg : Fin 16 ↪ Fin r) (done : Fin p) :
    Prop := ∀ i, M.code (pc i) = instruction pc reg done i

private def offset (base : Word w) : ℕ → Word w
  | 0 => base
  | n + 1 => offset base n + 1

private theorem offset_eq (base : Word w) (n : ℕ) : offset base n = base + (n : Word w) := by
  induction n with
  | zero => simp [offset]
  | succ n ih => simp [offset, ih, add_assoc]

/-- Trace of the header load. The machine reads the child-list pointer and count at `node` and
`node + 1`, then reads the seven directory words beginning at `base`. -/
def events (m : Memory w) (node base : Word w) : List (Event w) :=
  let fetch := fun addr : Word w => Event.read addr (m addr.val)
  [.tick, fetch node, .tick, fetch (node + 1), fetch base, .tick, fetch (offset base 1),
   .tick, fetch (offset base 2), .tick, fetch (offset base 3), .tick, fetch (offset base 4),
   .tick, fetch (offset base 5), .tick, fetch (offset base 6)]

theorem cost (m : Memory w) (node base : Word w) :
    countProbes (events m node base) = 9 ∧ (events m node base).length = 17 ∧
      choiceBits (events m node base) = [] := ⟨rfl, rfl, rfl⟩

/-- The header writes only the child scan's input registers. -/
def Preserved (reg : Fin 16 ↪ Fin r) (j : Fin r) : Prop :=
  ∀ z : Fin 16, z = 3 ∨ z = 6 ∨ z = 7 ∨ 9 ≤ z → j ≠ reg z

/-- State at the header continuation. The scan registers hold one, the child-list pointer and
count, and the seven directory words. All other registers, private memory, and persistent
state retain their entry values. -/
structure Ready (reg : Fin 16 ↪ Fin r) (done : Fin p) (c d : Config w p r)
    (f : Fields w) (src countValue : ℕ) : Prop where
  pc : d.pc = done
  one : d.reg (reg 3) = 1
  source : d.reg (reg 9) = (src : Word w)
  count : d.reg (reg 10) = (countValue : Word w)
  olderBase : d.reg (reg 11) = f.olderBase
  stride : d.reg (reg 12) = f.stride
  degree : d.reg (reg 13) = f.degree
  argumentStart : d.reg (reg 14) = f.argumentStart
  argumentStride : d.reg (reg 15) = f.argumentStride
  actualIn : d.reg (reg 6) = f.actualIn
  width : d.reg (reg 7) = f.width
  frame : ∀ j, Preserved reg j → d.reg j = c.reg j
  privateMem : d.privateMem = c.privateMem
  persistent : d.persistent = c.persistent

variable {M : Machine w p r k} {pc : Fin 17 → Fin p} {reg : Fin 16 ↪ Fin r} {done : Fin p}

private theorem step_at (hl : Linked M pc reg done) (i : Fin 17) {c : Config w p r}
    (hc : c.pc = pc i) :
    M.program.step c = (instruction pc reg done i).run M.publicData c := by
  change (M.code c.pc).run _ _ = _
  rw [hc, hl]

/-- Load the child scan's actual source, count and layer parameters. The prefix
preserves the bit stream and reaches the linked loop on the same external memory. -/
theorem native (hl : Linked M pc reg done) (m : Memory w) (c : Config w p r) (hc : c.pc = pc 0)
    (f : Fields w) (stored : f.Stored m (c.reg (reg 8))) (src : ℕ) (kids : List (Word w))
    (row : DFS.Row m (c.reg (reg 7)).val src kids) :
    ∃ d, Ready reg done c d f src kids.length ∧ ∀ fuel bs,
      execute M.program (fuel + 17) c m bs = (execute M.program fuel d m bs).map
        (fun rep => ⟨events m (c.reg (reg 7)) (c.reg (reg 8)) ++ rep.events, rep.result⟩) := by
  let node := c.reg (reg 7)
  let base := c.reg (reg 8)
  have srcWord : m node.val = (src : Word w) := row.2.2.1
  have countWord : m (node + 1).val = (kids.length : Word w) := by
    have hn : node.val + 1 < 2 ^ w := row.1
    have oneVal : (1 : Word w).val = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w)]
    rw [Fin.val_add, oneVal, Nat.mod_eq_of_lt hn]
    exact row.2.2.2.1
  have read (j : Fin 7) : m (offset base j.val).val = f.words j := by
    rw [offset_eq]
    exact stored j
  have path := ReadPrefix.tick (step_at hl 0 hc)
    (ReadPrefix.read (m := m) _ (step_at hl 1 rfl)
    (ReadPrefix.tick (step_at hl 2 rfl)
    (ReadPrefix.read _ (step_at hl 3 rfl)
    (ReadPrefix.read _ (step_at hl 4 rfl)
    (ReadPrefix.tick (step_at hl 5 rfl)
    (ReadPrefix.read _ (step_at hl 6 rfl)
    (ReadPrefix.tick (step_at hl 7 rfl)
    (ReadPrefix.read _ (step_at hl 8 rfl)
    (ReadPrefix.tick (step_at hl 9 rfl)
    (ReadPrefix.read _ (step_at hl 10 rfl)
    (ReadPrefix.tick (step_at hl 11 rfl)
    (ReadPrefix.read _ (step_at hl 12 rfl)
    (ReadPrefix.tick (step_at hl 13 rfl)
    (ReadPrefix.read _ (step_at hl 14 rfl)
    (ReadPrefix.tick (step_at hl 15 rfl)
    (ReadPrefix.read _ (step_at hl 16 rfl) (ReadPrefix.nil _)))))))))))))))))
  let final {d : Config w p r} {es : List (Event w)} (_ : ReadPrefix M m c es d) := d
  refine ⟨final path, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
    all_goals simp only [final]
    all_goals simp (config := { decide := true }) only [Config.put, Fin.isValue, ne_eq,
      reg.injective.eq_iff, not_false_eq_true, Function.update_of_ne, BinaryOp.eval,
      Function.update_self, Function.update_idem]
    · exact srcWord
    · exact countWord
    · exact read 0
    · exact read 1
    · exact read 2
    · exact read 3
    · exact read 4
    · exact read 5
    · exact read 6
    · intro j keep
      simp [Function.update_of_ne (keep 3 (by decide)), Function.update_of_ne (keep 6 (by decide)),
        Function.update_of_ne (keep 7 (by decide)), Function.update_of_ne (keep 9 (by decide)),
        Function.update_of_ne (keep 10 (by decide)), Function.update_of_ne (keep 11 (by decide)),
        Function.update_of_ne (keep 12 (by decide)), Function.update_of_ne (keep 13 (by decide)),
        Function.update_of_ne (keep 14 (by decide)), Function.update_of_ne (keep 15 (by decide))]
  · intro fuel bs
    simpa (config := { decide := true }) [events, offset, Config.put, reg.injective.eq_iff,
      BinaryOp.eval, final] using ReadPrefix.execute path fuel bs

end PairSimulation.NodeArguments.ChildHeader

end VPVNP
end Computability
end OAI
