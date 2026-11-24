import OAI.Computability.VPVNP.PairNodeArguments
import OAI.Computability.VPVNP.PairSimulationAssembly
import OAI.Computability.VPVNP.PairSimulationPrivateSlices

/-!
# Reading an old site's descriptor address for a child visit

The next word in a placement row names an old descriptor. Its ordinal within the
old layer identifies the first outgoing port. Its absolute address identifies
the private interval for this child's half-wire guesses. The seven instructions
read one external word and preserve the unconsumed choice bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildAddress

open BurstRAM BurstRAM.PrivateRAM Compression LocalHistory CompressorRecords
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.tick ReadPrefix.read ReadPrefix.nil ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {w p r k a g : ℕ}

/-- Seven instructions that read the next child descriptor, advance the placement-row pointer,
and compute both the child's first outgoing port and its private argument base. -/
def instruction (pc : Fin 7 → Fin p) (reg : Fin 16 ↪ Fin r) (done : Fin p) :
    Fin 7 → Instr w p r k :=
  ![.readExternal (reg 2) (reg 9) (pc 1),
    .binary .add (reg 9) (reg 9) (reg 3) (pc 2),
    .binary .sub (reg 8) (reg 2) (reg 11) (pc 3),
    .binary .div (reg 8) (reg 8) (reg 12) (pc 4),
    .binary .mul (reg 8) (reg 8) (reg 13) (pc 5),
    .binary .mul (reg 2) (reg 2) (reg 15) (pc 6),
    .binary .add (reg 2) (reg 14) (reg 2) done]

theorem resize_instruction (pc : Fin 7 → Fin p) (reg : Fin 16 ↪ Fin r) (done : Fin p)
    (i : Fin 7) : (instruction (w := 1) (k := k) pc reg done i).resize w =
      instruction pc reg done i := by fin_cases i <;> rfl

/-- The seven supplied machine labels contain the child-address instructions with the specified
register embedding and continuation. -/
def Linked (M : Machine w p r k) (pc : Fin 7 → Fin p) (reg : Fin 16 ↪ Fin r) (done : Fin p) :
    Prop := ∀ i, M.code (pc i) = instruction pc reg done i

/-- Trace of a child-address lookup, consisting of the external read of the descriptor at `ptr`
followed by six arithmetic ticks. -/
def events (m : Memory w) (ptr : Word w) : List (Event w) :=
  [.read ptr (m ptr.val), .tick, .tick, .tick, .tick, .tick, .tick]

theorem cost (m : Memory w) (ptr : Word w) :
    countProbes (events m ptr) = 1 ∧ (events m ptr).length = 7 ∧ choiceBits (events m ptr) = [] :=
  ⟨rfl, rfl, rfl⟩

variable {M : Machine w p r k} {pc : Fin 7 → Fin p} {reg : Fin 16 ↪ Fin r} {done : Fin p}

private theorem step_at (hl : Linked M pc reg done) (i : Fin 7) {c : Config w p r}
    (hc : c.pc = pc i) :
    M.program.step c = (instruction pc reg done i).run M.publicData c := by
  change (M.code c.pc).run _ _ = _
  rw [hc, hl]

/-- The child setup preserves the parent's count, the incidence tables, the other
configuration registers, all private words, and the external memory. -/
theorem native (hl : Linked M pc reg done) (m : Memory w) (c : Config w p r)
    (hc : c.pc = pc 0) (hone : c.reg (reg 3) = 1) :
    let ptr := c.reg (reg 9)
    let node := m ptr.val
    ∃ d, d.pc = done ∧ d.reg (reg 2) = c.reg (reg 14) + node * c.reg (reg 15) ∧
      d.reg (reg 8) = BinaryOp.div.eval (node - c.reg (reg 11)) (c.reg (reg 12)) *
        c.reg (reg 13) ∧ d.reg (reg 9) = ptr + 1 ∧
      (∀ j, j ≠ reg 2 → j ≠ reg 8 → j ≠ reg 9 → d.reg j = c.reg j) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      ∀ fuel bs, execute M.program (fuel + 7) c m bs =
        (execute M.program fuel d m bs).map
          (fun rep => ⟨events m ptr ++ rep.events, rep.result⟩) := by
  intro ptr node
  have path := ReadPrefix.read (M := M) (m := m) (c := c) ptr (step_at hl 0 hc)
    (ReadPrefix.tick (step_at hl 1 rfl) (ReadPrefix.tick (step_at hl 2 rfl)
      (ReadPrefix.tick (step_at hl 3 rfl) (ReadPrefix.tick (step_at hl 4 rfl)
        (ReadPrefix.tick (step_at hl 5 rfl) (ReadPrefix.tick (step_at hl 6 rfl)
          (ReadPrefix.nil _)))))))
  refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ReadPrefix.execute path⟩
  · rfl
  · simp (config := { decide := true })
      [Config.put, reg.injective.eq_iff, BinaryOp.eval, node, ptr]
  · simp (config := { decide := true })
      [Config.put, reg.injective.eq_iff, BinaryOp.eval, node, ptr]
  · simp (config := { decide := true })
      [Config.put, reg.injective.eq_iff, BinaryOp.eval, hone, ptr]
  · intro j h₂ h₈ h₉
    simp [Config.put, Function.update_of_ne h₂, Function.update_of_ne h₈, Function.update_of_ne h₉]
  · rfl
  · rfl

/-- Dividing the descriptor offset by its positive stride recovers the old site
ordinal. Multiplying by the old degree gives the port used by the incidence reader. -/
theorem firstPort_eq (X : State a g) (u : X.network.Site) (node olderBase stride : Word w)
    (hnode : node.val = olderBase.val + stride.val * ((siteOrder X).entries.symm u).val)
    (hstride : 0 < stride.val) :
    BinaryOp.div.eval (node - olderBase) stride * ((2 ^ a : ℕ) : Word w) =
      IncidenceDirectory.actualPort X (u, 0) := by
  have lower : olderBase ≤ node := show olderBase.val ≤ node.val by omega
  have quotient : (node - olderBase).val / stride.val = ((siteOrder X).entries.symm u).val := by
    rw [Fin.sub_val_of_le lower, hnode, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hstride]
  have word : BinaryOp.div.eval (node - olderBase) stride =
      (((siteOrder X).entries.symm u).val : Word w) := by
    change Fin.ofNat _ ((node - olderBase).val / stride.val) = _
    rw [quotient]
    rfl
  rw [word, ← Nat.cast_mul]
  apply congrArg (fun n : ℕ => (n : Word w))
  change ((bitWordFinEquiv g u.2).val + 2 ^ g * (X.baseIndex u.1).val) * 2 ^ a =
    ((X.baseIndex u.1).val * 2 ^ g + (bitWordFinEquiv g u.2).val) * 2 ^ a + 0
  ring

end PairSimulation.NodeArguments.ChildAddress

end VPVNP
end Computability
end OAI
