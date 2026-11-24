import OAI.Computability.VPVNP.PrimedInputRAMFlowRun
import OAI.Computability.VPVNP.PrimedInputRAMAddresses

/-!
# Finite word code for identifying a directed-message sender

This block reads the current site and incident position from registers 23
and 25. Registers 32, 33 and 34 report whether the port is connected and
the site and local offset of the sender. The triangular layer search scans
successive phase sizes using subtraction, so its intermediate counters fit
in a word whenever the ordinal does.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.PortCode

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM RAMLayout

/-- Structured word code for resolving a message port, with 48 private registers and 16 public
words. -/
abbrev Block := Flow 48 16

/-- Emit one register-copy instruction in the port resolver. -/
def copy (dst src : Fin 48) : Block := .line (.copy dst src)
/-- Emit one instruction that applies the given binary word operation to two registers. -/
def binary (op : BinaryOp) (dst a b : Fin 48) : Block := .line (.binary op dst a b)
/-- Emit one instruction loading a public port-layout word into a private register. -/
def publicWord (dst : Fin 48) (i : Fin 16) : Block := .line (.publicWord dst i)

/-- One iteration removes the next complete triangular row. -/
def scanStep : Block := .seq (binary .add 41 41 1) (binary .sub 40 40 41)

/-- Register 40 is the residual exchange ordinal, 41 is the current phase.
If the residual is at most the phase, the residual itself is the step. -/
def scan : Block := .whileLt 41 40 scanStep

/-- Resolve a sorting receive port by decoding its triangular exchange ordinal, flipping the
partner bit of the site index and subtracting one block from the port offset. -/
def receiveSort : Block :=
  .seq (binary .div 40 38 2) <|
  .seq (copy 41 0) <|
  .seq scan <|
  .seq (binary .sub 42 41 40) <|
  .seq (binary .shiftLeft 42 1 42) <|
  .seq (binary .bitXor 33 23 42) (binary .sub 34 25 37)

/-- Decode the sorting block number from the port offset. An even block uses the sending site,
while an odd block resolves the corresponding receive port to its sender. -/
def sort : Block :=
  .seq (publicWord 37 13) <|
  .seq (binary .sub 38 25 36) <|
  .seq (binary .div 38 38 37) <|
  .seq (binary .mod 39 38 2) (.ifEq 39 0 (copy 32 1) receiveSort)

/-- Test whether the site has a successor. Its outgoing port is connected precisely before the
last site. -/
def successorSend : Block :=
  .seq (binary .sub 37 7 1) (.ifLt 23 37 (copy 32 1) (copy 32 0))

/-- Mark the incoming successor port as disconnected at site zero. At a later site use the
preceding site and its outgoing port offset. -/
def successorReceive : Block :=
  .ifEq 23 0 (copy 32 0) (.seq (binary .sub 33 23 1) (binary .sub 34 25 35))

/-- The instruction table is independent of every word width and loop bound. -/
def program : Block :=
  .seq (copy 32 1) <|
  .seq (copy 33 23) <|
  .seq (copy 34 25) <|
  .seq (publicWord 35 14) <|
  .seq (publicWord 36 15) (.ifLt 25 35 successorSend (.ifLt 25 36 successorReceive sort))

/-- Decode registers 32 through 34 into an optional pair of sender site and local offset. -/
def result {w : ℕ} (rs : Regs w 48) : Option (ℕ × ℕ) :=
  if (rs 32).val = 0 then none else some ((rs 33).val, (rs 34).val)

/-- Register contract on entry. The other registers may contain any word. -/
structure Input {w : ℕ} (d H : ℕ) (v : Fin (2 ^ d)) (k : Fin (width d H w))
    (pub : Fin 16 → Word w) (rs : Regs w 48) : Prop where
  zero : (rs 0).val = 0
  one : (rs 1).val = 1
  two : (rs 2).val = 2
  sites : (rs 7).val = 2 ^ d
  site : (rs 23).val = v.val
  offset : (rs 25).val = k.val
  block : (pub 13).val = blockBits H w
  first : (pub 14).val = 8 * w
  base : (pub 15).val = 16 * w

theorem layerCount_next (p : ℕ) : layerCount (p+1) = layerCount p + (p+1) := by
  rw [layerCount, Nat.choose_succ_succ (p+1) 1, Nat.choose_one_right, Nat.add_comm]
  rfl

theorem layerCount_mono : Monotone layerCount :=
  fun _ _ h ↦ Nat.choose_le_choose 2 (Nat.succ_le_succ h)

end PrimedInputRAM.PortCode

end VPVNP
end Computability
end OAI
