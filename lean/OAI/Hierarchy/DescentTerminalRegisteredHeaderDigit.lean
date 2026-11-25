import OAI.Hierarchy.DescentArchiveCellRead
import OAI.Hierarchy.DescentPriorOperandTerminal

namespace OAI
/-! # Reading a registered pointer digit at its physical host and group -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentSIMDLookup DescentOperandStateBanks DescentPackedColony ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

/-- Once the address chart has a single chunk, the previous packed word occurs at the
plain host offset and its group digit is the original physical group. -/
theorem singleton_pitch {H G M : ℕ} (one : chunks G M=1) (positive : 0<M) (h : Fin H) (g : Fin G) :
    (row H G M (position h g positive)).val=h.val ∧ (lane g positive).val=g.val := by
  have zero : g.val/M=0:=by
    have inside : g.val/M<chunks G M:=(position h g positive).2.isLt
    rw [one] at inside
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ inside)
  have small : g.val<M:=by
    by_contra! larger
    have pos:=Nat.div_pos larger positive
    omega
  constructor
  · change (finProdFinEquiv (position h g positive)).val=_
    simp [finProdFinEquiv_apply_val,position,zero,one]
  · exact Nat.mod_eq_of_lt small

end
end Hierarchy.DescentTerminalPointerDigits

namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup DescentTerminalPointerDigits ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B)
local notation "Node" => NodeOrder.All B
local notation "L" => ports.rangeLayout

variable {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
    (label : NodeOrder.All B→Label G s Z op) (pointer : NodeOrder.All B→ℕ→Pointer)
    (flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)
local notation "slot" => slotAt ports r B number room
local notation "arguments" y => occurrences (shape.sites (y:Node).1) y.2


variable {ports r B number room shape op label pointer flags}
variable {m : Memory w} (held : Hierarchy.DescentSixParty.Chronology.DatePorts.ArchiveRead
      ports r B number room shape op label pointer flags m)
    (fmt : Widths) (capacity : fmt.nodeCapacity=some ports.nodes) (width : ∀f,fmt.pointer f=ports.operandBits)
    (positive : 0<ports.operandLanes) (packed : (ports.operandBits*ports.nodes)*ports.operandLanes≤w)
local notation "bank_" x:arg f:arg j:arg => previousBank L ports.archive.arguments x (DescentOperandStateBanks.page (Fin.castLE (by decide : 4≤7) f) j)
local notation "H" => ports.operandHosts
local notation "G₀" => ports.venue.groups
local notation "M" => ports.operandLanes

include held capacity width packed in
/-- The archived source supplies the pointer field directly at its two physical
digit indices even when this host has multiple group words. -/
theorem ArchiveRead.terminal_header_digit (x : Fin (2^ports.venue.k)) (n : Fin ports.nodes)
    (j : Fin ports.argumentsPerNode) (f : Fin 4) (h : Fin H) (g : Fin G₀) (y : Node)
    (place : slot x n h g=some y) (active : j.val<(arguments y).length) :
    fmt.nodeDigit (fmt.pointer f) n.val (lane g positive).val
      (m ((bank_ x f j).base+(row H G₀ M (position h g positive)).val)).val=(pointer y j.val).header f := by
  obtain ⟨cells,issued,atSite⟩:=ArchiveRead.headers (F:=F) (W:=W) (G:=G) held x j f
  rw [width]
  exact (fmt.nodeDigit_stored capacity (bank_ x f j) cells m issued packed positive h g n).trans
    (atSite h g n y place active)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
