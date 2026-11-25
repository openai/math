import OAI.Hierarchy.DescentTerminalResetNodeCells

namespace OAI
/-! # The primitive digit returned at each reached reset slot -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSixParty DescentCompiler DescentResetGates DescentKernelHistory DescentEpochTagKeys
open DescentSIMDLookup DescentPackedResetRotorRoles DescentPackedZip DescentPackedColony DescentPrimitivePalette
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false

variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v₀" => a.successor
local notation "base" => a.rebased floor
local notation "F" => z.menu.F
local notation "G" => z.menu.gadget
local notation "s" => z.menu.stageBits
local notation "Z" => z.menu.grain
local notation "op" => z.menu.op
local notation "pr" => (v₀).primitive
local notation "chart" => (pr).chart
local notation "md₀" => (v₀).metadata
variable {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {q ε : ℝ} {S : AtomSchedule} {k i grain D wire hist n h C f g cut tail p : ℕ}
    {prev : Reached W G q ε S k i grain D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (menu : Runnable F op) (closed : ClosedReset prev ctl) (hp : 0<p) (whole : p∣closed.reset.unit)
    (fixed : Chronology.resetSpec closed=op) (history : Chronology.Archive W)
    (old : Encoding (Label G s Z op) (dictionary G op menu p) history.bit)
local notation "enc" => Encoding.reset op menu closed hp whole fixed history old
local notation "gate" => reachedInput G s Z op menu closed hp whole history old

variable (earlier : DescentLocalArchiveOrder.Local history.bit)
    (blocks : (chart).blocks=2^k) (hosts : (chart).hosts=S.hostSize (i+1)) (groups : (chart).groups=S.groupCount (i+1))
local notation "slot" => nodeCell z closed hp whole history earlier blocks hosts groups
local notation:max "labelWord" y:arg => DescentPrimitivePalette.token G s Z op ((enc).atNode y)
local notation:max "natWord" y:arg => ((codec («G»:=G) op).store ((enc).atNode y)).val+1

/-- The physical reset expression and the global archive label agree as packed cells,
including a query whose host or local node slot is unoccupied. -/
theorem nodeCell_token (x : Fin (chart).blocks) (j : Fin (chart).nodes)
    (rack : Fin (chart).hosts) (group : Fin (chart).groups) :
    emit G s Z op ((slot x j rack group).elim .padding gate)=
      (slot x j rack group).elim 0 (fun y=>labelWord y):=by
  cases slot x j rack group with
  | none=>rfl
  | some y=>exact reached_emit G s Z op menu closed hp whole fixed history old y

private theorem restore_digit {a b : ℕ} (same : a=b) (word : Cell b) :
    (word.val:Cell a)=word.cast (congrArg (2^·) same.symm):=by
  subst b
  apply Fin.ext
  exact Nat.mod_eq_of_lt word.isLt

/-- The exact digit of the returned chart has the global finite primitive width. -/
theorem nodeCell_digit (bitsEq : (chart).bits=printedBits G s Z op) (x : Fin (chart).blocks)
    (j : Fin (chart).nodes) (rack : Fin (chart).hosts) (group : Fin (chart).groups) :
    ((slot x j rack group).elim 0 (fun y=>natWord y):Cell (chart).bits)=
      ((slot x j rack group).elim 0 (fun y=>labelWord y)).cast (congrArg (2^·) bitsEq.symm):=by
  cases at_:slot x j rack group with
  | none=>
    apply Fin.ext
    simp
  | some y=>
    have correct : ((natWord y : ℕ) : Cell (chart).bits) =
        (labelWord y).cast (congrArg (2^·) bitsEq.symm) := by
      rw [←DescentPrimitivePalette.token_val G s Z op ((enc).atNode y)]
      exact restore_digit bitsEq _
    simpa only [Option.elim_some,Nat.cast_add,Nat.cast_one] using correct

private theorem pack_digits {a b N : ℕ} (bitsEq : a=b) (y : Fin N→Cell b) :
    (encode a N (fun j=>(y j).cast (congrArg (2^·) bitsEq.symm))).val=(encode b N y).val:=by
  subst b
  rfl

/-- The complete node page, in increasing local node order, is the primitive page expected
by the next date's archive read. -/
theorem nodeCell_page (bitsEq : (chart).bits=printedBits G s Z op) (x : Fin (chart).blocks)
    (rack : Fin (chart).hosts) (group : Fin (chart).groups) :
    (encode (chart).bits (chart).nodes (fun j=>((slot x j rack group).elim 0 (fun y=>natWord y):Cell (chart).bits))).val=
      (encode (printedBits G s Z op) (chart).nodes (fun j=>(slot x j rack group).elim 0 (fun y=>labelWord y))).val:=by
  simp only [z.nodeCell_digit menu closed hp whole fixed history old earlier blocks hosts groups bitsEq]
  exact pack_digits bitsEq _

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
