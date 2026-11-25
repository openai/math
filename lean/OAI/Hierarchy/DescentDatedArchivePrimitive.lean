import OAI.Hierarchy.DescentRegisteredResetArchive
import OAI.Hierarchy.DescentDatedNodeCellToken
import OAI.Hierarchy.DescentDatedInheritedRegister

namespace OAI
/-! # The selected reset's final primitive archive, including all empty slots -/
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
local notation "next" => (Chronology.resetArchive closed p hp whole history).bit
local notation "enc" => Encoding.reset op menu closed hp whole fixed history old
local notation "gate" => reachedInput G s Z op menu closed hp whole history old

variable (earlier : DescentLocalArchiveOrder.Local history.bit)
    (blocks : (chart).blocks=2^k) (hosts : (chart).hosts=S.hostSize (i+1)) (groups : (chart).groups=S.groupCount (i+1))
local notation "slot" => nodeCell z closed hp whole history earlier blocks hosts groups
local notation:max "labelWord" y:arg => DescentPrimitivePalette.token G s Z op ((enc).atNode y)
local notation:max "natWord" y:arg => ((codec («G»:=G) op).store ((enc).atNode y)).val+1


open DescentSixParty.Chronology.DatePorts
local notation "ports" => DescentSixParty.Chronology.DatePorts.reset a floor u
local notation "current" => DescentLocalArchiveOrder.reset closed p hp whole history earlier
variable (placed : RangeRoom ports closed.next next)
local notation "oldOut" => slotAt ports closed.next next current placed
local notation "dx" => (congrArg (2^·) placed.radix.symm).trans blocks.symm
local notation "dg" => placed.groups.symm.trans groups.symm

private theorem move_reads {H₀ G₀ s₀ H₁ G₁ s₁ M : ℕ} {bank : Bank} {m : Memory w}
    (hs:H₁=H₀) (gs:G₁=G₀) (ss:s₁=s₀) (xs:Fin H₀→Fin G₀→Cell s₀) (ys:Fin H₁→Fin G₁→Cell s₁)
    (bits : ∀h g,(xs (h.cast hs) (g.cast gs)).val=(ys h g).val) (paid : Reads bank xs M m) :
    Reads bank ys M m:=by
  subst H₀;subst G₀;subst s₀
  have eqn:xs=ys:=funext fun h=>funext fun g=>Fin.ext (bits h g)
  exact eqn ▸ paid

private theorem move_digits {n₀ n₁ t : ℕ} (eqn:n₁=n₀) (xs:Fin n₀→Cell t) (ys:Fin n₁→Cell t)
    (same:∀i,xs (i.cast eqn)=ys i) : (encode t n₀ xs).val=(encode t n₁ ys).val:=by
  subst n₀
  rw [show xs=ys by exact funext same]

theorem registered_node_slot (nodes:(ports).nodes=(chart).nodes) (height:(ports).operandHosts=(chart).hosts)
    (x:Fin (2^(ports).venue.k)) (j:Fin (ports).nodes) (r:Fin (ports).operandHosts) (g:Fin (ports).venue.groups) :
    slot (x.cast dx) (j.cast nodes) (r.cast height) (g.cast dg)=oldOut x j r g:=by
  classical
  have small:r.val<S.hostSize (i+1):=r.isLt.trans_eq (height.trans hosts)
  simp only [nodeCell,slotAt,Reached.NodeCells.atPhysical,dite_eq_left small,Reached.NodeCells.whereAt]
  rfl

theorem dated_archive_primitive (fit : z.Room) {before mid dst : Memory w} (ran : (date z).Runs before dst)
    (operands : u.throughOperandDate.Runs before mid) (bitsEq : (chart).bits=printedBits G s Z op)
    (width : roleBits closed.reset.n≤(pr).rawBits)
    (retained : ∀x n,Source (z.roles.retained x n)
      (fun h g=>DescentResetPrimitivePage.oldWord ((slot x n h g).elim .padding gate))
      (chart).lanes (z.roleInput mid))
    (fresh : ∀x n,Source (z.roles.fresh x n)
      (fun h g=>(DescentResetPrimitivePage.localRole ((slot x n h g).elim .padding gate):Cell (pr).rawBits))
      (chart).lanes (z.roleInput mid))
    (relay : ∀x n,Source (z.roles.relay x n)
      (fun h g=>DescentResetPrimitivePage.relayFlag ((slot x n h g).elim .padding gate))
      (chart).lanes (z.roleInput mid))
    (nodes:(ports).nodes=(chart).nodes) (height:(ports).operandHosts=(chart).hosts)
    (x : Fin (2^(ports).venue.k)) :
    Reads ((ports).archive.roles.bank x.val) (fun h g=>encode (printedBits G s Z op) (ports).nodes fun j=>
      (oldOut x j h g).elim 0 (fun y=>token G s Z op ((enc).atNode y))) (ports).roleLanes dst :=by
  have exactBank : ((ports).archive.roles.bank x.val)=(v₀).terminalRole base (x.cast dx):=
    (PriorRolePages.reset_pages (v₀) base).2 (x.cast dx)
  rw [exactBank]
  have read:=z.dated_canonical_role menu closed hp whole fixed history old earlier blocks hosts groups fit ran
    operands bitsEq width retained fresh relay (x.cast dx)
  apply move_reads height dg (congrArg₂ (·*·) bitsEq.symm nodes)
    _ _ _ read
  intro h g
  apply (z.nodeCell_page menu closed hp whole fixed history old earlier blocks hosts groups bitsEq (x.cast dx)
    (h.cast height) (g.cast dg)).trans
  apply move_digits nodes
  intro j
  rw [z.registered_node_slot closed hp whole history earlier blocks hosts groups placed nodes height]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
