import OAI.Hierarchy.DescentTerminalResetReachedRole
import OAI.Hierarchy.DescentReachedNodeCells

namespace OAI
/-! # The returned primitive bank at its actual reached coordinates -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSixParty DescentCompiler DescentResetGates DescentKernelHistory DescentEpochTagKeys
open DescentSIMDLookup DescentPackedResetRotorRoles DescentPackedZip DescentPackedColony DescentPrimitivePalette
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false

variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v" => a.successor
local notation "base" => a.rebased floor
local notation "F" => z.menu.F
local notation "G" => z.menu.gadget
local notation "s" => z.menu.stageBits
local notation "Z" => z.menu.grain
local notation "op" => z.menu.op
local notation "pr" => (v).primitive
local notation "chart" => (pr).chart
local notation "md₀" => (v).metadata
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
local notation "current" => DescentLocalArchiveOrder.reset closed p hp whole history earlier

def nodeCell (x : Fin (chart).blocks) (n : Fin (chart).nodes) (h : Fin (chart).hosts) (g : Fin (chart).groups) :
    Option (NodeOrder.All («F»:=F) next) :=
  Reached.NodeCells.whereAt closed.next next current (x.cast blocks) n (h.cast hosts) (g.cast groups)

local notation "cell" => nodeCell z closed hp whole history earlier blocks hosts groups

theorem nodeCell_some (x : Fin (chart).blocks) (j : Fin (chart).nodes) (rack : Fin (chart).hosts) (group : Fin (chart).groups)
    (site : closed.reblock.result.graph.Site) (a : ((next).recipe site).Node) :
    cell x j rack group=some ⟨site,a⟩ ↔ Reached.NodeCells.coordinate closed.next site=(rack.cast hosts,group.cast groups,x.cast blocks) ∧
      j.val=(current site a).val :=
  Reached.NodeCells.whereAt_some closed.next next current _ _ _ _ _ _

theorem nodeCell_pad (x : Fin (chart).blocks) (j : Fin (chart).nodes) (rack : Fin (chart).hosts) (group : Fin (chart).groups) :
    cell x j rack group=none ↔ ∀site,Reached.NodeCells.coordinate closed.next site=(rack.cast hosts,group.cast groups,x.cast blocks)→
      Fintype.card ((next).recipe site).Node≤j.val :=
  Reached.NodeCells.whereAt_pad closed.next next current _ _ _ _

theorem dated_canonical_role (fit : z.Room) {before mid dst : Memory w} (ran : (date z).Runs before dst)
    (operands : u.throughOperandDate.Runs before mid) (bitsEq : (chart).bits=printedBits G s Z op)
    (width : roleBits closed.reset.n≤(pr).rawBits)
    (retained : ∀x n,Source (z.roles.retained x n)
      (fun h g=>DescentResetPrimitivePage.oldWord ((cell x n h g).elim .padding gate))
      (chart).lanes (z.roleInput mid))
    (fresh : ∀x n,Source (z.roles.fresh x n)
      (fun h g=>(DescentResetPrimitivePage.localRole ((cell x n h g).elim .padding gate):Cell (pr).rawBits))
      (chart).lanes (z.roleInput mid))
    (relay : ∀x n,Source (z.roles.relay x n)
      (fun h g=>DescentResetPrimitivePage.relayFlag ((cell x n h g).elim .padding gate))
      (chart).lanes (z.roleInput mid)) (x : Fin (chart).blocks) :
    Reads ((v).terminalRole base x) (fun h g=>encode (chart).bits (chart).nodes fun j=>
      ((cell x j h g).elim 0 (fun node=>((codec («G»:=G) op).store ((enc).atNode node)).val+1):Cell (chart).bits))
      (chart).lanes dst :=
  z.dated_reached_role menu closed hp whole fixed history old fit ran operands bitsEq width cell retained fresh relay x

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
