import OAI.Hierarchy.DescentPrimitiveReachedRole
import OAI.Hierarchy.DescentTerminalResetRoleArity

namespace OAI
/-! # Reading the archived primitive role from the final memory of a reset date -/
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

/-- The old, fresh and relay source columns are observed at the true input to the primitive
writer. The later metadata issue preserves its entire output bank, including zero slots. -/
theorem dated_reached_role (fit : z.Room) {before mid dst : Memory w}
    (ran : (date z).Runs before dst) (operands : u.throughOperandDate.Runs before mid)
    (bitsEq : (chart).bits=printedBits G s Z op) (width : roleBits closed.reset.n≤(pr).rawBits)
    (whereAt : Fin (chart).blocks→Fin (chart).nodes→Fin (chart).hosts→Fin (chart).groups→
      Option (NodeOrder.All («F»:=F) next))
    (retained : ∀x n,Source (z.roles.retained x n)
      (fun h g=>DescentResetPrimitivePage.oldWord ((whereAt x n h g).elim .padding gate))
      (chart).lanes (z.roleInput mid))
    (fresh : ∀x n,Source (z.roles.fresh x n)
      (fun h g=>(DescentResetPrimitivePage.localRole ((whereAt x n h g).elim .padding gate):Cell (pr).rawBits))
      (chart).lanes (z.roleInput mid))
    (relay : ∀x n,Source (z.roles.relay x n)
      (fun h g=>DescentResetPrimitivePage.relayFlag ((whereAt x n h g).elim .padding gate))
      (chart).lanes (z.roleInput mid))
    (x : Fin (chart).blocks) :
    Reads ((v).terminalRole base x) (fun h g=>encode (chart).bits (chart).nodes fun j=>
      ((whereAt x j h g).elim 0 (fun node=>((codec («G»:=G) op).store ((enc).atNode node)).val+1):Cell (chart).bits))
      (chart).lanes dst := by
  rw [PhysicalReset.date_image z fit ran operands]
  have below: (v).primitiveEnd base≤a.endAddress floor:=((v).terminal_order base).2.2
  have source:=issued_reached G s Z op menu closed hp whole fixed history old (pr) ((v).birthEnd base)
    z.roles (z.roleInput mid) fit.roleFields (below.trans_lt fit.endFits) bitsEq width
    whereAt retained fresh relay x
  have kept:=((md₀).chart.metadataAny ((v).primitiveEnd base) (md₀).paidBits (md₀).spanBits
    (paid u) z.spans (z.tokenImage (z.roleInput mid)) fit.count fit.spans fit.endFits).2.1
  intro j
  obtain ⟨bound,size⟩:=(v).terminal_role_room base fit.endFits x
  have lo:=bound.2.2
  have inside:(row _ _ _ j).val<(chart).rows:=(row _ _ _ j).isLt
  have addr:((v).terminalRole base x).base+(row _ _ _ j).val<(v).primitiveEnd base:=by omega
  exact (kept _ (.inl addr)).trans (source j)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
