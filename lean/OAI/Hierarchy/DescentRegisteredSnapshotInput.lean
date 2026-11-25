import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentRegisteredSnapshotDirectory
import OAI.Hierarchy.DescentScheduledPaddedReceipt

namespace OAI
/-! # Source of the graph and population on the snapshot census's actual padded input -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler DescentPackedWalsh
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F V : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
  {d : ℕ} {bits : V→ℕ} {W : MarkedWorld F d V bits} {n degree k i grain D wire hist w : ℕ}
  {q ε : ℝ} (menu : Menu n degree) (cur : Position)
  (r : Reached W G q ε S k i grain D wire hist)
local notation "outer" => scheduledAtPorts G S menu.board k menu.tail i menu.p menu.f menu.gain menu.drift
  menu.degreeLimit menu.payload menu.ordinary menu.op (S.firstWidth G.b menu.p) (S.grainAt G.b menu.p 0)
  cur.ports cur.floor
local notation "pub" => priorArchivePhase G S menu.board k menu.tail i menu.p menu.f menu.gain menu.drift
  menu.degreeLimit menu.payload menu.ordinary menu.op (S.firstWidth G.b menu.p) (S.grainAt G.b menu.p 0)
  cur.ports cur.floor w
local notation "raw" => previousArchiveLayout G S menu.board k menu.tail i menu.p menu.f menu.gain menu.drift
  menu.degreeLimit menu.payload menu.ordinary menu.op (S.firstWidth G.b menu.p) (S.grainAt G.b menu.p 0)
  cur.ports cur.floor

/-- The census reads the preceding graph and its count after the actual prefix
pad. This part of the reset does not depend on the actor ranks being proved. -/
theorem snapshot_padded_held (geo : Geometry G S menu k w i cur)
    (cap : cur.ports.venue.cap=r.placement.cap) (space : (outer).fullEnd<2^w)
    (m : Memory w) (seen : cur.ports.held r cur.floor m) :
    (pub).Runs m ∧ cur.ports.held r (outer).priorStart ((pub).image m) := by
  have begin_ : cur.floor≤(outer).priorStart := (outer).stages.1
  have wide := (outer).stages.2.trans_lt space
  have native : cur.ports.archive.Fits raw cur.floor := geo.archive.data (outer).inner.successor.setup.retained
  have home : cur.floor<2^w := begin_.trans_lt wide
  have safe : ∀j,(cur.ports.archive.prior raw j).Fits w cur.floor :=
    (raw).prior_registers cur.ports.archive.seed cur.ports.archive.nodeBase cur.ports.archive.arguments
      cur.floor w native.1 native.2 home
  have tokens : ∀j : Fin (2^k),(cur.ports.archive.roles.bank j.val).Fits w cur.floor :=
    fun j=>cur.ports.archive.roles.fits w cur.floor j.val (j.isLt.trans_le geo.archive.blocks) geo.archive.roles home
  obtain ⟨go,save⟩:=cur.ports.full_pad_any k cur.floor (cur.ports.archive.prior raw)
    (fun j=>cur.ports.archive.roles.bank j.val) m safe tokens wide
  refine ⟨go,?_⟩
  have count : cur.ports.archive.count.base<cur.floor :=
    (Nat.lt_add_of_pos_right (Nat.two_pow_pos cur.ports.archive.count.bits)).trans_le geo.room.header.count.2.2
  exact cur.ports.held_below r cur.floor (outer).priorStart m ((pub).image m) seen count geo.room.wires
    geo.format.width cap geo.room.population.groups begin_ (fun j hj=>save j (.inl hj))

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
