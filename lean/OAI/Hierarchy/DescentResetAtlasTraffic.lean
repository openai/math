import OAI.Hierarchy.DescentResetPreparedScale
import OAI.Hierarchy.DescentPhysicalResetAtlas

namespace OAI
/-! All signed rows, repeats, paid reservations, and root plans of the actual dated atlas. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentPackedWalsh DescentFallbackPeriod DescentSIMDLookup DescentGLPacked.BankImage.SignedFields
open DescentSixParty.Chronology DescentStaticWordColumn ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} (z : a.Atlas) (sh : a.StencilShape) (floor : ℕ)
    (count hub : Bank) (g Y : ℕ) (roots : a.RootInputs)
local notation "m" => a.successor.middle
local notation "S" => (m).stencil
local notation "rc" w => a.rootPhase sh floor count hub g Y roots w
local notation "book" w => atlasBook z sh floor count hub g Y roots w
local notation "args" => Projected.Receiver.arityLimit a.ports (2^(m).rootDepth) (a.c/2) (m).rotorBits (m).rootDepth

/-- Numeric facts about a placed atlas. All ten quantities concern fixed row counts
or the bit widths of concrete instructions, and carry no execution or pricing hypothesis. -/
structure Atlas.Shape (a : PhysicalReset) (field u payload : ℕ) : Prop where
  groups : a.successor.middle.rootGroups=2^a.successor.middle.stencil.c
  rows : 2^a.successor.middle.high=chunks a.successor.middle.rootGroups a.successor.middle.signedLanes
  ratio : a.successor.middle.signedRatio ≤ payload+1
  lanes : a.successor.middle.signedLanes ≤ payload
  blocks : a.successor.middle.oldBlocks=2^a.successor.middle.rootDepth
  oldKey : DescentSignedCableCodec.width a.ports (a.c/2)*
    (a.successor.middle.signedRatio*a.successor.middle.signedLanes) ≤ payload/2
  matrixKey : (a.successor.middle.high+a.successor.middle.low)*(a.successor.middle.high+a.successor.middle.low) ≤ payload/2
  glKey : (DescentSignedCableCodec.width a.ports (a.c/2)+DescentSignedCableCodec.width a.ports (a.c/2))*
    2^a.successor.middle.low ≤ payload/2
  joinKey : joinWidth (DescentSignedCableCodec.width a.ports (a.c/2)) a.successor.middle.oldBlocks*
    a.successor.middle.signedLanes ≤ payload/2
  queryKey : Projected.maxBits a.successor.middle.stencil.t a.ports (a.c/2) (2^a.successor.middle.rootDepth)*
    a.successor.middle.signedLanes ≤ payload/2
  lookupKey : (field*(Projected.Receiver.arityLimit a.ports (2^a.successor.middle.rootDepth) (a.c/2)
    a.successor.middle.rotorBits a.successor.middle.rootDepth+1))*a.successor.middle.signedLanes ≤ payload/2
  copyKey : a.successor.middle.stencil.n*a.successor.middle.signedLanes ≤ payload/2
  reserveKey : a.successor.middle.stencil.total ≤ payload/2
  arity : Projected.Receiver.arityLimit a.ports (2^a.successor.middle.rootDepth) (a.c/2)
    a.successor.middle.rotorBits a.successor.middle.rootDepth ≤ u
  basis : a.successor.middle.high+a.successor.middle.low ≤ u
  stencil : a.successor.middle.stencil.m ≤ u

theorem Atlas.atlas_traffic (payload u w : ℕ) (size : Atlas.Shape a roots.field u payload)
    (space : (rc w).PreparedFits (book w)) :
    (rc w).preparedTicks (book w) space+7*names ((rc w).preparedRoots (book w) space) ≤
      (Projected.Receiver.rootCoefficient a.ports (m).rotorBits roots.Ht u).total 1 1 1*
      ((m).signedHosts+(m).signedHosts*chunks (m).rootGroups (m).signedLanes+(payload+1)*2^(payload/2)) := by
  let phase:=a.stencilPhase sh floor count hub g Y
  let E:=a.estimator floor
  let code : DescentResetHostSize.Code (m).rootDepth:=⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩
  let page : RootPage (m).rootDepth (2^(m).rotorBits):=(false,.inr (code,none))
  have digits:roots.field ≤ payload/2 := by
    have first:=Nat.le_mul_of_pos_right roots.field (Nat.succ_pos args)
    exact (first.trans (Nat.le_mul_of_pos_right _ roots.lanes)).trans size.lookupKey
  have rows:=size.rows
  rw [size.groups] at rows
  have out:=(rc w).prepared_traffic E phase.S phase.X phase.base phase.bank g z.directions z.hostIndex
    (.lit (a.c/2)) a.depthCut a.classBound a.fullBudget phase.S.total a.ports z.board z.packet z.C
    z.groupDigits z.batches z.layerBits z.factor z.primitive page payload size.groups rows size.ratio
    size.lanes size.oldKey size.matrixKey size.glKey size.joinKey size.queryKey size.lookupKey size.copyKey
    size.reserveKey digits
  let read:=Projected.Receiver.readWork phase.S.m phase.X.count (.lit (a.c/2))
  have readFit:read ≤ 500+23*u := by
    change 400+23*(S).m+(1+5)+1 ≤ _
    have fact:=Nat.mul_le_mul_left 23 size.stencil
    omega
  have dim:E.dim ≤ u := by
    change a.high+a.low ≤ u
    simpa only [← sh.dimension] using size.stencil
  have localCost:=Projected.Receiver.issued_coefficient a.ports (a.c/2) (m).rotorBits
    (m).rootDepth (m).high (m).low roots.Ht E.dim read u size.arity size.basis dim readFit
  have paid:=(rc w).whole_price (book w) space
  apply (paid.trans out).trans
  rw [size.groups]
  apply Nat.mul_le_mul_right
  rw [size.blocks]
  exact localCost

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
