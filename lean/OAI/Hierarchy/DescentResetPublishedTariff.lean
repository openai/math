import OAI.Hierarchy.DescentResetPrimeTariff
import OAI.Hierarchy.DescentPreparedSignedTariff
import OAI.Hierarchy.DescentPhysicalResetBooks

namespace OAI
/-! The complete reset up to the published roots has three consecutive paid computations. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.PackedFlow.Canvas DescentFallbackPeriod DescentPackedWalsh
open ProtocolRAM DescentStaticWordColumn ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable (a : PhysicalReset) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (inputs : a.RootInputs)
local notation "v" => a.successor.middle
local notation "Q" w => a.rootPhase sh floor count hub g Y inputs w
local notation "st" => a.stencilPhase sh floor count hub g Y


def publishedBill (book : Projected.RootBook a.successor.middle.rotorBits a.successor.middle.rootDepth a.ports (2^a.successor.middle.rootDepth) (a.c/2) inputs.field) (src : Bank) (R D w : ℕ) :=
  let E:=a.estimator floor
  (a.primeCanvas floor src count D).fee a.hosts a.ports R a.high a.low a.bits a.short a.lanes w+
    (E.installedTicks+7*names (E.installedCPU w))*w+
    ((st).time w+7*names ((st).code w))*w+(Q w).wholeBill book*w

theorem through_published_price (book : Projected.RootBook a.successor.middle.rotorBits a.successor.middle.rootDepth a.ports (2^a.successor.middle.rootDepth) (a.c/2) inputs.field) (src : Bank) (R D w : ℕ) (safe : (Q w).PreparedFits book) :
    (a.throughPublishedTicks sh floor count hub g Y inputs book R D w safe+
      7*names (a.throughPublishedRoots sh floor count hub g Y inputs book src R D w safe))*w≤
        a.publishedBill sh floor count hub g Y inputs book src R D w := by
  have roots:=Nat.mul_le_mul_right w ((Q w).whole_price book safe)
  have front:=a.prime_invoice floor src count R D w
  simp only [throughPublishedTicks,throughPublishedRoots,throughStencilTicks,throughStencil,names_seq]
  unfold publishedBill
  nlinarith only [front,roots]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
