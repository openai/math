import OAI.Hierarchy.DescentResetIngressPublishedPrice

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod DescentStaticWordColumn ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
variable (a : PhysicalReset) (base : ℕ) (io : Dated.Operands) (sh : a.StencilShape) (count hub : Bank)
  (g Y : ℕ) (inputs : a.RootInputs)
local notation "floor₀" => a.stageStart base
local notation "Q" w => a.rootPhase sh floor₀ count hub g Y inputs w
local notation "front" w => a.ingress.phase base w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)
variable (book : Projected.RootBook a.successor.middle.rotorBits a.successor.middle.rootDepth
  a.ports (2^a.successor.middle.rootDepth) (a.c/2) inputs.field)

local notation "src" => a.ingress.source base
local notation "st" => a.stencilPhase sh floor₀ count hub g Y

/-- The solver, the charged Walsh stencil, and the selected atlas each appear
once in the original bytecode. This equality keeps the measured atlas cost. -/
theorem incurred_root_bits (R D w : ℕ) (safe : (Q w).PreparedFits book) :
    let prior:=a.throughPublishedRoots sh floor₀ count hub g Y inputs book src R D w safe
    let ticks:=a.throughPublishedTicks sh floor₀ count hub g Y inputs book R D w safe
    ((front w).ticks+ticks+7*names ((front w).program.seq prior))*w =
      ((front w).ticks+7*names (front w).program)*w+
      (a.primeTicks floor₀ R D w+7*names (a.prime floor₀ src count R D w))*w+
      ((st).time w+7*names ((st).code w))*w+
      ((Q w).preparedTicks book safe+7*names ((Q w).preparedRoots book safe))*w := by
  dsimp only
  simp only [throughPublishedTicks,throughPublishedRoots,throughStencilTicks,throughStencil,names_seq]
  ring

def rootDateAllowance (H groups stages height shared unit copies : ℕ) :=
  H*height*unit+H*(groups*stages)*unit+copies*shared

/-- The native ingress and final prepared dictionary each have one shared
allowance, and the solver has a separate lookup and matrix allowance. -/
theorem incurred_root_budget (R D w : ℕ) (safe : (Q w).PreparedFits book)
    (H groups δ h shared inUnit primeUnit stencilUnit rootUnit stencilShares : ℕ)
    (ingress : ((front w).ticks+7*names (front w).program)*w ≤ rootDateAllowance H groups δ h shared inUnit 1)
    (prime : (a.primeTicks floor₀ R D w+7*names (a.prime floor₀ src count R D w))*w ≤ rootDateAllowance H groups δ h shared primeUnit 2)
    (stencil : ((st).time w+7*names ((st).code w))*w ≤ rootDateAllowance H groups δ h shared stencilUnit stencilShares)
    (atlas : ((Q w).preparedTicks book safe+7*names ((Q w).preparedRoots book safe))*w ≤ rootDateAllowance H groups δ h shared rootUnit 1) :
    let prior:=a.throughPublishedRoots sh floor₀ count hub g Y inputs book src R D w safe
    let ticks:=a.throughPublishedTicks sh floor₀ count hub g Y inputs book R D w safe
    ((front w).ticks+ticks+7*names ((front w).program.seq prior))*w≤
      rootDateAllowance H groups δ h shared (inUnit+primeUnit+stencilUnit+rootUnit) (4+stencilShares) := by
  refine (a.incurred_root_bits base io sh count hub g Y inputs book R D w safe).le.trans ?_
  refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ingress prime) stencil) atlas).trans ?_
  apply le_of_eq
  unfold rootDateAllowance
  ring

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
