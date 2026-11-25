import OAI.Hierarchy.DescentPhysicalResetLeft
import OAI.Hierarchy.DescentResetReceiverCPU

namespace OAI
/-! # The dated reset continues from its selected stencil through every private root -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod DescentGLPacked
open DescentPackedWalsh ProtocolRAM ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable (a : PhysicalReset)
local notation "v₀" => a.successor.middle
local notation "S₀" => (v₀).stencil
local notation "cap₀" => a.c/2

/-- Original signed banks and the public sizes of the measured root stage. -/
structure RootInputs where
  field : ℕ
  Ht : ℕ
  old : Fin (2*cap₀)→Fin (v₀).oldBlocks→Bank
  ratio : 0<(v₀).signedRatio
  lanes : 0<(v₀).signedLanes
  groups : (v₀).rootGroups=((v₀).rootGroups/((v₀).signedRatio*(v₀).signedLanes))*((v₀).signedRatio*(v₀).signedLanes)

/-- Reusing a physical host and old signed capacity determines the projection's full dimensions. -/
structure RootShape : Prop where
  limbs : (v₀).signedPorts=2*cap₀
  bits : (v₀).signedBits=DescentSignedCableCodec.width a.ports cap₀
  hosts : (v₀).rootHosts=(v₀).signedHosts
  groups : (v₀).rootGroups=2^(S₀).c
  lanes : (v₀).rootLanes=(v₀).signedLanes
  degree : (v₀).rootDegree=a.ports

variable (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (inputs : a.RootInputs)
local notation "P" => a.stencilPhase sh floor count hub g Y
def rootPhase (w : ℕ) :
    Projected.Receiver a.ports cap₀ (v₀).oldBlocks (v₀).rotorBits (v₀).rootDepth (S₀).c
      (v₀).signedHosts (v₀).rootGroups ((v₀).rootGroups/((v₀).signedRatio*(v₀).signedLanes))
      (v₀).signedRatio (v₀).signedLanes (v₀).high (v₀).low (S₀).t inputs.field inputs.Ht w where
  origin := (P).endAddress
  saved := ⟨(P).saved,0⟩
  stencil := ⟨(P).output,Nat.clog 2 ((v₀).signedHosts*DescentSIMDLookup.chunks (2^(S₀).c) (v₀).signedLanes)⟩
  old := inputs.old
  slots := inputs.groups
  ratio := inputs.ratio
  positive := inputs.lanes

local notation "Q" w => a.rootPhase sh floor count hub g Y inputs w

theorem projection_end (shape : a.RootShape) (w : ℕ) :
    (Q w).projectionEnd=(v₀).afterProjection (a.rebased floor) := by
  have first : (Q w).signedEnd=(v₀).afterSigned (a.rebased floor) := by
    unfold ResetMiddle.afterSigned ResetMiddle.signedCharts ResetMiddle.retileEnd
    rw [shape.bits,shape.limbs,←a.stencil_end sh floor count hub g Y]
    rfl
  unfold Projected.Receiver.projectionEnd ResetMiddle.afterProjection Projected.start
  rw [first]
  unfold ResetMiddle.projectBits ResetMiddle.projectCount
  rw [shape.bits,shape.limbs,shape.groups,shape.hosts,shape.lanes]
  rfl

theorem root_end (shape : a.RootShape) (w : ℕ) :
    (Q w).endAddress=RootTemplates.privateEnd ((v₀).afterProjection (a.rebased floor))
      (v₀).rootHosts (v₀).rootGroups (v₀).rootLanes (v₀).rootDepth (v₀).rotorBits (v₀).rootDegree := by
  unfold Projected.Receiver.endAddress RootTemplates.privateEnd
  rw [a.projection_end sh floor count hub g Y inputs shape w,shape.hosts,shape.lanes,shape.groups,shape.degree]


def throughRoots {templates : RootTemplates (v₀).rotorBits (v₀).rootDepth a.ports (2^(v₀).rootDepth) cap₀}
    (src : Bank) (R δ w : ℕ) (safe : (Q w).Fits templates) : Procedure w :=
  (a.throughStencil sh floor count hub g Y src R δ w).seq ((Q w).program (templates:=templates) safe)

def throughRootsTicks {templates : RootTemplates (v₀).rotorBits (v₀).rootDepth a.ports (2^(v₀).rootDepth) cap₀}
    (R δ w : ℕ) (safe : (Q w).Fits templates) : ℕ :=
  a.throughStencilTicks sh floor count hub g Y R δ w+(Q w).ticks (templates:=templates) safe

set_option maxHeartbeats 700000 in
theorem throughRoots_any {templates : RootTemplates (v₀).rotorBits (v₀).rootDepth a.ports (2^(v₀).rootDepth) cap₀}
    (src : Bank) (R δ w : ℕ) (safe : (Q w).Fits templates) (m : Memory w)
    (front : a.PrimeRoom floor src count R δ w) (middle : (P).Room w) :
    ∃measured,(a.throughStencil sh floor count hub g Y src R δ w).Exec m measured
      (a.throughStencilTicks sh floor count hub g Y R δ w) ∧
      (a.throughRoots (templates:=templates) sh floor count hub g Y inputs src R δ w safe).Exec m ((Q w).image (templates:=templates) safe measured)
      (a.throughRootsTicks (templates:=templates) sh floor count hub g Y inputs R δ w safe) ∧
      CheapCode (a.throughRoots (templates:=templates) sh floor count hub g Y inputs src R δ w safe) := by
  obtain ⟨_,measured,_,_,run,small⟩:=a.throughStencil_any sh floor count hub g Y src R δ w m front middle
  obtain ⟨finish,cheap,_⟩ := (Q w).any_input (templates:=templates) safe measured
  let first := a.throughStencil sh floor count hub g Y src R δ w
  let last := (Q w).program (templates:=templates) safe
  refine ⟨measured,@run,?_,?_⟩
  · exact @Procedure.Exec.then w first last m measured ((Q w).image (templates:=templates) safe measured)
      (a.throughStencilTicks sh floor count hub g Y R δ w) ((Q w).ticks (templates:=templates) safe) @run @finish
  · exact @cheap_seq w first last @small @cheap

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
