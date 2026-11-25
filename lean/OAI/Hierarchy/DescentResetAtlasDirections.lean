import OAI.Hierarchy.DescentPhysicalResetAtlas
import OAI.Hierarchy.DescentResetMiddleCalendar

namespace OAI
/-! # The actual post-remix peer and host tables used at every reset root -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.Atlas
open DescentSixParty DescentPackedColony DescentPlainTerminal.Suffix DescentResetGates DescentSIMDLookup
open ProtocolRAM ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

/-- Preserve all four physical port banks under an equality of their degree indices. -/
def sameDegree {d cap : ℕ} (e : d=cap) (P : Ports d) : Ports cap :=
  ⟨fun i=> P.ids (Fin.cast e.symm i),P.roster,P.offsets,P.chunks⟩

theorem mounted_sameDegree {d cap H G M w : ℕ} (e : d=cap) (P : Ports d)
    (rs : Fin H→Fin d→Option (Fin H)) (mem : Memory w) (old : Mounted P rs mem G M) :
    Mounted (sameDegree e P) (fun v i=> rs v (Fin.cast e.symm i)) mem G M := by
  subst cap
  exact old

theorem accessible_sameDegree {d cap H G M w floor : ℕ} (e : d=cap) (P : Ports d)
    (prior : Bank) (old : Accessible P prior H G M w floor) :
    Accessible (sameDegree e P) prior H G M w floor := by
  subst cap
  exact old

variable (a : PhysicalReset) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ)
local notation "phase" => a.stencilPhase sh floor count hub g Y
local notation "py" => (phase).S.chosen (phase).base (phase).bank (phase).X.roster

def directionsOf (degree : (phase).S.degree=a.ports) : Ports a.ports :=
  sameDegree degree (py).ports

def hostIndexOf : Bank:=((phase).S.header (phase).base).pos

/-- The static atlas uses the same original roster installed by the suffix split pass.
Its host ID is the public row of the measured header at the chosen root group pitch. -/
def fromStencil (degree : (phase).S.degree=a.ports) (boardDegree instructionBits : ℕ)
    (board : NonlinearExpanders.Graph a.successor.middle.rotorBits boardDegree)
    (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^a.successor.middle.rotorBits)→Cell instructionBits) : a.Atlas :=
  ⟨boardDegree,instructionBits,board,packet,C,groupDigits,batches,layerBits,factor,primitive,
    directionsOf a sh floor count hub g Y degree,hostIndexOf a sh floor count hub g Y⟩

theorem mounted (degree : (phase).S.degree=a.ports) {w : ℕ}
    (rs : Fin (phase).S.hosts→Fin (phase).S.degree→Option (Fin (phase).S.hosts)) (mem : Memory w)
    (prior : Mounted (py).ports rs mem (2^(phase).S.c) (phase).S.M) :
    Mounted (directionsOf a sh floor count hub g Y degree)
      (fun v q=> rs v (Fin.cast degree.symm q)) mem (2^(phase).S.c) (phase).S.M :=
  mounted_sameDegree degree _ rs mem prior

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.Atlas

end OAI
