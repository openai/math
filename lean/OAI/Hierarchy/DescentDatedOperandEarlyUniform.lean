import OAI.Hierarchy.DescentDatedOperandOriginUniform
import OAI.Hierarchy.DescentOrdinaryStaticCore
import OAI.Hierarchy.DescentDatedOperandOriginalHeads

namespace OAI
/-! Public addresses of the original donor, path, rank, and two compact-node header programs. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentHaloWalkRAM ProtocolRAM
open DescentOrdinaryAtomFieldRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

namespace ArgumentPlan
variable (p : ArgumentPlan) (c : StaticCore)

def depotRows : DescentDatedOperandPages.Layout :=
  let e:=c.material
  ⟨e.oldHosts,e.oldGroups,e.oldLanes,e.lanes*e.blocks,e.fieldBits,c.prefixProgram.material.setup.profile⟩

def pathStart :=DescentDatedOperandPages.lastAddress c.format (depotRows c) p.originMouthEnd
def rankStart :=DescentDatedSourcePathDirectory.stop (p.pathStart c) c.material.oldHosts
  c.material.groups c.material.lanes c.format.degree
def oldStart :=DescentDatedSourcePathDirectory.Local.stop (p.rankStart c) c.material.oldHosts c.format.degree
def mouthStart :=p.oldStart c+p.resolver.nodes*2^(((p.resolver.size+2)*p.resolver.nodes)*p.resolver.lanes)
def headBound :=p.mouthStart c+p.resolver.nodes*2^((p.born.bits*p.resolver.nodes)*p.resolver.lanes)

def early (w : ℕ) : NativePhase w :=
  let H:=c.material.oldHosts
  let G:=c.material.groups
  let M:=c.material.lanes
  let D:=c.format.degree
  let original:=DescentDatedOperandPages.phase c.format (depotRows c) p.originMouthEnd w p.venue.panel
  let paths:=DescentDatedSourcePathDirectory.allPages
    (DescentDatedSourcePathDirectory.nativeBanks H G M D c.donorEnd) (p.pathStart c) H G M D w
  let ranks:=PriorHeader.rankBanks H G M D c.donorEnd
  let rank:=(DescentDatedSourcePathDirectory.Local.job ranks H D).atBase (p.rankStart c) w
  let header:=(previousHeaderPhase (p.resolver.size+2) p.resolver.nodes p.resolver.lanes
    (p.oldStart c) w).seq (previousHeaderPhase p.born.bits p.resolver.nodes p.resolver.lanes (p.mouthStart c) w)
  (((original.seq paths).seq rank).seq header)

end ArgumentPlan

variable {F I F' I' : Type} [Field F] [Field F']

theorem head_bound_plan (v : PhysicalOrdinary F I) (floor : ℕ) (A : v.ArgumentEntry)
    (m : A.Match v floor) :
    (v.bareArguments floor A m).headBound (v.staticCore floor)=v.operandHeaderEnd floor :=rfl

theorem early_plan (v : PhysicalOrdinary F I) (floor w : ℕ) (A : v.ArgumentEntry)
    (m : A.Match v floor) :
    (v.bareArguments floor A m).early (v.staticCore floor) w=v.operandEarlyPhase floor w A :=rfl

theorem early_plan_eq (v : PhysicalOrdinary F I) (u : PhysicalOrdinary F' I')
    (floor floor' w : ℕ) (A : v.ArgumentEntry) (B : u.ArgumentEntry)
    (m : A.Match v floor) (n : B.Match u floor') (common : v.bareArguments floor A m=u.bareArguments floor' B n)
    (geometry : v.staticCore floor=u.staticCore floor') :
    v.operandEarlyPhase floor w A=u.operandEarlyPhase floor' w B :=by
  rw [←v.early_plan floor w A m,←u.early_plan floor' w B n,common,geometry]

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
