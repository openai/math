import OAI.Hierarchy.DescentOrdinaryArgumentPhaseUnique
import OAI.Hierarchy.DescentDatedMouthPersistence

namespace OAI
/-! The actor origin and newborn mouth use the same public references as the argument gather. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPackedActorMask DescentHaloWalkRAM
open DescentOrdinaryOriginMask DescentOrdinaryOriginPorts DescentSIMDLookup DescentOrdinaryBorn
open DescentPackedColony DescentOperandVectorArena DescentOrdinaryReferenceInputs ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

namespace ArgumentPlan
variable (p : ArgumentPlan)

def originChart : DescentOrdinaryOriginMask.Return :=
  let C:=p.reference
  let V:=p.vector
  let N:=nodes (breadth C.degree*2^C.k) C.oldNodes C.capacity
  ⟨C.degree,C.k,C.oldNodes,C.capacity,p.resolver.nodes,Nat.clog 2 (N+1),
    V.hosts,V.lows,V.groups,V.radix,V.lanes⟩

def portFloor :=p.originChart.finish p.routedStart
def portEnd :=DescentOrdinaryOriginPorts.endAddress p.originChart p.portFloor

def mouthChart : DescentOrdinaryMouthReturn.Layout :=
  ⟨p.born,p.reference.degree,p.reference.k,p.reference.oldNodes,p.resolver.nodes,p.vector.lows,
    p.vector.groups,p.vector.radix,p.vector.lanes,p.newBlocks⟩

def originMouthEnd :=
  let B:=p.born
  let V:=p.vector
  let n:=B.args*3
  let a:=B.bits*p.resolver.nodes
  let raw:=RolePorts.endAddress B 0+2^Nat.clog 2 (n*DescentVectorBookReshape.sourceWords B.hosts V.lows V.groups V.lanes)
  p.portEnd + (DescentVectorBookReshape.output raw n B.hosts V.lows V.groups V.radix a V.lanes+
    n*DescentVectorBookReshape.rows B.hosts V.lows V.groups V.radix V.lanes+
    2^Nat.clog 2 ((B.hosts*V.lows)*chunks V.groups V.lanes))

private def castCapacity {D k K c d : ℕ} (h : c=d) (r : Refs D k K c) : Refs D k K d := h ▸ r

def mouthRefs (arg : Fin p.born.args) (low : Fin p.vector.lows) : p.mouthChart.Ref :=
  let r:=p.directory.refs (finProdFinEquiv ((0:Fin 7),arg.cast p.newArgs)) low
  castCapacity p.newCap.symm r

def originAndMouth (outBits w : ℕ) (pg : Fin (7*p.vector.operands)) : NativePhase w :=
  let R:=p.originChart
  let actor:=R.phase (p.directory.refs pg) p.routedStart w
  let ports : NativePhase w :=
    ⟨DescentOrdinaryOriginPorts.program R outBits p.portFloor w,4+10*words R,
      DescentOrdinaryOriginPorts.image R outBits p.portFloor,DescentStaticWordColumn.cheap w p.portFloor _ _⟩
  (actor.seq ports).seq (p.mouthChart.phase (p.chip.bank p.chipStart) p.portEnd w p.mouthRefs)

end ArgumentPlan

variable {F I F' I' : Type} [Field F] [Field F']

def bareArguments (v : PhysicalOrdinary F I) (floor : ℕ) (A : v.ArgumentEntry)
    (m : A.Match v floor) :=v.argumentPlan floor A m (fun _ _=>.row)

theorem mouth_end_plan (v : PhysicalOrdinary F I) (floor : ℕ) (A : v.ArgumentEntry)
    (m : A.Match v floor) :
    (v.bareArguments floor A m).originMouthEnd=v.originMouthEnd floor :=rfl

theorem origin_mouth_plan (v : PhysicalOrdinary F I) (floor outBits w : ℕ) (A : v.ArgumentEntry)
    (m : A.Match v floor) (pg : Fin (7*v.vector.operands)) :
    (v.bareArguments floor A m).originAndMouth outBits w pg =
    v.originAndMouth floor w A m outBits ((A.directory v floor m).refs pg) :=rfl

private theorem origin_pages_eq {p q : ArgumentPlan} (common : p=q) {bits₁ bits₂ : ℕ}
    (commonBits : bits₁=bits₂) (w : ℕ) (i : Fin (7*p.vector.operands))
    (j : Fin (7*q.vector.operands)) (commonPage : i.val=j.val) :
    p.originAndMouth bits₁ w i=q.originAndMouth bits₂ w j :=by
  subst q
  subst bits₂
  exact congrArg _ (Fin.ext commonPage)

theorem origin_mouth_plan_eq (v : PhysicalOrdinary F I) (u : PhysicalOrdinary F' I')
    (floor floor' b b' w : ℕ) (A : v.ArgumentEntry) (B : u.ArgumentEntry)
    (m : A.Match v floor) (n : B.Match u floor') (i : Fin (7*v.vector.operands))
    (j : Fin (7*u.vector.operands)) (same : v.bareArguments floor A m=u.bareArguments floor' B n)
    (width : b=b') (page : i.val=j.val) :
    v.originAndMouth floor w A m b ((A.directory v floor m).refs i)=
      u.originAndMouth floor' w B n b' ((B.directory u floor' n).refs j) :=by
  rw [←v.origin_mouth_plan,←u.origin_mouth_plan]
  exact origin_pages_eq same width w i j page

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
