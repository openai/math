import OAI.Hierarchy.DescentOrdinaryGatherOnly
import OAI.Hierarchy.DescentDatedPhysicalOperandBanks
import OAI.Hierarchy.DescentDatedOperandWords
import OAI.Hierarchy.DescentOrdinaryRegisteredOperands

namespace OAI
/-! # Ordinary scalar arguments from prior seven-field books before signed publication -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOperandVectorArena DescentDatedPriorOperand DescentSIMDLookup DescentOperandStateBanks
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) {D k K cap w : ℕ}
    (C : References v.vector D k K cap) (floor : ℕ)
    (side : Fin v.resolver.jobs→Fin 6→Bank) (route : Fin v.resolver.jobs→Fin 3→Bank)
open scoped Fin.CommRing
set_option quotPrecheck false
local notation "B" => v.operandBanks floor side route
def scalarProgram (w : ℕ) :=((References.phase C w (v.vectorStart floor)).program).seq
  (v.operandProgram B w floor)
def scalarTicks :=(References.phase C 0 (v.vectorStart floor)).ticks+v.operandTicks B floor
def scalarImage (m : Memory w) :=v.operandState B floor (References.image C (v.vectorStart floor) m)

structure BeforeRoom (v : PhysicalOrdinary F P) (C : References v.vector D k K cap) (floor w : ℕ)
    (side : Fin v.resolver.jobs→Fin 6→Bank) (route : Fin v.resolver.jobs→Fin 3→Bank) : Prop where
  gather : References.Room C w (v.vectorStart floor)
  shape : v.VectorShape
  sides : ∀j i,(side j i).Fits w (v.normalizedEnd floor) ∧ v.resolver.rows≤(side j i).size
  routes : ∀j i,(route j i).Fits w (v.normalizedEnd floor) ∧ v.resolver.rows≤(route j i).size
  fits : v.endAddress floor<2^w
  packed : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2

theorem before_run (safe : BeforeRoom v C floor w side route) (m : Memory w) :
    (v.scalarProgram C floor side route w).Exec m (v.scalarImage C floor side route m)
      (v.scalarTicks C floor side route) ∧ CheapCode (v.scalarProgram C floor side route w) ∧
    ∀a,a<v.vectorStart floor ∨ v.endAddress floor≤a → v.scalarImage C floor side route m a=m a:=by
  have fst:=References.any C (v.vectorStart floor) m safe.gather
  have snd:=v.operand_any_from_vector floor side route (References.image C (v.vectorStart floor) m)
    safe.shape safe.sides safe.routes safe.fits safe.packed
  have low := (v.vector_before floor).trans (v.routed_le floor)
  have high : v.normalizedEnd floor≤v.endAddress floor:=v.resolver.floor_le _
  refine ⟨?_,?_,?_⟩
  · intro pcCount regCount pubCount mach
    exact Procedure.Exec.then fst.1 snd.1 mach
  · exact @cheap_seq w (References.phase C w (v.vectorStart floor)).program (v.operandProgram B w floor)
      (References.phase C w (v.vectorStart floor)).cheap snd.2.2
  · intro a ha
    exact (snd.2.1 a (ha.imp_left (fun h=>h.trans_le low))).trans (fst.2 a (ha.imp_right (fun h=>(v.routed_le floor).trans (high.trans h))))

section
attribute [local irreducible] scalarProgram scalarTicks scalarImage

def argumentsBefore (safe : BeforeRoom v C floor w side route) : NativePhase w :=
  ⟨v.scalarProgram C floor side route w,v.scalarTicks C floor side route,v.scalarImage C floor side route,
    @And.left _ _ (v.before_run C floor side route safe (fun _=>0)).2⟩

end

theorem argumentsBefore_any (safe : BeforeRoom v C floor w side route) (m : Memory w) :
    (v.argumentsBefore C floor side route safe).Runs m ∧
    ∀a,a<v.vectorStart floor ∨ v.endAddress floor≤a → (v.argumentsBefore C floor side route safe).image m a=m a:=
  ⟨(v.before_run C floor side route safe m).1,(v.before_run C floor side route safe m).2.2⟩

theorem argumentsBefore_keys (safe : BeforeRoom v C floor w side route) (m : Memory w)
    (v0 : Fin v.resolver.jobs→DescentDatedPriorOperand.Source v.resolver)
    (registered : (B).Registered v0 (References.image C (v.vectorStart floor) m))
    (pos : 0<v.resolver.lanes) (j : Fin v.resolver.jobs) :
    DescentPackedColony.Reads (Banks.wordBank v.resolver (v.normalizedEnd floor) j)
      (fun h g=>DescentPackedOperand.word ((v0 j).compiled h g)) v.resolver.lanes
      ((v.argumentsBefore C floor side route safe).image m):=
  Banks.run_words _ _ _ (v.operand_early floor side route safe.shape safe.fits safe.sides safe.routes)
    registered safe.fits pos safe.packed j
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
