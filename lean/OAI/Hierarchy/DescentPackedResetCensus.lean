import OAI.Hierarchy.DescentPackedStageCensus
import OAI.Hierarchy.DescentGrainMeasurements
import OAI.Hierarchy.DescentPackedResetSource

namespace OAI
/-! # Identify the old packed site-load histogram with the actual reset weight -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentSIMDLookup DescentColonies StarKeys DescentGL DescentPackedWalsh Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {k d i H R m : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (name : V↪Fin H) (group : J≃Fin R)

include S ready in
theorem reset_census (digits : Block m≃J×Block k) (v : V) (x : Block m) :
    A.censusValue name group false (name v) (group (digits x).1) (digits x).2 =
      A.resetLoad digits v x := by
  have live : ∃u,name u=name v:=⟨v,rfl⟩
  simp only [censusValue,dite_eq_left live,Bool.false_eq_true,ite_false,Equiv.symm_apply_apply,
    name.injective live.choose_spec]
  exact (filled_mass W.graph A.pos A.block digits
    (W.siteUnits (A.hub ∘ fun u => (A.pos u).2) A.records A.wire 256 A.hist) v x).symm.trans
    (W.mass_of_counts A.grainCount (A.z * G.b) (A.grainCount_fit S ready)
      (fun u => (A.pos u).2) (filled W.graph A.pos A.block digits)
      (A.hub ∘ fun u => (A.pos u).2) A.records A.wire 256 A.hist v x).symm

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
