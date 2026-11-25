import OAI.Hierarchy.DescentDatedVenueSources
import OAI.Hierarchy.DescentSharedCableCensus
import OAI.Hierarchy.DescentPackedMatchPrepareIssued
import OAI.Hierarchy.DescentPackedStageCensus

namespace OAI
/-! # The chooser census assembled from the actual previous signed records -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census
open DescentSixParty DescentSIMDLookup DescentPackedColony DescentStageEdgeReceipt
open scoped Classical Fin.CommRing
noncomputable section

/-- The previous host's public hub flag is repeated at every dyadic block. The
two signed bits are read directly from the existing physical cable codec. -/
def assemble (D cap b r : ℕ) (hub : Cell 1) (counts : Fin r→Cell b)
    (cables : Fin r→Fin (2*cap)→Cell (DescentSignedCableCodec.width D cap)) : Cell ((1+b+2*(2*cap))*r) :=
  encode (1+b+2*(2*cap)) r (fun x=>PackedCensus.header b (2*cap)
    ((hub,counts x),fun j=>DescentSignedCableCodec.census (cables x j)))

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k age G H : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S age) (groups : J≃Fin G) (hosts : V↪Fin H)

omit [DecidableEq J] [DecidableEq V] in
theorem spread_index {X : Type*} (zero : X) (f : J×V→X) (h : Fin H) (g : Fin G) :
    Prepare.spreadField groups.toEmbedding hosts zero f h g =
      if v : ∃u,hosts u=h then f (groups.symm g,v.choose) else zero := by
  by_cases real : ∃u,hosts u=h
  · have existsPair : ∃z : J×V,groups.toEmbedding z.1=g ∧ hosts z.2=h :=
      ⟨(groups.symm g,real.choose),groups.apply_symm_apply _,real.choose_spec⟩
    have equal : existsPair.choose=(groups.symm g,real.choose) :=
      Prod.ext (groups.injective (existsPair.choose_spec.1.trans (groups.apply_symm_apply g).symm))
        (hosts.injective (existsPair.choose_spec.2.trans real.choose_spec.symm))
    simp only [Prepare.spreadField,dite_eq_left existsPair,dite_eq_left real,equal]
  · have noPair : ¬∃z : J×V,groups.toEmbedding z.1=g ∧ hosts z.2=h :=
      fun ⟨z,_,hit⟩=>real ⟨z.2,hit⟩
    simp only [Prepare.spreadField,dite_eq_right noPair,dite_eq_right real]

/-- This equality also holds at a padded host and at a real, isolated actor
where both signed-port families are empty. It uses the actual old slot order. -/
theorem raw_eq (b : ℕ) (h : Fin H) (g : Fin G) :
    assemble A.degree A.cap b (2^k) (hub A hosts h) (count A groups hosts b h g)
      (fun x j=>DescentSignedCableCodec.encode (Prepare.signed A native S ready groups.toEmbedding hosts x j h g)) =
    A.rawCensus hosts groups (DescentSharedCableNames.Stage.signed A native S ready) b h g := by
  classical
  by_cases real : ∃u,hosts u=h
  · simp only [assemble,hub,count,GroupStage.rawCensus,PackedCensus.source,
      Prepare.signed,spread_index groups hosts,dite_eq_left real,DescentSignedCableCodec.census_at,
      DescentSharedCableNames.Stage.census_tags]
    apply congrArg (encode (1+b+2*(2*A.cap)) (2^k))
    funext x
    rfl
  · simp only [assemble,hub,count,GroupStage.rawCensus,Prepare.signed,spread_index groups hosts,
      dite_eq_right real,DescentSignedCableCodec.census_at,DescentSharedCableNames.Stage.censusTag]; rfl

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census

end OAI
