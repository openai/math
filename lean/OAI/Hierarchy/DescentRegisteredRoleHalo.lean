import OAI.Hierarchy.DescentOrdinaryCapturedRoleStock
import OAI.Hierarchy.DescentPhysicalRosterPrefix

namespace OAI
/-! The public ordinary register retains the old four-hop ordinal unchanged at every
old host, even if the physical scratch has more hosts or more shapes per next host. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentHaloWalkRAM DescentScalarVenueMask DescentSortedRoster DescentPacking.PackedMatch.Local.Stage
noncomputable section

theorem registered_role_halo {H H' R D E : ℕ} (wide : H≤R) (hosts : R=H') (degree : E=D)
    (small : Fin H→Fin D→Option (Fin H)) (large : Fin H'→Fin E→Option (Fin H'))
    (rows : ∀(h : Fin H) (j : Fin D),large ((h.castLE wide).cast hosts) (j.cast degree.symm)=
      (small h j).map (fun t=>(t.castLE wide).cast hosts))
    (h : Fin H) (p : Fin (breadth D)) :
    primitiveRoster hosts (congrArg breadth degree.symm) (indexed (Gather.reaching large)) (h.castLE wide) p=
      (indexed (Gather.reaching small) h p).map (Fin.castLE wide):=by
  subst H'
  subst E
  have reached:=reaching_pad wide small large (fun h j=>by simpa using rows h j) h
  simpa [primitiveRoster] using indexed_pad wide (Gather.reaching small) (Gather.reaching large) h reached p

/-- The same comparison for the real returned old-host rotor from the previous dated directory. -/
theorem registered_role_rotor {V : Type} [Fintype V] {H H' D : ℕ} (wide : H≤H') (host : V↪Fin H)
    (near : V→Fin D→Option V) (h : Fin H) (p : Fin (breadth D)) :
    primitiveRoster rfl rfl (indexed (Gather.reaching (hostRotor (host.trans (Fin.castLEEmb wide)) near))) (h.castLE wide) p=
      (indexed (Gather.reaching (hostRotor host near)) h p).map (Fin.castLE wide) :=
  registered_role_halo wide rfl rfl (hostRotor host near) _ (physical_rotor wide host near) h p

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
