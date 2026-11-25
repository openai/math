import OAI.Hierarchy.DescentDatedSortedPathSocket
import OAI.Hierarchy.DescentPhysicalRosterPrefix

namespace OAI
/-! # Both physical donor coordinates survive padding the old host rack -/
namespace Hierarchy.DescentDatedSourcePathDirectory.Sorted
open DescentHaloWalkRAM DescentSortedRoster DescentScalarVenueMask DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {H H' P D : ℕ} (wide : H≤H')
local notation "up" => Fin.castLEEmb wide

theorem selected_pad (small : Fin H→Fin P→Option (Fin H)) (large : Fin H'→Fin P→Option (Fin H'))
    (v : Fin H) (same : ∀j,large (up v) j=(small v j).map up) (p : Fin P) :
    Gather.select large (up v) p=(Gather.select small v p).map up :=by
  have repeat_ : (∃q : Fin P,q<p ∧ large (up v) q=large (up v) p) ↔ ∃q : Fin P,q<p ∧ small v q=small v p :=by
    simp only [same,(Option.map_injective (up).injective).eq_iff]
  by_cases repeated : ∃q : Fin P,q<p ∧ small v q=small v p
  · simp only [Gather.select,ite_eq_left repeated,ite_eq_left (repeat_.2 repeated),Option.map_none]
  · unfold Gather.select
    rw [ite_eq_right (mt repeat_.1 repeated), ite_eq_right repeated, same]

/-- The W's sorted index and its unique first visit identify exactly the
same old host in the physical matcher rectangle, including repeated paths. -/
theorem host_coordinates {V : Type} [Fintype V] (host : V↪Fin H) (near : V→Fin D→Option V)
    (v u : Fin H) (s p : Fin (breadth D))
    (stored : indexed (Gather.reaching (hostRotor host near)) v s=some u)
    (raw : Gather.select (Gather.reaching (hostRotor host near)) v p=some u) :
    let reach:=Gather.reaching (hostRotor (host.trans up) near)
    indexed reach (up v) s=some (up u) ∧ Gather.select reach (up v) p=some (up u) ∧
      rawAtOrdinal reach (up v) s=p.val :=by
  intro reach
  let before:=Gather.reaching (hostRotor host near)
  have agree:=reaching_pad wide _ _ (physical_rotor wide host near) v
  change indexed before v s = some u at stored
  change Gather.select before v p = some u at raw
  have atSort : indexed reach (up v) s=some (up u):=by
    simpa only [stored,Option.map_some] using indexed_pad wide before reach v agree s
  have atRaw : Gather.select reach (up v) p=some (up u):=by
    simpa only [raw,Option.map_some] using selected_pad wide before reach v agree p
  exact ⟨atSort,atRaw,raw_eq reach (up v) (up u) s p atSort atRaw⟩

end
end Hierarchy.DescentDatedSourcePathDirectory.Sorted

end OAI
