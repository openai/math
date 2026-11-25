import OAI.Hierarchy.DescentResetJoinedRank
import OAI.Hierarchy.DescentSortedRoster

namespace OAI
/-! # Attained original host codes select their ordinal in the true successor's four slots -/
namespace Hierarchy.DescentResetJoinedRank
open DescentSortedRoster DescentFallbackLeafScan DescentSIMDLookup
open scoped Classical
noncomputable section
variable {H b : ℕ} (rows : Fin H→Fin 4→Option (Fin H))

theorem before_lt (v z : Fin H) (member : z∈present rows v) : before rows v z<4:=by
  obtain ⟨key,hit⟩:=first_one rows v z (Finset.mem_filter.mp member).2
  let predecessors:=Finset.univ.filter fun i:Fin 4=>keep rows v z i=true
  have missing : key∉predecessors:=by
    intro contained
    have rejected:=(Finset.mem_filter.mp contained).2
    change (first rows v key).any (fun x=>decide (x<z))=true at rejected
    simp [hit] at rejected
  have sub : predecessors⊂Finset.univ :=
    (Finset.ssubset_iff_of_subset (Finset.subset_univ predecessors)).2 ⟨key,Finset.mem_univ _,missing⟩
  rw [←order_count]
  simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_lt_card sub

theorem rank_read (v z : Fin H) (x : Fin 5→Cell b) (room : 4≤2^b) (presentZ : z∈present rows v)
    (positive : x 4≠0) (capture : ∀j : Fin 4,x j.castSucc=x 4 ↔ indexed rows v j=some z) :
    (rank x).val=before rows v z:=by
  let j : Fin 4:=⟨before rows v z,before_lt rows v z presentZ⟩
  apply rank_at x j room positive
  intro i
  rw [capture,indexed_iff]
  constructor
  · rintro ⟨_,eqn⟩
    exact Fin.ext eqn.symm
  · rintro rfl
    exact ⟨presentZ,rfl⟩

end
end Hierarchy.DescentResetJoinedRank

end OAI
