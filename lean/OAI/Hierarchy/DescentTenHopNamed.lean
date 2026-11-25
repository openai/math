import OAI.Hierarchy.DescentTenHopRoster
import OAI.Hierarchy.DescentOldHostBall

namespace OAI
/-! # Identification of the reached physical roster with the named old ten-hop venue set -/
namespace Hierarchy.DescentTenHopRoster
open DescentOrdinaryDonorHalo DescentSortedRoster
noncomputable section
variable {V : Type} [DecidableEq V] {H D : ℕ} (peer : Fin H→Fin D→Option (Fin H))

theorem last_hop {n : ℕ} {v z : Fin H} (path : Walk peer (n+1) v z) :
    ∃u,Walk peer n v u ∧ ∃i,peer u i=some z := by
  induction n generalizing v z with
  | zero=>
    cases path with
    | cons edge rest=>cases rest;exact ⟨_,.nil _,edge⟩
  | succ n ih=>
    cases path with
    | cons edge rest=>
      obtain ⟨u,earlier,last⟩:=ih rest
      exact ⟨u,.cons edge earlier,last⟩

variable (name : V↪Fin H) (near : V→Finset V)
variable (rows : ∀v z,(∃j,peer (name v) j=some z)↔∃u∈near v,name u=z)

include rows in
theorem named_ball (n : ℕ) (v : V) (z : Fin H) :
    (∃s≤n,Walk peer s (name v) z) ↔ ∃u∈around near n v,name u=z := by
  classical
  induction n generalizing z with
  | zero=>
    constructor
    · rintro ⟨s,hs,p⟩
      obtain rfl : s=0:=by omega
      cases p
      exact ⟨v,Finset.mem_singleton_self _,rfl⟩
    · rintro ⟨u,mem,rfl⟩
      obtain rfl : u=v:=Finset.mem_singleton.mp mem
      exact ⟨0,le_rfl,.nil _⟩
  | succ n ih=>
    constructor
    · rintro ⟨s,hs,p⟩
      by_cases earlier : s≤n
      · obtain ⟨u,mem,eqn⟩:=(ih z).mp ⟨s,earlier,p⟩
        exact ⟨u,Finset.mem_biUnion.mpr ⟨u,mem,Finset.mem_insert_self ..⟩,eqn⟩
      · obtain rfl : s=n+1:=by omega
        obtain ⟨x,first,last⟩:=last_hop peer p
        obtain ⟨old,member,rfl⟩:=(ih x).mp ⟨n,le_rfl,first⟩
        obtain ⟨fresh,found,eqn⟩:=(rows old z).mp last
        exact ⟨fresh,Finset.mem_biUnion.mpr ⟨old,member,Finset.mem_insert_of_mem found⟩,eqn⟩
    · rintro ⟨u,mem,rfl⟩
      obtain ⟨old,member,step⟩:=Finset.mem_biUnion.mp mem
      obtain ⟨s,le,path⟩:=(ih (name old)).mpr ⟨old,member,rfl⟩
      rcases Finset.mem_insert.mp step with rfl|edge
      · exact ⟨s,le.trans (Nat.le_succ _),path⟩
      · exact ⟨s+1,Nat.succ_le_succ le,snoc peer path ((rows old (name u)).mpr ⟨u,edge,rfl⟩)⟩

include rows in
theorem oldSet_named (v : V) : oldSet peer (name v)=(around near 10 v).map name := by
  ext z
  exact (present_iff peer (name v) z).trans ((named_ball peer name near rows 10 v z).trans Finset.mem_map.symm)

end
end Hierarchy.DescentTenHopRoster

end OAI
