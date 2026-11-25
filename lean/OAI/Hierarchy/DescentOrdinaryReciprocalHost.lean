import OAI.Hierarchy.DescentGroupPeerOrder

namespace OAI
/-! The preceding published host directory is reciprocal on its entire padded address space. -/
namespace Hierarchy.DescentGroupPeerOrder
open DescentSixParty DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt
open scoped Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k H : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {q ε:ℝ}
variable (A:GroupStage W G q ε J V k) (name:V↪Fin H) (rank:V↪ℕ)
local notation "near" => hostRoster A rank
local notation "R" => hostRotor name near

theorem extended_at (v:V) (j:Fin A.degree) : R (name v) j=(near v j).map name :=by
  have found:∃u,name u=name v:=⟨_,rfl⟩
  simp only [hostRotor,dite_eq_left found,name.injective found.choose_spec]

theorem extended_reciprocal (a b:Fin H) (j:Fin A.degree) (hit:R a j=some b) : ∃l,R b l=some a:=by
  unfold hostRotor at hit
  split at hit
  next has=>
    let v:=has.choose
    have srcEq:name v=a:=has.choose_spec
    cases old:near v j with
    | none=>change (near v j).map name=some b at hit;rw [old] at hit;contradiction
    | some t=>
      change (near v j).map name=some b at hit
      have dest:name t=b:=Option.some.inj (by simpa only [old,Option.map_some] using hit)
      have seen:=(hostRoster_mem A rank v t).2 ⟨j,old⟩
      obtain ⟨l,back⟩:=(hostRoster_mem A rank t v).1 ((A.symmetric v t).1 seen)
      exact ⟨l,by rw [←dest,extended_at,back,Option.map_some,srcEq]⟩
  next=>contradiction

theorem extended_group (groups:J↪ℕ) (u:J×V) (j:Fin A.degree) :
    R (name u.2) j=(rotor A (groupRank groups rank) u j).map (fun t=>name t.2):=by
  rcases u with ⟨g,v⟩
  rw [extended_at,rotor_group A groups rank]
  cases near v j <;>rfl

end
end Hierarchy.DescentGroupPeerOrder

end OAI
