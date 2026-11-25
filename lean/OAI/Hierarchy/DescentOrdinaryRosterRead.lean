import OAI.Hierarchy.DescentOrdinaryPeerReceipt
import OAI.Hierarchy.DescentGroupPeerOrder
import OAI.Hierarchy.DescentPackedFlowHeader
import OAI.Hierarchy.DescentPackedMatchTerrain

namespace OAI
/-! The sorted numerical adjacency column is exactly the physical host rotor
used by the next signed-board publisher. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentGroupPeerOrder DescentSharedCableNames DescentPacking.PackedMatch.Local.Stage
open scoped Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}

theorem genuine_hostRoster (A : GroupStage W G q ε J V k) (name : V↪ℕ) (v : V) (j : Fin A.degree) (R : ℕ) :
    ordinalPeer ((A.mutual v).map name) R j.val=(hostRoster A name v j).elim R name := by
  classical
  have sym : A.mutual v=A.near v:=Finset.ext (fun u=>by
    simp only [GroupStage.mutual,Finset.mem_filter]
    exact ⟨And.left,fun h=>⟨h,(A.symmetric v u).mp h⟩⟩)
  rw [sym]
  let pool:=(A.near v).map name
  change ordinalPeer pool R j.val = (hostRoster A name v j).elim R name
  by_cases active : j.val<pool.card
  · let ix:Fin pool.card:=⟨j.val,active⟩
    let z:pool:=pool.orderIsoOfFin rfl ix
    obtain ⟨x,hx,eqn⟩:=Finset.mem_map.mp z.property
    let u:↥(A.near v):=⟨x,hx⟩
    have arg : (⟨name x,Finset.mem_map.mpr ⟨x,hx,rfl⟩⟩:pool)=z:=Subtype.ext eqn
    have gets : hostSlot A name v u=j:=by
      apply Fin.ext
      change ((pool.orderIsoOfFin rfl).symm (⟨name x,_⟩:pool)).val=j.val
      rw [arg]
      exact congrArg Fin.val ((pool.orderIsoOfFin rfl).symm_apply_apply ix)
    have reported : hostRoster A name v j=some x:=gets ▸ at_host A name v u
    rw [ordinalPeer, dite_eq_left active, reported]
    change z.val = name x
    exact eqn.symm
  · have empty : hostRoster A name v j=none:=by
      unfold hostRoster
      split
      next hit =>
        obtain ⟨u,chosen⟩:=hit
        have inside : (hostSlot A name v u).val<pool.card:=
          ((pool.orderIsoOfFin rfl).symm ⟨name u.val,Finset.mem_map.mpr ⟨u.val,u.property,rfl⟩⟩).isLt
        exact False.elim (active (chosen ▸ inside))
      next =>rfl
    rw [ordinalPeer, dite_eq_right active, empty]
    rfl

theorem genuine_hostRotor {R : ℕ} (A : GroupStage W G q ε J V k) (names : V↪Fin R) (h : Fin R) (j : Fin A.degree) :
    (if yes : ∃v,(names v).val=h.val then ordinalPeer ((A.mutual yes.choose).map
      (names.trans Fin.valEmbedding)) R j.val else R)=
      (hostRotor names (hostRoster A (names.trans Fin.valEmbedding)) h j).elim R Fin.val := by
  classical
  by_cases live : ∃v,names v=h
  · obtain ⟨v,rfl⟩:=live
    have h₁ : ∃z,(names z).val=(names v).val:=⟨v,rfl⟩
    have h₂ : ∃z,names z=names v:=⟨v,rfl⟩
    rw [dite_eq_left h₁,hostRotor,dite_eq_left h₂,names.injective (Fin.ext h₁.choose_spec),names.injective h₂.choose_spec,
      genuine_hostRoster]
    cases hostRoster A (names.trans Fin.valEmbedding) v j <;> rfl
  · have absent : ¬∃v,(names v).val=h.val:=fun h'=>live (h'.imp (fun _ hh=>Fin.ext hh))
    simp [absent,hostRotor,live]

theorem original_hostRotor_rows {R : ℕ} (A : GroupStage W G q ε J V k) (names : V↪Fin R) (v : V) (z : Fin R) :
    (∃j,hostRotor names (hostRoster A (names.trans Fin.valEmbedding)) (names v) j=some z) ↔
      ∃u∈A.near v,names u=z := by
  have live : ∃x,names x=names v:=⟨v,rfl⟩
  simp only [hostRotor,dite_eq_left live,names.injective live.choose_spec]
  constructor
  · rintro ⟨j,hj⟩
    cases seen : hostRoster A (names.trans Fin.valEmbedding) v j with
    | none=>simp [seen] at hj
    | some y=>
      have where_ : names y=z:=by simpa [seen] using hj
      exact ⟨y,(hostRoster_mem A (names.trans Fin.valEmbedding) v y).2 ⟨j,seen⟩,where_⟩
  · rintro ⟨y,near,rfl⟩
    obtain ⟨j,hj⟩:=(hostRoster_mem A (names.trans Fin.valEmbedding) v y).1 near
    exact ⟨j,by simp [hj]⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI
