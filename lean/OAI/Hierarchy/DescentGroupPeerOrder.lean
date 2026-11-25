import OAI.Hierarchy.DescentHostRosterOrder
import OAI.Hierarchy.DescentPackedMatchRoster
import OAI.Hierarchy.DescentFallbackSignedPeer

namespace OAI
/-! # The same old neighbor ordinal in every external group and local block -/

namespace Hierarchy.DescentGroupPeerOrder
open DescentSharedCableNames DescentSixParty DescentStageEdgeReceipt DescentHostDirectory
open DescentPacking.PackedMatch.Local.Stage DescentIssuedFallbackPanel
open scoped Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
variable (A : GroupStage W G q ε J V k) (groupKey : J↪ℕ) (vertex : V↪ℕ)
local notation "rank" => groupRank groupKey vertex

theorem groupSlot (j : J) (v : V) (w : ↥(A.near v)) :
    ordinal A rank (j,v) ⟨(j,w.val),Finset.mem_map.mpr ⟨w.val,w.property,rfl⟩⟩=hostSlot A vertex v w := by
  apply Fin.ext
  rw [ordinal,nb_val,hostSlot_val]
  let embed:=liftSite (V:=V) j
  have both : ((neighbors A (j,v)).filter (fun u=>rank u<rank (j,w.val)))=
      (((A.near v).filter (fun u=>vertex u<vertex w.val)).map embed) := by
    ext z
    simp only [neighbors,groupedNear,Finset.mem_filter,Finset.mem_map]
    constructor
    · rintro ⟨⟨z,mz,rfl⟩,lt⟩
      exact ⟨z,⟨mz,Nat.lt_of_add_lt_add_left
        (show groupKey j*pitch vertex+vertex z<groupKey j*pitch vertex+vertex w.val from lt)⟩,rfl⟩
    · rintro ⟨z,⟨mz,lt⟩,rfl⟩
      exact ⟨⟨z,mz,rfl⟩,Nat.add_lt_add_left lt _⟩
  rw [both,Finset.card_map]

theorem rotor_group (j : J) (v : V) (s : Fin A.degree) :
    rotor A rank (j,v) s=(hostRoster A vertex v s).map (fun w=>(j,w)) := by
  by_cases active : ∃w,hostSlot A vertex v w=s
  · obtain ⟨w,rfl⟩:=active
    rw [at_host,Option.map_some]
    rw [←groupSlot A groupKey vertex j v w,rotor_at]
  · have idle : ¬∃u,ordinal A rank (j,v) u=s := by
      rintro ⟨⟨a,mem⟩,eqn⟩
      obtain ⟨y,hy,ey⟩:=Finset.mem_map.mp mem
      subst a
      exact active ⟨⟨y,hy⟩,(groupSlot A groupKey vertex j v ⟨y,hy⟩).symm.trans eqn⟩
    simp [rotor,hostRoster,active,idle]

theorem physicalPeer_group (j : J) (v : V) (x : Fin (2^k)) (s : Fin A.degree) :
    physicalPeer A (cableNames k rank) ((j,v),x) s=(hostRoster A vertex v s).map (fun w=>((j,w),x)) := by
  let rankLocal:=Ends.neighborOrder (Stage.near A) (cableNames k rank) (Stage.near_room A) ((j,v),x)
  have atSlot (z : ↥(A.near v)) :
      rankLocal ⟨((j,z.val),x),Finset.mem_map.mpr ⟨(j,z.val),Finset.mem_map.mpr ⟨z.val,z.property,rfl⟩,rfl⟩⟩=
        hostSlot A vertex v z :=
    (paired A rank (j,v) x ⟨(j,z.val),Finset.mem_map.mpr ⟨z.val,z.property,rfl⟩⟩).trans
      (groupSlot A groupKey vertex j v z)
  by_cases live : ∃z,hostSlot A vertex v z=s
  · obtain ⟨z,rfl⟩:=live
    rw [at_host,Option.map_some]
    let a : ↥(Stage.near A ((j,v),x)):=⟨((j,z.val),x),
      Finset.mem_map.mpr ⟨(j,z.val),Finset.mem_map.mpr ⟨z.val,z.property,rfl⟩,rfl⟩⟩
    have find : ∃p,rankLocal p=hostSlot A vertex v z:=⟨a,atSlot z⟩
    unfold physicalPeer
    rw [dite_eq_left find,rankLocal.injective (find.choose_spec.trans (atSlot z).symm)]
  · have none : ¬∃p,rankLocal p=s := by
      rintro ⟨⟨p,mem⟩,eqn⟩
      obtain ⟨b,mb,rfl⟩:=Finset.mem_map.mp mem
      obtain ⟨u,mu,rfl⟩:=Finset.mem_map.mp mb
      exact live ⟨⟨u,mu⟩,(atSlot ⟨u,mu⟩).symm.trans eqn⟩
    simp [physicalPeer,hostRoster,none,live,rankLocal]

end
end Hierarchy.DescentGroupPeerOrder

end OAI
