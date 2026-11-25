import OAI.Hierarchy.DescentReachedAtomHalo
import OAI.Hierarchy.DescentHaloDonorChart
import OAI.Hierarchy.DescentIssuedHostRoster

namespace OAI
/-! # The previous scalar-book donor's sorted, physically mounted four-hop ordinal -/
namespace Hierarchy.DescentSortedHaloRaster
open DescentSixParty DescentStageEdgeReceipt DescentHostDegree DescentHostDirectory DescentCableDonorNames
open DescentPacking.PackedMatch.Local.Stage DescentOrdinaryDonorHalo DescentHaloWalkRAM DescentSortedRoster
open DescentPackedColony DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {V U : Type} [DecidableEq V] {H D G M w : ℕ}
variable (near : V→Finset V) (name : V↪Fin H) (R : Fin H→Fin D→Option (Fin H))
variable (exactRows : ∀v z,(∃i,R (name v) i=some z) ↔ ∃u∈near v,name u=z)

include exactRows in
private theorem follows (p : Path D) (v : V) (t : ℕ) (height : t≤4) {z : Fin H} (seen : walk R (name v) p t=some z) : ∃u∈around near t v,name u=z :=by
  induction t generalizing z with
  | zero=>exact ⟨v,by simp [around],Option.some.inj seen⟩
  | succ t ih=>
    have lt:t<4:=by omega
    simp only [walk,dite_eq_left lt,step] at seen
    split at seen
    · obtain ⟨prev,old,hit⟩:=Option.bind_eq_some_iff.mp seen
      obtain ⟨u,visited,rfl⟩:=ih (by omega) old
      obtain ⟨last,adj,eqn⟩:=(exactRows u z).1 ⟨_,hit⟩
      exact ⟨last,Finset.mem_biUnion.mpr ⟨u,visited,Finset.mem_insert_of_mem adj⟩,eqn⟩
    · obtain ⟨u,old,hit⟩:=ih (by omega) seen
      exact ⟨u,Finset.mem_biUnion.mpr ⟨u,old,Finset.mem_insert_self ..⟩,hit⟩

include exactRows in
theorem reached_set (v : V) : present (Gather.reaching R) (name v)=(around near 4 v).map name :=by
  ext z
  constructor
  · intro stored
    obtain ⟨p,hit⟩:=(Finset.mem_filter.mp stored).2
    exact Finset.mem_map.mpr (follows near name R exactRows (path p) v 4 le_rfl hit)
  · intro mem
    obtain ⟨u,old,rfl⟩:=Finset.mem_map.mp mem
    obtain ⟨p,hit⟩:=DescentHaloDonorChart.reached R near name (fun v u h=>(exactRows v _).2 ⟨u,h,rfl⟩) 4 le_rfl v u old
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,finFunctionFinEquiv p,by simpa [Gather.reaching,path] using hit⟩

variable (degree : ∀v,(near v).card≤D)
include exactRows in
theorem sorted_slot (v : V) (u : ↥(around near 4 v)) :
    indexed (Gather.reaching R) (name v) ((Halo.fromRank (around near 4) (name.trans Fin.valEmbedding) (around_room near D degree 4)).slot v u)=some (name u.val) :=by
  apply (indexed_iff ..).2
  refine ⟨by rw [reached_set near name R exactRows];exact Finset.mem_map.mpr ⟨u,u.property,rfl⟩,?_⟩
  change before _ _ _=(DescentSharedCableNames.Ends.neighborOrder (around near 4) (name.trans Fin.valEmbedding) (around_room near D degree 4) v u).val
  rw [before,reached_set near name R exactRows,nb_val,Finset.filter_map,Finset.card_map];rfl

theorem no_repeat (rs : Fin H→Fin D→Option (Fin H)) : Gather.select (indexed rs)=indexed rs :=by
  funext v j;unfold Gather.select
  split
  · rename_i earlier;obtain ⟨k,lt,eqn⟩:=earlier
    cases seen:indexed rs v j with
    | none=>rfl
    | some z=>obtain ⟨_,left⟩:=(indexed_iff rs v k z).1 (eqn.trans seen);obtain ⟨_,right⟩:=(indexed_iff rs v j z).1 seen;have:=Fin.ext (left.symm.trans right);exact (lt.ne this).elim
  · rfl

/-- All native packed joins can use their ordinary fixed-rank port operand
on this directory even though the original walk endpoints repeat. -/
theorem mounted (C : DescentSortedRoster.Chart) (P : Ports (breadth D)) (out : Bank) (m : Memory w)
    (fit : DescentSortedRoster.Room C (breadth D) H w out.base) (raw : Raw C (Gather.reaching R) m)
    (ports : Mounted P (Gather.reaching R) m G M) (ids : ∀j,(P.ids j).base+H*chunks G M≤out.base)
    (off : P.offsets.base+H≤out.base) (ch : P.chunks.base+H*chunks G M≤out.base) :
    let rs:=Gather.reaching R;let e:=DescentSortedRoster.code C (breadth D) H;let end_:=image out.base (H*breadth D) e m
    Mounted {P with roster:=out} (Gather.select (indexed rs)) end_ G M :=by
  dsimp only
  rw [no_repeat];exact DescentSortedRoster.ports C _ m P out fit raw ports ids off ch

/-- Taking a group is a product embedding of the very same set of old racks. -/
theorem grouped (near : V→Finset V) {J : Type} [DecidableEq J] (g : J) (v : V) (t : ℕ) :
    around (groupedNear near) t (g,v)=(around near t v).map (liftSite g) :=by
  induction t with
  | zero=>simp [around,liftSite];rfl
  | succ t ih=>
    ext z
    simp only [around,ih,Finset.mem_biUnion,Finset.mem_map,Finset.mem_insert,groupedNear]
    constructor
    · rintro ⟨_,⟨u,old,rfl⟩,eqn|⟨y,hop,eqn⟩⟩
      · exact ⟨u,⟨u,old,Or.inl rfl⟩,eqn.symm⟩
      · exact ⟨y,⟨u,old,Or.inr hop⟩,eqn⟩
    · rintro ⟨y,⟨u,old,eqn|hop⟩,rfl⟩
      · subst y
        exact ⟨liftSite g u,⟨u,old,rfl⟩,Or.inl rfl⟩
      · exact ⟨liftSite g u,⟨u,old,rfl⟩,Or.inr ⟨_,hop,rfl⟩⟩

/-- Combining the immutable group and the previous host in the input rank
preserves the sorted local halo at every actual donor. -/
theorem group_slot {J : Type} [DecidableEq J] (r : J×V↪ℕ) (order : ∀g v u,r (g,v)<r (g,u) ↔ name v<name u)
    (v : V) (g : J) (u : ↥(around near 4 v)) (dg : ∀x,((groupedNear near) x).card≤D) :
    (Halo.fromRank (around (groupedNear near) 4) r (around_room _ D dg 4)).slot (g,v)
      ⟨(g,u.val),by change (g,u.val) ∈ around (groupedNear near) 4 (g,v); rw [grouped];exact Finset.mem_map.mpr ⟨u,u.property,rfl⟩⟩ =
    (Halo.fromRank (around near 4) (name.trans Fin.valEmbedding) (around_room near D degree 4)).slot v u :=by
  apply Fin.ext
  let gu : ↥(around (groupedNear near) 4 (g,v)) :=
    ⟨(g,u.val), by rw [grouped]; exact Finset.mem_map.mpr ⟨u.val,u.property,rfl⟩⟩
  change (DescentSharedCableNames.Ends.neighborOrder (around (groupedNear near) 4) r
    (around_room _ D dg 4) (g,v) gu).val =
    (DescentSharedCableNames.Ends.neighborOrder (around near 4) (name.trans Fin.valEmbedding)
      (around_room near D degree 4) v u).val
  rw [nb_val,nb_val]
  change ((around (groupedNear near) 4 (g,v)).filter (fun x => r x < r (g,u.val))).card = _
  rw [grouped,Finset.filter_map,Finset.card_map]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨mem,lt⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨mem,(order g x u.val).mp lt⟩
  · intro hx
    obtain ⟨mem,lt⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨mem,(order g x u.val).mpr lt⟩

end
end Hierarchy.DescentSortedHaloRaster

end OAI
