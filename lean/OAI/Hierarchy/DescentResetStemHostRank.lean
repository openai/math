import OAI.Hierarchy.DescentResetStemIssuedGroups
import OAI.Hierarchy.DescentResetStemHalo
import OAI.Hierarchy.DescentFallbackSignedPeer

namespace OAI
/-! # Reading the original source class on either side of a signed stem -/
namespace Hierarchy.DescentResetStemCompactOrder
open scoped Classical
noncomputable section

def closeRank (missing : Bool) (self peer : ℕ) : ℕ :=
  peer + if missing=true ∧ self≤peer then 1 else 0

private theorem growing {d : Finset ℕ} {v t : ℕ} (mem : t∈d) (less : t<v) : compress d t<compress d v := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (show d.filter (·<t)⊆d.filter (·<v) from fun a ha=>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp ha).2.trans less⟩)).2
  exact ⟨t,Finset.mem_filter.mpr ⟨mem,less⟩,by simp⟩

theorem closeRank_correct (d : Finset ℕ) (v t : ℕ) (mem : t∈d) :
    closeRank (decide (v∉d)) (compress (insert v d) v) (compress d t)=compress (insert v d) t := by
  by_cases hit:v∈d
  · simp [closeRank,hit,Finset.insert_eq_of_mem hit]
  have diff:v≠t:=fun eqn=>hit (eqn ▸ mem)
  by_cases ab:v<t
  · have monotone:compress d v≤compress d t:=Finset.card_le_card
      (fun a ae=>Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ae).1,(Finset.mem_filter.mp ae).2.trans ab⟩)
    simp [closeRank,hit,compress,Finset.filter_insert,ab]
    exact monotone
  · have more:=growing mem (lt_of_le_of_ne (Nat.le_of_not_gt ab) (Ne.symm diff))
    simp [closeRank,hit,compress,Finset.filter_insert,ab]
    exact more

open DescentSixParty DescentSharedCableNames DescentIssuedFallbackPanel DescentGroupPeerOrder
open DescentCompiler DescentColonies DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i h : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : AtomSchedule) (ready : A.StateBounds S i)
    (grp : J↪ℕ) (vertex : V↪Fin (Fintype.card V))
local notation "ids" => vertex.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank grp ids)
set_option quotPrecheck false in
local notation "oldsrc" => fun (e : Stage.Grain A) => (A.pos (W.graph.src (e : Stage.Grain A).1)).2
set_option quotPrecheck false in
local notation "here" => fun (s : Bool) (e : Stage.Grain A) => (A.pos (endSite A s e)).2
set_option quotPrecheck false in
local notation "sd" => fun (s : Bool) (e : Stage.Grain A) => Stage.live A native S ready names (port A s e).1 (port A s e).2

theorem peer_host (e : Stage.Grain A) :
    hostRoster A ids (here true e) (sd true e).neighbor=some (oldsrc e) := by
  let p:=port A true e
  have peer:=signedPeer_actual A native S ready names true e
  simp only [signedPeer,Stage.signed_read] at peer
  change (if (sd true e).target=true then physicalPeer A names p.1 (sd true e).neighbor else none)=_ at peer
  simp only [show (sd true e).target=true from rfl,ite_true] at peer
  rw [physicalPeer_group A grp ids] at peer
  apply_fun Option.map (fun item : Stage.Host J V k=>item.1.2) at peer
  simpa [p,Function.comp_def,port_fst,Stage.home,endSite] using peer

private theorem image_compress (v u : V) :
    compress ((A.near v).image (fun t=>(vertex t).val)) (vertex u).val=
      ((A.near v).filter (fun t=>ids t < ids u)).card := by
  let emb:=vertex.trans Fin.valEmbedding
  change (((A.near v).image emb).filter (fun x=>x<emb u)).card=_
  rw [←Finset.map_eq_image,Finset.filter_map,Finset.card_map];rfl

theorem source_halo (s : Bool) (e : Stage.Grain A) :
    (if s then closeRank (decide (here s e∉A.near (here s e)))
      (compress (hostDomain A vertex (here s e)) (vertex (here s e)).val) (sd s e).neighbor.val
      else compress (hostDomain A vertex (here s e)) (vertex (here s e)).val)=
      compress (hostDomain A vertex (here s e)) (vertex (oldsrc e)).val := by
  cases s with
  | false=>rfl
  | true=>
    let v:=here true e
    let u:=oldsrc e
    let near:=(A.near v).image (fun t=>(vertex t).val)
    have observed:hostRoster A ids v (sd true e).neighbor=some u:=peer_host A native S ready grp vertex e
    have member:u∈A.near v:=(hostRoster_mem A ids v u).2 ⟨_,observed⟩
    have num:(sd true e).neighbor=hostSlot A ids v ⟨u,member⟩:=by
      unfold hostRoster at observed
      split at observed
      next yes=>
        have equal : (Classical.choose yes : ↥(A.near v)).val=u:=Option.some.inj observed
        exact yes.choose_spec.symm.trans (congrArg (hostSlot A ids v) (Subtype.ext equal))
      next no=>contradiction
    have closed:hostDomain A vertex v=insert (vertex v).val near:=by simp [hostDomain,near]
    have miss:(vertex v).val∈near ↔ v∈A.near v:=by
      constructor
      · rintro p;obtain ⟨u,hu,same⟩:=Finset.mem_image.mp p
        exact (vertex.injective (Fin.ext same)) ▸ hu
      · exact fun p=>Finset.mem_image_of_mem _ p
    change closeRank (decide (v∉A.near v)) (compress (hostDomain A vertex v) (vertex v).val)
      (sd true e).neighbor.val=compress (hostDomain A vertex v) (vertex u).val
    rw [num,hostSlot_val,←image_compress A vertex,closed]
    have sameMiss : decide (v∉A.near v) = decide ((vertex v).val∉near) := by
      by_cases used : v∈A.near v
      · simp [used,miss.mpr used]
      · have missing := mt miss.mp used
        simp [used,missing]
    rw [sameMiss]
    exact closeRank_correct near (vertex v).val (vertex u).val (Finset.mem_image_of_mem _ member)
end
end Hierarchy.DescentResetStemCompactOrder

end OAI
