import OAI.Hierarchy.DescentOrdinaryCompactPeer
import OAI.Hierarchy.DescentOrdinaryMeasuredPeer
import OAI.Hierarchy.DescentPackedChildNeighborIssued

namespace OAI
/-! # Read the real sorted successor slot at its compact physical host ordinal -/
namespace Hierarchy.DescentOrdinaryCompactPeer
open DescentSixParty DescentGroupPeerOrder DescentStageEdgeReceipt DescentHostDirectory DescentSharedCableNames
open DescentPacking.PackedMatch.Local.Stage DescentIssuedFallbackPanel DescentHaloWalkRAM DescentParallelBase.ParentFilter
open DescentPackedChildNeighbor
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM
open DescentColonies
open scoped Classical Fin.CommRing
noncomputable section
variable {N H L Q D w : ℕ}

theorem value_at (ends : Fin N→Fin L→Option (Fin N)) (roster : Fin H→Fin D→Option (Fin H))
    (pitch : ℕ) (v other : Fin N) (h dest : Fin H) (q : Fin L) (low : Fin Q) (j : Fin D)
    (endpoint : ends v q=some other) (address : dest.val=other.val*pitch+low.val)
    (found : roster h j=some dest) (unique : ∀t,roster h t=some dest→t=j) :
    value ends roster pitch v h ⟨rank ends v q,Ranks.bound ..⟩ low=j.val := by
  simp only [value,previous_at,endpoint,number,Option.elim_some,ite_eq_right other.isLt.ne]
  apply search_live _ _ _ _ _ _ ⟨j,List.mem_finRange _,by simpa [found,number] using address⟩
  intro t _ hit
  apply congrArg Fin.val (unique t ?_)
  cases hy:roster h t with
  | none=>
    simp only [hy,Option.elim_none,←address] at hit
    exact False.elim (dest.isLt.ne hit.symm)
  | some a=>
    simp only [hy,Option.elim_some,←address] at hit
    exact congrArg some (Fin.ext hit)

section StageRank
variable {F J V U : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i E : ℕ} {bits : U→ℕ} {W : MarkedWorld F d U bits} {powg : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W powg price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (group : J↪ℕ) (name : V↪Fin H)
local notation "vertex" => name.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank group vertex)
local notation "neighbors" => hostRotor name (hostRoster A vertex)

private theorem at_sorted (v : V) (j : Fin A.degree) : neighbors (name v) j=(hostRoster A vertex v j).map name := by
  have yes : ∃u,name u=name v:=⟨v,rfl⟩
  rw [hostRotor,dite_eq_left yes,name.injective yes.choose_spec]

private theorem unique_name {v u : V} {a b : Fin A.degree} (left : hostRoster A vertex v a=some u) (right : hostRoster A vertex v b=some u) : a=b := by
  unfold hostRoster at left right
  split at left
  · rename_i first
    split at right
    · rename_i second
      have same : first.choose=second.choose:=Subtype.ext ((Option.some.inj left).trans (Option.some.inj right).symm)
      exact (first.choose_spec.symm.trans (congrArg (hostSlot A vertex v) same)).trans second.choose_spec
    · contradiction
  · contradiction


theorem live_rank (adj : Fin N→Fin E→Option (Fin N)) (pitch : ℕ) (v donor other : Fin N)
    (path : Fin (breadth E)) (dest : Endpoint (breadth E) Q)
    (there : Gather.reaching adj v path=some donor) (across : Gather.reaching adj donor dest.path=some other)
    (j : J) (a : V) (x : Block k) (port : A.CellPorts j a x)
    (endpoint : (name (((Stage.source A native).peer ((j,a),x) (Stage.ofPort A native ((j,a),x) port).val).1.2)).val=
      other.val*pitch+dest.low.val) :
    value (PairRanks.combined (Gather.reaching adj)) neighbors pitch v (name a)
      (finProdFinEquiv.symm (peer adj v path dest)).1 (finProdFinEquiv.symm (peer adj v path dest)).2=
      (Stage.live A native S ready names ((j,a),x) port).neighbor.val := by
  let h:=((j,a),x);let z:=(Stage.source A native).peer h (Stage.ofPort A native h port).val
  let slot:=(Stage.live A native S ready names h port).neighbor
  have key : (hostRoster A vertex a slot).map (fun u=>((j,u),x))=some z:=
    (physicalPeer_group A group vertex j a x slot).symm.trans (physicalPeer_read A native S ready names h port)
  have localHit : hostRoster A vertex a slot=some z.1.2 := by
    obtain ⟨u,hit,which⟩:=Option.map_eq_some_iff.mp key
    exact hit.trans (congrArg (fun t=>some t.1.2) which)
  simp only [peer,Equiv.symm_apply_apply]
  apply value_at _ _ _ v other _ (name z.1.2) (PairRanks.pair path dest.path) _ slot
    (by simp [there,across]) endpoint
  · rw [at_sorted,localHit,Option.map_some]
  · intro t hit
    rw [at_sorted] at hit
    obtain ⟨u,seen,equal⟩:=Option.map_eq_some_iff.mp hit
    exact unique_name A name (seen.trans (congrArg some (name.injective equal))) localHit

end StageRank

open DescentSIMDLookup DescentPackedZip DescentOrdinarySignedMeta DescentParallelBase

theorem value_bound (ends : Fin N→Fin L→Option (Fin N)) (roster : Fin H→Fin D→Option (Fin H))
    (pitch : ℕ) (old : Fin N) (h : Fin H) (ticket : Fin L) (low : Fin Q) :
    value ends roster pitch old h ticket low≤D := by
  have search_bound (f : Fin D→ℕ) (x : ℕ) (js : List (Fin D)) : search f Fin.val x D js≤D := by
    induction js with
    | nil => rfl
    | cons j js ih => simp only [search]; split; exact j.isLt.le; exact ih
  dsimp only [value]
  split
  · exact le_rfl
  · exact search_bound ..

def directory {b : ℕ} (ends : Fin N→Fin L→Option (Fin N)) (roster : Fin H→Fin D→Option (Fin H))
    (pitch : ℕ) (rack : Fin H→Option (Fin N)) (wide : D<2^b) (h : Fin H) (j : Fin (L*Q)) : Cell b :=
  ⟨(rack h).elim D (fun v=>value ends roster pitch v h (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2),by
    cases hit:rack h with
    | none=>exact wide
    | some u=>exact (value_bound ..).trans_lt wide⟩

theorem header_words {b : ℕ} (ends : Fin N→Fin L→Option (Fin N)) (roster : Fin H→Fin D→Option (Fin H))
    (pitch : ℕ) (rack : Fin H→Option (Fin N)) (wide : D<2^b) (m : Memory w) (out : ℕ)
    (read : ∀z : Key H L Q,m (out+(index H L Q z).val)=
      (((rack z.1).elim D (fun v=>value ends roster pitch v z.1 z.2.1 z.2.2):ℕ):Word w)) (h : Fin H) (j : Fin (L*Q)) :
    m (out+(h.val*(L*Q)+j.val))=((directory ends roster pitch rack wide h j).val:Word w) := by
  have seen:=read (h,finProdFinEquiv.symm j)
  simpa only [index,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,Equiv.apply_symm_apply,
    finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm,directory] using seen

section Measured
variable {F Pin J V E X T V₀ : Type} [Field F] [Fintype J] [DecidableEq J]
  [Fintype V] [DecidableEq V] [Fintype E] [Fintype X] [Fintype T] {d k i b O K cap : ℕ}
  {bits : Pin→ℕ} {W : MarkedWorld F d Pin bits} {G : PoweredGadget F} {p ε : ℝ}
  (A : GroupStage W G p ε J V k) (native : W.graph.Edge↪ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
  (group : J↪ℕ) (name : V↪Fin H) (C : Blocks (Stage.source A native) E)
  (R : Fin N→Fin D→Option (Fin N)) (symm : ∀v u j,R v j=some u→∃l,R u l=some v)
  (Z : Measured C R X T V₀ Q O K cap)
local notation "res" => Measured.roster C R symm Z
local notation "old" => PairRanks.combined (Gather.reaching R)
local notation "next" => hostRotor name (hostRoster A (name.trans Fin.valEmbedding))
local notation "cnames" => cableNames k (groupRank group (name.trans Fin.valEmbedding))
variable (pitch : ℕ) (rack : Fin H→Option (Fin N)) (wide : A.degree<2^b)
  (coord : ∀h : Stage.Host J V k,(name h.1.2).val=(Z.venue h).1.val*pitch+(Z.venue h).2.val)
  (found : ∀h : Stage.Host J V k,rack (name h.1.2)=some (Z.venue h).1)

include coord found in
theorem measured_rank (h : Stage.Host J V k) (x : Local C h) :
    (directory old next pitch rack wide (name h.1.2) ((res).entry h x).peer).val=
      (DescentResetWindowFields.neighbor A native S ready cnames C h (residentFace A native C h x)).val := by
  let f:=residentFace A native C h x
  let u:=DescentResetWindowFields.firstUnit A native C h f
  let port:=GrainPorts.port A native C h u
  have edge : u.val.1.1=x.val := residentFace_edge A native C h x
  have here : (Stage.source A native).peer h (Stage.ofPort A native h port).val=other C h x := by
    dsimp only [port]
    rw [Ends.peer,issued_port_order A native C h u,C.atSource,C.atTarget,edge]
    rfl
  have reach:=Z.otherFields h x
  have last : (name (((Stage.source A native).peer h (Stage.ofPort A native h port).val).1.2)).val=
      (Z.venue (other C h x)).1.val*pitch+(Z.otherEnd h x).low.val := by rw [here,coord,reach.2]
  have trueRank := live_rank A native S ready group name R pitch (Z.venue h).1 (Z.old h x)
    (Z.venue (other C h x)).1 (Measured.visit C R symm Z h x) (Z.otherEnd h x)
    (Measured.fromOld C R symm Z h x) reach.1 h.1.1 h.1.2 h.2 port last
  simp only [directory,found,Option.elim_some]
  exact trueRank


include coord found in
theorem funded {a : ℕ} (shelf : Measured.Shelf C R Z)
    (small : ∀h path x (s : ParentFilter.Source (breadth D) Q K cap) j,
      Machine.fields R (Z.venue h) path (Z.loc x).1 s j<2^a)
    (h : Stage.Host J V k) (j : Fin (breadth D*O)) :
    let scanned:=Fused.filtered (Fused.fetched C R Z shelf small h j)
    let dir:=directory old next pitch rack wide (name h.1.2)
    SIMD.lookup dir (PeerQuery.number scanned) (List.finRange ((breadth D*breadth D)*Q)) =
      peerCell (b:=b) A native S ready cnames C h (DescentOrdinarySignedRanks.resident ((res).address h) j) := by
  intro scanned dir
  have physical : scanned=place ((res).address h) ((res).entry h) j := Fused.fetched_read C R symm Z shelf small h j
  by_cases hit : ∃x, (res).address h x=j
  · obtain ⟨x,rfl⟩:=hit
    rw [place_at] at physical
    rw [physical,DescentOrdinarySignedRanks.resident_at]
    have number : (PeerQuery.number (some ((res).entry h x))).val=((res).entry h x).peer.val+1 := by rfl
    rw [SIMD.lookup_at dir _ _ number,ite_eq_left (List.mem_finRange _)]
    apply Fin.ext
    change (dir ((res).entry h x).peer).val=(((DescentResetWindowFields.neighbor A native S ready cnames C h
      (residentFace A native C h x)).val:Cell b)).val
    rw [Fin.val_cast_of_lt ((DescentResetWindowFields.neighbor A native S ready cnames C h
      (residentFace A native C h x)).isLt.trans wide)]
    exact measured_rank A native S ready group name C R symm Z pitch rack wide coord found h x
  · have absent:=place_empty ((res).address h) ((res).entry h) j (not_exists.mp hit)
    rw [absent] at physical
    rw [physical,DescentOrdinarySignedRanks.resident_miss _ _ (not_exists.mp hit)]
    exact SIMD.lookup_missing dir _ (fun g=>Nat.zero_ne_add_one _) _

end Measured

end
end Hierarchy.DescentOrdinaryCompactPeer

end OAI
