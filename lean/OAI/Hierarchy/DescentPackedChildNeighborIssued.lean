import OAI.Hierarchy.DescentPackedChildNeighbor

namespace OAI
/-! # The compact eight-hop lookup reports the actual signed child cable field -/
namespace Hierarchy.DescentPackedChildNeighbor
open DescentSixParty DescentGroupPeerOrder DescentStageEdgeReceipt DescentHostDirectory DescentSharedCableNames
open DescentPacking.PackedMatch.Local.Stage DescentIssuedFallbackPanel DescentHaloWalkRAM DescentParallelBase.ParentFilter
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentColonies
open scoped Classical Fin.CommRing
noncomputable section
variable {F J V T : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i E Q H w : ℕ} {bits : T→ℕ} {W : MarkedWorld F d T bits} {g : PoweredGadget F} {price ε : ℝ}
/-- The exact low digit of a normalized successor host. The omitted heap
slot is the unused all-ones code, including on inactive old racks. -/
def lowDigit {U : Type} [Fintype U] {k slots : ℕ} (u : ↥(keys (V:=U) k slots)) : Fin ((2^(k+1)-1)*slots) :=by
  let v:=Finset.mem_product.mp (Finset.mem_product.mp u.property).2
  have hi:=codes_valid v.1
  let t:=nodeNumber u.val.2.1.1 u.val.2.1.2
  have ix:t<2^(k+1)-1:=(node_range hi.2).2.trans_le (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ hi.1)) _)
  have j:u.val.2.2<slots:=Finset.mem_range.mp v.2
  exact ⟨t*slots+u.val.2.2,(Nat.add_lt_add_left j _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ ix)⟩

def nextName {U : Type} [Fintype U] {k slots : ℕ} (prior : U↪Fin (Fintype.card U)) : ↥(keys (V:=U) k slots)↪Fin (Fintype.card U*((2^(k+1)-1)*slots)) :=
  (DescentRosterOrder.compact ((packedEmbedding prior (Function.Embedding.subtype _) (fun v=>v.2)).trans Fin.valEmbedding)).trans
    (finCongr (by rw [card_fullHost prior];ring)).toEmbedding

theorem next_name {U : Type} [Fintype U] {k slots : ℕ} (prior : U↪Fin (Fintype.card U)) (u : ↥(keys (V:=U) k slots)) :
    nextName prior u=host (prior u.val.1) (lowDigit u) :=by
  apply Fin.ext
  change (DescentRosterOrder.compact ((packedEmbedding prior (Function.Embedding.subtype _) (fun v=>v.2)).trans Fin.valEmbedding) u).val=_
  rw [compact_fullHost,host_val]
  change ((prior u.val.1).val*(2^(k+1)-1)+_)*slots+_= (prior u.val.1).val*((2^(k+1)-1)*slots)+(nodeNumber u.val.2.1.1 u.val.2.1.2*slots+u.val.2.2)
  ring

variable (A : GroupStage W g price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (group : J↪ℕ) (name : V↪Fin (H*Q))
local notation "vertex" => name.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank group vertex)
local notation "neighbors" => hostRotor name (hostRoster A vertex)

private theorem sorted_at (v : V) (j : Fin A.degree) : neighbors (name v) j=(hostRoster A vertex v j).map name := by
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

theorem live_rank (adj : Fin H→Fin E→Option (Fin H)) (v old other : Fin H) (mine : Fin Q) (path : Fin (breadth E)) (dest : Endpoint (breadth E) Q)
    (there : Gather.reaching adj v path=some old) (across : Gather.reaching adj old dest.path=some other)
    (j : J) (a : V) (x : Block k) (port : A.CellPorts j a x)
    (source : name a=host v mine)
    (endpoint : name (((Stage.source A native).peer ((j,a),x) (Stage.ofPort A native ((j,a),x) port).val).1.2)=host other dest.low) :
    value (PairRanks.combined (Gather.reaching adj)) neighbors ((v,mine),finProdFinEquiv.symm (peer adj v path dest))=
      (Stage.live A native S ready names ((j,a),x) port).neighbor.val := by
  let h:=((j,a),x);let z:=(Stage.source A native).peer h (Stage.ofPort A native h port).val
  let slot:=(Stage.live A native S ready names h port).neighbor
  have key : (hostRoster A vertex a slot).map (fun u=>((j,u),x))=some z:=
    (physicalPeer_group A group vertex j a x slot).symm.trans (physicalPeer_read A native S ready names h port)
  have localHit : hostRoster A vertex a slot=some z.1.2 := by
    obtain ⟨u,hit,which⟩:=Option.map_eq_some_iff.mp key
    exact hit.trans (congrArg (fun t=>some t.1.2) which)
  apply filter_peer adj neighbors v old other mine path dest slot there across
  · rw [←source,sorted_at,localHit,Option.map_some,←endpoint]
  · intro t hit
    rw [←source,sorted_at,←endpoint] at hit
    obtain ⟨u,seen,equal⟩:=Option.map_eq_some_iff.mp hit
    exact unique_name A name (seen.trans (congrArg some (name.injective equal))) localHit

/-- In the terminal sorted successor host chart this is a RAM read by either
grain endpoint. The same concluded field is used by the signed cable codec. -/
theorem live_word (adj : Fin H→Fin E→Option (Fin H)) (B : Banks) (out : ℕ)
    (fit : Room B H (breadth E*breadth E) Q A.degree w out) (m : Memory w)
    (old : Mounted B (PairRanks.combined (Gather.reaching adj)) neighbors m)
    (v donor other : Fin H) (mine : Fin Q) (p : Fin (breadth E)) (dest : Endpoint (breadth E) Q)
    (there : Gather.reaching adj v p=some donor) (across : Gather.reaching adj donor dest.path=some other)
    (j : J) (a : V) (x : Block k) (port : A.CellPorts j a x) (source : name a=host v mine)
    (endpoint : name (((Stage.source A native).peer ((j,a),x) (Stage.ofPort A native ((j,a),x) port).val).1.2)=host other dest.low) :
    let L:=breadth E*breadth E;let n:=(H*Q)*(L*Q);let compiled:=body B H L A.degree
    let q:=((v,mine),finProdFinEquiv.symm (peer adj v p dest))
    image out n compiled m (out+(rowId H L Q q).val)=((Stage.live A native S ready names ((j,a),x) port).neighbor.val:Word w) := by
  have posted:=(run B out fit (PairRanks.combined (Gather.reaching adj)) neighbors m old).2.1 ((v,mine),finProdFinEquiv.symm (peer adj v p dest))
  exact posted.trans (congrArg (fun n : ℕ=>(n:Word w)) (live_rank A native S ready group name adj v donor other mine p dest there across j a x port source endpoint))

end
end Hierarchy.DescentPackedChildNeighbor

end OAI
