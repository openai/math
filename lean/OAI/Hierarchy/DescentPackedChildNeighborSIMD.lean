import OAI.Hierarchy.DescentPackedChildNeighborIssued
import OAI.Hierarchy.DescentPackedHostLookup

namespace OAI
/-! # Packed lookup in a measured, host-dependent short neighbor directory -/
namespace Hierarchy.DescentPackedChildNeighbor.SIMD
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentColonies
open scoped Classical Fin.CommRing
noncomputable section
variable {H G T a b M w L Q D : ℕ}

private theorem search_le (f : Fin D→ℕ) (x : ℕ) (js : List (Fin D)) : search f Fin.val x D js≤D :=by
  induction js with | nil=>rfl | cons j js ih=>simp only [search];split;exact j.isLt.le;exact ih

theorem value_le (ends : Fin H→Fin L→Option (Fin H)) (roster : Fin (H*Q)→Fin D→Option (Fin (H*Q))) (z : Key H L Q) : value ends roster z≤D :=by
  dsimp only [value]
  split
  · exact le_rfl
  · exact search_le ..

def directory (ends : Fin H→Fin L→Option (Fin H)) (roster : Fin (H*Q)→Fin D→Option (Fin (H*Q))) (wide : D<2^b)
    (h : Fin (H*Q)) (j : Fin (L*Q)) : Cell b :=
  ⟨value ends roster (finProdFinEquiv.symm h,finProdFinEquiv.symm j),(value_le ..).trans_lt wide⟩

theorem header_words (ends : Fin H→Fin L→Option (Fin H)) (roster : Fin (H*Q)→Fin D→Option (Fin (H*Q))) (wide : D<2^b)
    (m : Memory w) (base : ℕ) (read : ∀z,m (base+(rowId H L Q z).val)=(value ends roster z:Word w))
    (h : Fin (H*Q)) (j : Fin (L*Q)) : m (base+(h.val*(L*Q)+j.val))=((directory ends roster wide h j).val:Word w) :=by
  have seen:=read (finProdFinEquiv.symm h,finProdFinEquiv.symm j)
  simpa only [rowId,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply,Equiv.apply_symm_apply,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm,directory] using seen

section Issued
open DescentSixParty DescentGroupPeerOrder DescentStageEdgeReceipt DescentHostDirectory DescentSharedCableNames
open DescentPacking.PackedMatch.Local.Stage DescentIssuedFallbackPanel DescentHaloWalkRAM DescentParallelBase.ParentFilter
variable {F J V U : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i E : ℕ} {bits : U→ℕ} {W : MarkedWorld F d U bits} {powg : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W powg price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (group : J↪ℕ) (name : V↪Fin (H*Q))
local notation "vertex" => name.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank group vertex)
local notation "neighbors" => hostRotor name (hostRoster A vertex)

/-- The actual packed result read at a child's source or target contains
exactly the normalized signed panel's short neighbor. -/
theorem issued_digit (adj : Fin H→Fin E→Option (Fin H)) (wide : A.degree<2^b)
    (query : Fin (H*Q)→Fin G→Cell a) (out : ℕ) (done : Memory w)
    (read : ∀p : Row (H*Q) G M,done (out+(row (H*Q) G M p).val)=((data (fun h g=>lookup
      (directory (PairRanks.combined (Gather.reaching adj)) neighbors wide h) (query h g) (List.finRange ((breadth E*breadth E)*Q))) p).val:Word w))
    (v donor other : Fin H) (mine : Fin Q) (p : Fin (breadth E)) (dest : Endpoint (breadth E) Q)
    (there : Gather.reaching adj v p=some donor) (across : Gather.reaching adj donor dest.path=some other)
    (j : J) (rack : V) (x : Block k) (port : A.CellPorts j rack x) (source : name rack=host v mine)
    (endpoint : name (((Stage.source A native).peer ((j,rack),x) (Stage.ofPort A native ((j,rack),x) port).val).1.2)=host other dest.low)
    (g : Fin G) (observed : (query (host v mine) g).val=(peer adj v p dest).val+1) (lanes : 0<M) (width : b*M≤w) :
    digit b (lane g lanes).val (done (out+(row (H*Q) G M (position (host v mine) g lanes)).val)).val=(Stage.live A native S ready names ((j,rack),x) port).neighbor.val :=by
  have got:=digit_of_words (directory (PairRanks.combined (Gather.reaching adj)) neighbors wide) query out done read (host v mine) g (peer adj v p dest) observed lanes width
  apply got.trans
  simp only [directory,host,Equiv.symm_apply_apply]
  exact live_rank A native S ready group name adj v donor other mine p dest there across j rack x port source endpoint
end Issued

end
end Hierarchy.DescentPackedChildNeighbor.SIMD

end OAI
