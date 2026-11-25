import OAI.Hierarchy.DescentOrdinarySignedMeta
import OAI.Hierarchy.DescentParentFilterFused
import OAI.Hierarchy.DescentPackedChildPeerQuery

namespace OAI
/-! # A measured resident parent reads its normalized opposite-host rank -/
namespace Hierarchy.DescentOrdinarySignedMeta
open DescentSixParty DescentSharedCableNames DescentNextSignedWindow DescentParallelBase
open DescentParallelBase.ParentFilter DescentGroupPeerOrder DescentStageEdgeReceipt DescentHostDirectory
open DescentPacking.PackedMatch.Local.Stage DescentIssuedFallbackPanel DescentHaloWalkRAM
open DescentPackedChildNeighbor DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F U J V E X T V₀ : Type} [Field F] [Fintype J] [DecidableEq J]
  [Fintype V] [DecidableEq V] [Fintype E] [Fintype X] [Fintype T] {d k i b H Q D O K L : ℕ}
  {bits : U→ℕ} {W : MarkedWorld F d U bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
  (group : J↪ℕ) (name : V↪Fin (H*Q)) (C : Blocks (Stage.source A native) E)
  (R : Fin H→Fin D→Option (Fin H)) (symm : ∀v u j,R v j=some u→∃l,R u l=some v)
  (Z : Measured C R X T V₀ Q O K L)
local notation "P" => breadth D
local notation "Host" => Stage.Host J V k
local notation "names" => cableNames k (groupRank group (name.trans Fin.valEmbedding))
local notation "roster" => hostRotor name (hostRoster A (name.trans Fin.valEmbedding))
local notation "res" => Measured.roster C R symm Z
variable (wide : A.degree<2^b)
  (coord : ∀h : Stage.Host J V k,name h.1.2=host (Z.venue h).1 (Z.venue h).2)

omit [Fintype E] in
theorem issued_port_order (h : Stage.Host J V k) (t : GrainPorts.Unit A native C h) :
    (Stage.ofPort A native h (GrainPorts.port A native C h t)).val = C.order t.val.1 := by
  have word (p : A.CellPorts h.1.1 h.1.2 h.2) :
      (Stage.ofPort A native h p).val = Stage.stream A native (Stage.recover A h p) := by
    cases p <;> rfl
  rw [word,(GrainPorts.value A native C h t).1]
  exact (Stage.stream A native).apply_symm_apply _

include coord in
/-- The directory result for a positive row is the neighbor number used by the
actual first-grain port. The source endpoint also handles a loop. -/
theorem measured_peer_rank (h : Host) (x : Local C h) :
    (SIMD.directory (PairRanks.combined (Gather.reaching R)) roster wide
      (host (Z.venue h).1 (Z.venue h).2) ((res).entry h x).peer).val =
    (DescentResetWindowFields.neighbor A native S ready names C h (residentFace A native C h x)).val := by
  let f:=residentFace A native C h x
  let u:=DescentResetWindowFields.firstUnit A native C h f
  let port:=GrainPorts.port A native C h u
  have edge : u.val.1.1=x.val := residentFace_edge A native C h x
  have here : (Stage.source A native).peer h (Stage.ofPort A native h port).val=other C h x := by
    dsimp only [port]
    rw [Ends.peer,issued_port_order A native C h u,C.atSource,C.atTarget,edge]
    rfl
  have reach:=Z.otherFields h x
  have last : name (((Stage.source A native).peer h (Stage.ofPort A native h port).val).1.2)=
      host (Z.venue (other C h x)).1 (Z.otherEnd h x).low := by rw [here,reach.2,coord]
  have trueRank := live_rank A native S ready group name R (Z.venue h).1 (Z.old h x)
    (Z.venue (other C h x)).1 (Z.venue h).2 (Measured.visit C R symm Z h x) (Z.otherEnd h x)
    (Measured.fromOld C R symm Z h x) reach.1 h.1.1 h.1.2 h.2 port (coord h) last
  change (SIMD.directory _ _ wide (host (Z.venue h).1 (Z.venue h).2) (peer R (Z.venue h).1 (Measured.visit C R symm Z h x) (Z.otherEnd h x))).val = (Stage.live A native S ready names h port).neighbor.val
  simpa only [SIMD.directory,host,Equiv.symm_apply_apply] using trueRank

include coord in
/-- Read the true eight-hop key from the physically filtered eleven words.
An unoccupied fixed slot requests zero and returns zero. -/
theorem funded_peer {a : ℕ} (shelf : Measured.Shelf C R Z)
    (small : ∀h path x (s : ParentFilter.Source P Q K L) j,
      Machine.fields R (Z.venue h) path (Z.loc x).1 s j<2^a)
    (h : Host) (j : Fin (P*O)) :
    let scanned:=Fused.filtered (Fused.fetched C R Z shelf small h j)
    let dir:=SIMD.directory (PairRanks.combined (Gather.reaching R)) roster wide
      (host (Z.venue h).1 (Z.venue h).2)
    SIMD.lookup dir (PeerQuery.number scanned) (List.finRange ((P*P)*Q)) =
      peerCell (b:=b) A native S ready names C h (DescentOrdinarySignedRanks.resident ((res).address h) j) := by
  intro scanned dir
  have physical : scanned=place ((res).address h) ((res).entry h) j := Fused.fetched_read C R symm Z shelf small h j
  by_cases hit : ∃x, (res).address h x=j
  · obtain ⟨x,rfl⟩:=hit
    rw [place_at] at physical
    rw [physical,DescentOrdinarySignedRanks.resident_at]
    have number : (PeerQuery.number (some ((res).entry h x))).val=((res).entry h x).peer.val+1 := by rfl
    rw [SIMD.lookup_at dir _ _ number,ite_eq_left (List.mem_finRange _)]
    apply Fin.ext
    change (dir ((res).entry h x).peer).val=(((DescentResetWindowFields.neighbor A native S ready names C h
      (residentFace A native C h x)).val:Cell b)).val
    rw [Fin.val_cast_of_lt ((DescentResetWindowFields.neighbor A native S ready names C h
      (residentFace A native C h x)).isLt.trans wide)]
    exact measured_peer_rank A native S ready group name C R symm Z wide coord h x
  · have absent:=place_empty ((res).address h) ((res).entry h) j (not_exists.mp hit)
    rw [absent] at physical
    rw [physical,DescentOrdinarySignedRanks.resident_miss _ _ (not_exists.mp hit)]
    exact SIMD.lookup_missing dir _ (fun g=>Nat.zero_ne_add_one _) _

include coord in
/-- Read the published query column through the prepared host directory at
every finite host and group. Padded hosts consume the actual zero query. -/
theorem funded_peer_source {a M w groups : ℕ} (shelf : Measured.Shelf C R Z)
    (small : ∀h path x (s : ParentFilter.Source P Q K L) j,
      Machine.fields R (Z.venue h) path (Z.loc x).1 s j<2^a)
    (positions : Fin (H*Q)→Fin groups→Option Host) (slot : Fin (H*Q)→Fin groups→Fin (P*O))
    (located : ∀v g h,positions v g=some h→v=host (Z.venue h).1 (Z.venue h).2)
    (chart : SIMD.Chart ((P*P)*Q)) (prior : Bank) (out : ℕ) (mem : Memory w)
    (fit : SIMD.Room chart (.lookup prior .row) (H*Q) groups (Packed.bits ((P*P)*Q)) b M w out)
    (rows : (H*Q)*chunks groups M≤prior.size)
    (setup : SIMD.Stored chart (H*Q) groups (Packed.bits ((P*P)*Q)) b M
      (SIMD.directory (PairRanks.combined (Gather.reaching R)) roster wide) mem)
    (old : DescentPackedColony.Reads prior (fun v g=>PeerQuery.number ((positions v g).bind
      (fun h=>Fused.filtered (Fused.fetched C R Z shelf small h (slot v g))))) M mem) :
    Source (SIMD.body chart (.lookup prior .row) (List.finRange ((P*P)*Q)))
      (fun v g=>(positions v g).elim 0 (fun h=>peerCell (b:=b) A native S ready names C h
        (DescentOrdinarySignedRanks.resident ((res).address h) (slot v g)))) M mem := by
  let values:=SIMD.directory (PairRanks.combined (Gather.reaching R)) roster wide
  let numbers:=fun v g=>PeerQuery.number ((positions v g).bind
    (fun h=>Fused.filtered (Fused.fetched C R Z shelf small h (slot v g))))
  have read:=source_column prior out fit.qFits.1 mem numbers rows old
  have body:=SIMD.measures chart (.lookup prior .row) out fit values mem setup numbers read
    (List.finRange ((P*P)*Q))
  convert body using 1
  funext v g
  cases occupied:positions v g with
  | none =>
    simp only [numbers,occupied,Option.bind_none,Option.elim_none]
    exact (SIMD.lookup_missing (values v) _ (fun j=>Nat.zero_ne_add_one _) _).symm
  | some h =>
    simp only [numbers,occupied,Option.bind_some,Option.elim_some]
    rw [show values v=values (host (Z.venue h).1 (Z.venue h).2) from congrArg values (located _ _ _ occupied)]
    exact (funded_peer A native S ready group name C R symm Z wide coord shelf small h (slot v g)).symm

end
end Hierarchy.DescentOrdinarySignedMeta

end OAI
