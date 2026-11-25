import OAI.Hierarchy.TaggedWideSpillPooledRank
import OAI.Hierarchy.ProtocolRAMTurnAuthenticated

namespace OAI
/-! # The word-addressed neighbor edge and rank in the dated comparison -/
noncomputable section
namespace Hierarchy.ProtocolRAMDateSpillRank
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard WireTelescope
open ProtocolRAM ProtocolRAM.Calendar CoreRoute RouteSettlement ProtocolRAMTurnPrefix ProtocolRAMTurnReplayed
open scoped Classical Fin.CommRing
set_option quotPrecheck false
variable {W h d k K : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    (board : HistoryRoles.RoleProgram.Board) {place : Site h d k→Fin K}
    (B : Mount (S:=S) π place board.edges) (inj : Function.Injective place) (pad : Chord K) (o : Orders h d k)
    {lo : ℕ} {spill : Bank} {m out : Memory W} (read : RankRead B o lo spill m out)
local notation "D" => B.datedLayout inj pad
local notation "size" => board.edges+coreCount o
local notation "enum" => spillEnum B o
local notation "ord" => (D).nativeOrder enum
local notation "stock" => fun g=>actual spill m (PurchaseInventory.slot g)
local notation "bits" => (D).bits stock
local notation "v" => ProtocolRAMTurnSnapshot.values (board.itinerary (key lo size) (rank lo size board.edges)) out

include read

theorem RankRead.snapshot (i : Fin (coreCount o)) (words : 4*size≤2^W) (room : board.edges≤2^W)
    (live : 0<bits (ord (i.natAdd board.edges)).1)
    (capacity : ∀e,routeLoad B.ordinary stock e≤2^W) :
    let q:=ord (i.natAdd board.edges)
    (v).edge (board.edges+i.val)=(((D).routes q.1).get q.2).val ∧
    (v).starts (board.edges+i.val)=NativeSlot.start (D).routes bits ord q.1 q.2 := by
  intro q
  let e:=((D).routes q.1).get q.2
  have hit : e=wireAt B o i := by
    refine ((D).native_edge enum (i.natAdd board.edges)).trans ?_
    simp only [SettledMatrix.Layout.nativeEdge,finSumFinEquiv_symm_apply_natAdd,wireAt]
    rfl
  have keyRoom:size≤(ProtocolRAMTurnReplayed.key lo size).size:=ProtocolRAMPackedRanked.group_capacity _
  have rankRoom:4*size≤2^(ProtocolRAMPackedRanked.groupBits (4*size)):=ProtocolRAMPackedRanked.group_capacity _
  have floor: NativeSlot.start (D).routes bits ord q.1 q.2+bits q.1≤2^W :=
    (NativeSlot.start_room (D).routes bits ord q.1 q.2 live).trans
      (((D).measured stock e).le.trans (capacity e))
  have startSmall : NativeSlot.start (D).routes bits ord q.1 q.2<2^W := by change 0<bits q.1 at live;omega
  refine ⟨?_,?_⟩
  · exact (ProtocolRAMTurnSnapshot.key_at board (ProtocolRAMTurnReplayed.key lo size)
      (ProtocolRAMTurnReplayed.rank lo size board.edges) (i.natAdd board.edges)
      (wireAt B o i) out (by omega) keyRoom room (read.key i)).trans (congrArg Fin.val hit.symm)
  · exact ProtocolRAMTurnSnapshot.rank_at board (ProtocolRAMTurnReplayed.key lo size) (ranks lo size board.edges)
      (ProtocolRAMPackedRanked.groupBits (4*size)) (i.natAdd board.edges) _ out words rankRoom startSmall
      (RankRead.router_start B inj pad o spill m read i)

omit read in
private theorem numbered_hop {I J : Type*} (r : J → ℕ) (num : I ≃ J)
    (i : I) (j : J) (eqn : num i=j) (q : Fin (r (num i))) :
    (Equiv.sigmaCongrLeft (β:=fun x => Fin (r x)) num).symm ⟨j,q.cast (congrArg r eqn)⟩=⟨i,q⟩ := by
  subst j
  apply (Equiv.sigmaCongrLeft (β:=fun x=>Fin (r x)) num).injective
  exact (Equiv.apply_symm_apply _ _).trans rfl

private theorem RankRead.snapshot_at (j : Fin (coreCount o)) (z : Σi,Fin ((D).routes i).length)
    (eqn : ord (j.natAdd board.edges)=z) (words : 4*size≤2^W) (room : board.edges≤2^W)
    (live : 0<bits z.1) (capacity : ∀e,routeLoad B.ordinary stock e≤2^W) :
    (v).edge (board.edges+j.val)=(((D).routes z.1).get z.2).val ∧
    (v).starts (board.edges+j.val)=NativeSlot.start (D).routes bits ord z.1 z.2 := by
  subst z
  exact RankRead.snapshot board B inj pad o read j words room live capacity

set_option maxHeartbeats 900000 in
/-- The same numeric read at the oriented hop of the particular commodity
selected by the canonical sparse row chart. -/
theorem RankRead.snapshot_good (i : Fin (board.edges+ProtocolRAM.PurchaseInventory.footprint h (Stages h d) k))
    (g : Commodity (Fin (2^h)) (Stages h d) k) (row : (D).num i=.inr (.inl g))
    (q : Fin ((D).routes i).length) (words : 4*size≤2^W) (room : board.edges≤2^W)
    (live : 0<bits i) (capacity : ∀e,routeLoad B.ordinary stock e≤2^W) :
    let hop:=q.cast (congrArg (fun z=>((D).data.steps z).length) row)
    let a:=board.edges+(goodIndex B inj pad o g hop).val
    (v).edge a=(((D).routes i).get q).val ∧ (v).starts a=NativeSlot.start (D).routes bits ord i q := by
  intro hop a
  have same:goodHop B inj pad g hop=⟨i,q⟩ :=
    numbered_hop (fun z=>((D).data.steps z).length) (D).num i _ row q
  have entry:ord ((goodIndex B inj pad o g hop).natAdd board.edges)=⟨i,q⟩:=
    (goodIndex_hop B inj pad o g hop).trans same
  exact RankRead.snapshot_at board B inj pad o read (goodIndex B inj pad o g hop) ⟨i,q⟩
    entry words room live capacity

end Hierarchy.ProtocolRAMDateSpillRank
end

end OAI
