import OAI.Hierarchy.DescentDatedCompactPeerTables
import OAI.Hierarchy.DescentDatedSignedHeader

namespace OAI
/-! # The measured peer field of the actual signed ordinary program -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty DescentSixParty.Chronology DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentOrdinarySignedParents DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open DescentPackedChildNeighbor DescentGroupPeerOrder DescentHostDirectory DescentIssuedFallbackPanel
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentStageEdgeReceipt
open DescentOrdinarySignedMeta DescentOrdinarySignedRanks DescentResetFieldAssembler
open DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin U J E X T V:Type} [Field F] [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U] [Fintype E] [Fintype X] [Fintype T]
  {d k i D Q O K b M H groups blocks oldH w:ℕ} {bits:Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ}
variable (A:GroupStage W G price ε J U k) (native:W.graph.Edge↪ℕ) (S:DescentCompiler.AtomSchedule)
  (ready:A.StateBounds S i) (group:J↪ℕ) (name:U↪Fin H) (C:Blocks (Stage.source A native) E) (marked:E→Prop)
  (R:Fin oldH→Fin D→Option (Fin oldH)) (symm:∀v u p,R v p=some u→∃z,R u z=some v)
  (Z:Measured C R X T V Q O K A.cap) (shelf:Measured.Shelf C R Z)
  (small:∀h path x (s:ParentFilter.Source (breadth D) Q K A.cap) f,Machine.fields R (Z.venue h) path (Z.loc x).1 s f<2^b)
  (orders:∀h (e f:Local C h),Incidence.srcKey C R symm Z h e<Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))
  (home:Fin blocks→Fin H→Fin groups→Option (Stage.Host J U k))
local notation "e₀" => (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩:SignedExtent)
local notation "names" => cableNames k (groupRank group (name.trans Fin.valEmbedding))
local notation "oldEnd" => PairRanks.combined (Gather.reaching R)
local notation "next" => hostRotor name (hostRoster A (name.trans Fin.valEmbedding))
local notation "P₀" => breadth D
local notation "old₀" => signedRaw C R Z shelf small home
local notation "p₀" => signedPeer (b:=b) A native S ready names C R symm Z home
variable (I : (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).Input) (base : ℕ) (m : Memory w)
local notation "sheet" => (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).installed I base m
variable (fits : (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).Fits I base w) (space : (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).roof base<2^w)
  (geo : (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).PeerInputs I base w)
  (coord : ∀h : Stage.Host J U k,(name h.1.2).val=(Z.venue h).1.val*I.hostPitch+(Z.venue h).2.val)
  (found : ∀h : Stage.Host J U k,DescentOrdinaryCompactPeer.ROM.rack oldH I.hostPitch (name h.1.2)=some (Z.venue h).1)
  (located : ∀x h g u,home x h g=some u→h=name u.1.2)
  (ranks : ∀v j,m (I.priorRanks.base+(v.val*(breadth D*breadth D)+j.val))=(rank (PairRanks.combined (Gather.reaching R)) v j:Word w))
  (endpoints : ∀v j,m (I.priorEnds.base+(v.val*(breadth D*breadth D)+j.val))=(number (PairRanks.combined (Gather.reaching R) v j):Word w))
  (neighbors : ∀v j,m (I.newNeighbors.base+(v.val*A.degree+j.val))=(number (hostRotor name (hostRoster A (name.trans Fin.valEmbedding)) v j):Word w))
  (oldFields : ∀x j f, Source ((⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).rawField base (x,j) f)
    (fun v g=>Fused.columns (signedRaw C R Z shelf small home x j v g) f) M ((⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).installed I base m))

include fits space geo coord found located ranks endpoints neighbors oldFields in
theorem signed_peer_field (degree : I.newDegree=A.degree) (wide : A.degree<2^b)
    (x : Fin blocks) (j : Fin (P₀*O)) :
    Source ((e₀).peerField I base (x,j)) (p₀ x j) M sheet := by
  let chart:=SIMD.ROM.layout ((e₀).peerROMBase base) ((e₀).peerKinds) ((e₀).peerBits) b M
    (Nat.clog 2 ((e₀).slab)) ((e₀).peerDirectory base)
  let values:=DescentOrdinaryCompactPeer.directory oldEnd next I.hostPitch
    (DescentOrdinaryCompactPeer.ROM.rack oldH I.hostPitch) wide (Q:=Q)
  have header:= (e₀).compact_peer_degree I base m fits space degree geo oldEnd next wide ranks endpoints neighbors
  have tables:= (e₀).peer_lookup_tables I base m fits space values header
  have good:=(e₀).peer_chart_room I base fits space (x,j)
  have raw:=signed_gathered C R Z shelf small home I base m fits space oldFields x j
  have keys:=DescentOrdinarySocketPeer.read ((e₀).peerKeyBase base) ((e₀).tailStart base) ((e₀).gathered base (x,j))
    sheet good.qFits.1 ((e₀).funded_peer_key I base m fits space) (old₀ x j) raw
  have seen:=SIMD.measures chart _ _ good values sheet tables _ keys (List.finRange ((P₀*P₀)*Q))
  convert seen using 1 <;> first | rfl | skip
  funext v g
  cases live:home x v g with
  | none =>
    simp only [signedRaw,signedPeer,live,Option.bind_none,Option.elim_none,Fused.filtered]
    exact (SIMD.lookup_missing (values v) _ (fun _=>Nat.zero_ne_add_one _) _).symm
  | some u =>
    obtain rfl:=located x v g u live
    simp only [signedRaw,signedPeer,live,Option.bind_some,Option.elim_some,values]
    exact (DescentOrdinaryCompactPeer.funded A native S ready group name C R symm Z I.hostPitch
        (DescentOrdinaryCompactPeer.ROM.rack oldH I.hostPitch) wide coord found shelf small u j).symm

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
