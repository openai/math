import OAI.Hierarchy.DescentDatedSignedPrefixFits
import OAI.Hierarchy.DescentDatedSignedHeaderFits
import OAI.Hierarchy.DescentDatedOrdinarySignedMeasured
import OAI.Hierarchy.DescentDatedSignedHome
import OAI.Hierarchy.DescentDatedCompactPeerIssued

namespace OAI
/-! The successor signed input is produced at exactly the vertex, group,
block, and socket read by the next genuine ordinary/reset calendar. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty DescentSixParty.Chronology DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentOrdinarySignedParents DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentOrdinarySignedRanks DescentPackedChildNeighbor DescentHostDirectory
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin U J E X T V:Type} [Field F] [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U] [Fintype E] [Fintype X] [Fintype T]
  {d k i D Q O K b M H groups oldH w:ℕ} {bits:Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ}
variable (A:GroupStage W G price ε J U k) (native:W.graph.Edge↪ℕ) (S:DescentCompiler.AtomSchedule)
  (ready:A.StateBounds S i) (names:Stage.Host J U k↪ℕ) (C:Blocks (Stage.source A native) E) (marked:E→Prop)
  (R:Fin oldH→Fin D→Option (Fin oldH)) (symm:∀v u p,R v p=some u→∃z,R u z=some v)
  (Z:Measured C R X T V Q O K A.cap) (shelf:Measured.Shelf C R Z)
  (small:∀h path x (s:ParentFilter.Source (breadth D) Q K A.cap) f,Machine.fields R (Z.venue h) path (Z.loc x).1 s f<2^b)
  (orders:∀h (e f:Local C h),Incidence.srcKey C R symm Z h e<Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))

local notation "s"=> (⟨2^k,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩:SignedExtent)
local notation "Prep" => DescentPacking.PackedMatch.Local.Stage.Prepare.spreadField
variable (group:J↪Fin groups) (host:U↪Fin H)

local notation "who" =>wholeHost group host
local notation "P₀"=>breadth D
local notation "parents"=>Measured.roster C R symm Z
local notation "oldEnd"=>PairRanks.combined (Gather.reaching R)
local notation "nearby"=>DescentPacking.PackedMatch.Local.Stage.hostRotor host (DescentGroupPeerOrder.hostRoster A (host.trans Fin.valEmbedding))
local notation "name"=>DescentPacking.PackedMatch.Local.Stage.cableNames k (DescentStageEdgeReceipt.groupRank (group.trans Fin.valEmbedding) (host.trans Fin.valEmbedding))
variable (I:(⟨2^k,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩:SignedExtent).Input) (base:ℕ) (m:Memory w)
local notation "sheet"=>(s).installed I base m
local notation "priorRaw"=>fun (z:(s).Socket)=>Fused.cell C R Z shelf small (who z.1) z.2
local notation "sourceLocal" e=>(⟨(e).val,(e).property.1,Or.inl rfl⟩:Local C (C.src (e).val))

include orders in
theorem phase_from_hosts_heads (prior:(s).Prior I base w) (room:(s).roof base+max (s).slab (s).oldSlab<2^w)
    (t₂:(s).PeerInputs I base w)
    (size:P₀*P₀<2^b) (degree:I.newDegree=A.degree) (emission:DescentResetWindowFields.Emission A native C marked)
    (headers:DescentOrdinaryDonorRankDirectory.Reads R I.rankBanks m)
    (donors:(s).Donors I R priorRaw base m) (v:(s).RouteDigits) (routes:v.Earlier I m)
    (physical:∀u, (host u.1.2).val=(Z.venue u).1.val*I.hostPitch+(Z.venue u).2.val)
    (lowFits:∀u,(Z.venue u).2.val<I.hostPitch)
    (raw:∀h (e:Local C h),Z.loc (Z.raw h e)=Z.loc (Z.raw (C.src e.val) (sourceLocal e)))
    (forward:∀x h g t,who x h g=some t→∀e:Local C t,
      let a:=Z.loc (Z.raw t e);v.forward x a.2 a.1 g=Packed.token (some (Z.read (C.src e.val) (sourceLocal e)).src.path))
    (low:∀x h g t,who x h g=some t→∀e:Local C t,
      let a:=Z.loc (Z.raw t e);(v.low x a.2 a.1 g).val=(Z.venue (C.src e.val)).2.val)
    (tokens:∀x o u g,Packed.token (Packed.readToken P₀ (v.forward x o u g))=v.forward x o u g)
    (back:∀x o u g,v.back x o u g=SourceReturn.Query.packedRoute R u (Packed.readToken _ (v.forward x o u g)))
    (ports:Mounted I.ports (Gather.reaching R) m groups M)
    (reverse:∀h p,m (I.reversePath.base+(DescentHaloWalkRAM.row h p).val)=(Rebase.value R .path h p:Word w))
    (ranked:∀u j,m (I.priorRanks.base+(u.val*(P₀*P₀)+j.val))=(rank oldEnd u j:Word w))
    (endpoints:∀u j,m (I.priorEnds.base+(u.val*(P₀*P₀)+j.val))=(number (oldEnd u j):Word w))
    (neighbors:∀u j,m (I.newNeighbors.base+(u.val*A.degree+j.val))=(number (nearby u j):Word w))
    (mb:Fin (2^k)→Fin (P₀*O)→Fin H→Fin groups→Cell 1)
    (bits_:∀x j,Source (I.mark (x,j)) (mb x j) M m) (marks:∀z,(I.mark z).Fits w base)
    (known:∀x j h g u,who x h g=some u→∀e:Local C u,(parents).address u e=j→((mb x j h g).val=1 ↔ marked e.val))
    (digits:max (A.degree+1) (A.cap+1)<2^b) (codes:P₀*P₀*Q≤2^b) (tickets:K≤2^b):
    ((∀x axis j, let field:=(s).retainedRankField base x axis j
        field.Fits w ((s).roof base) ∧ Source field
          (fun h g=>(DescentOrdinarySignedRanks.result C (Incidence.of_measured C R symm Z orders) who (Stage.measured A native S ready) x axis j h g : Cell b))
          M ((s).phaseImage I base m)) ∧ (∀x j, let field:=(s).peerField I base (x,j)
        field.Fits w ((s).roof base) ∧ Source field
          (signedPeer (b:=b) A native S ready name C R symm Z who x j) M ((s).phaseImage I base m))) ∧
    ((s).phase I base w).Runs m ∧
    (∀x j,Reads ((s).page base x j) (fun h g=>DescentSignedCableCodec.encode
      (DescentPacking.PackedMatch.Local.Stage.Prepare.signed A native S ready group host x j h g)) M ((s).phaseImage I base m)) ∧
    (∀a,a<base ∨ (s).roof base≤a→(s).phaseImage I base m a=m a) ∧ CheapCode ((s).phase I base w).program:=by
  have space:(s).roof base<2^w:=(Nat.le_add_right ..).trans_lt room
  have t₀:=(s).local_room base I room prior.path prior.endpoint prior.material
  have fg:=(s).flags_fits I base prior room
  have t₁:=(s).return_room I base prior room fg
  have fits:=(s).fits_from_prior I base prior room ((s).peer_head_fits I base room t₂) ((s).signed_header_fits I base prior room) fg
  have geometry:=route_of_hosts A native C R Z group host I v physical lowFits raw forward low back
  have located:∀(x:Fin (2^k)) (h:Fin H) (g:Fin groups) (u:Stage.Host J U k),who x h g=some u→h=host u.1.2:=
    fun x h g u present=>((wholeHost_iff group host x h g u).mp present).2.1.symm
  have found (u:Stage.Host J U k):(s).rack I.hostPitch (host u.1.2)=some (Z.venue u).1:=
    geometry.receiver u.2 (host u.1.2) (group u.1.1) u ((wholeHost_iff group host _ _ _ _).mpr ⟨rfl,rfl,rfl⟩)
  have result:=phase_from_prior_heads A native S ready name C marked R symm Z shelf small orders who I base m
    fits space t₀ t₁ size degree emission headers donors v routes geometry ports reverse tokens mb bits_ marks known
    (fun readings=>signed_peer_field A native S ready (group.trans Fin.valEmbedding) host C R symm Z shelf small who I base m
      fits space t₂ physical found located ranked endpoints neighbors (fun x j=>readings (x,j)) degree
      ((Nat.le_succ _).trans_lt ((le_max_left _ _).trans_lt digits))) digits codes tickets
  refine ⟨result.1,result.2.1,?_,result.2.2.2⟩
  intro x j
  simpa only [signed_target A native S ready host group name,DescentPacking.PackedMatch.Local.Stage.Prepare.signed]
    using result.2.2.1 x j

include orders in
theorem phase_from_hosts (prior:(s).Prior I base w) (room:(s).roof base+max (s).slab (s).oldSlab<2^w)
    (t₂:(s).PeerInputs I base w)
    (size:P₀*P₀<2^b) (degree:I.newDegree=A.degree) (emission:DescentResetWindowFields.Emission A native C marked)
    (headers:DescentOrdinaryDonorRankDirectory.Reads R I.rankBanks m)
    (donors:(s).Donors I R priorRaw base m) (v:(s).RouteDigits) (routes:v.Earlier I m)
    (physical:∀u, (host u.1.2).val=(Z.venue u).1.val*I.hostPitch+(Z.venue u).2.val)
    (lowFits:∀u,(Z.venue u).2.val<I.hostPitch)
    (raw:∀h (e:Local C h),Z.loc (Z.raw h e)=Z.loc (Z.raw (C.src e.val) (sourceLocal e)))
    (forward:∀x h g t,who x h g=some t→∀e:Local C t,
      let a:=Z.loc (Z.raw t e);v.forward x a.2 a.1 g=Packed.token (some (Z.read (C.src e.val) (sourceLocal e)).src.path))
    (low:∀x h g t,who x h g=some t→∀e:Local C t,
      let a:=Z.loc (Z.raw t e);(v.low x a.2 a.1 g).val=(Z.venue (C.src e.val)).2.val)
    (tokens:∀x o u g,Packed.token (Packed.readToken P₀ (v.forward x o u g))=v.forward x o u g)
    (back:∀x o u g,v.back x o u g=SourceReturn.Query.packedRoute R u (Packed.readToken _ (v.forward x o u g)))
    (ports:Mounted I.ports (Gather.reaching R) m groups M)
    (reverse:∀h p,m (I.reversePath.base+(DescentHaloWalkRAM.row h p).val)=(Rebase.value R .path h p:Word w))
    (ranked:∀u j,m (I.priorRanks.base+(u.val*(P₀*P₀)+j.val))=(rank oldEnd u j:Word w))
    (endpoints:∀u j,m (I.priorEnds.base+(u.val*(P₀*P₀)+j.val))=(number (oldEnd u j):Word w))
    (neighbors:∀u j,m (I.newNeighbors.base+(u.val*A.degree+j.val))=(number (nearby u j):Word w))
    (mb:Fin (2^k)→Fin (P₀*O)→Fin H→Fin groups→Cell 1)
    (bits_:∀x j,Source (I.mark (x,j)) (mb x j) M m) (marks:∀z,(I.mark z).Fits w base)
    (known:∀x j h g u,who x h g=some u→∀e:Local C u,(parents).address u e=j→((mb x j h g).val=1 ↔ marked e.val))
    (digits:max (A.degree+1) (A.cap+1)<2^b) (codes:P₀*P₀*Q≤2^b) (tickets:K≤2^b):
    ((s).phase I base w).Runs m ∧
    (∀x j,Reads ((s).page base x j) (fun h g=>DescentSignedCableCodec.encode
      (DescentPacking.PackedMatch.Local.Stage.Prepare.signed A native S ready group host x j h g)) M ((s).phaseImage I base m)) ∧
    (∀a,a<base ∨ (s).roof base≤a→(s).phaseImage I base m a=m a) ∧ CheapCode ((s).phase I base w).program:=
  (phase_from_hosts_heads A native S ready C marked R symm Z shelf small orders group host I base m
    prior room t₂ size degree emission headers donors v routes physical lowFits raw forward low tokens back ports reverse ranked endpoints neighbors mb bits_ marks known digits codes tickets).2

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
