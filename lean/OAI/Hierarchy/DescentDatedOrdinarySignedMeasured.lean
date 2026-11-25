import OAI.Hierarchy.DescentDatedRetainedPeer
import OAI.Hierarchy.DescentDatedSignedGate

namespace OAI
/-! # Physical dated ordinary signed publication on the real two-sided cable geometry -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty DescentSixParty.Chronology DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentOrdinarySignedParents DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentOrdinarySignedRanks
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin U J E X T V:Type} [Field F] [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U] [Fintype E] [Fintype X] [Fintype T]
  {d k i D Q O K b M H groups blocks oldH w:ℕ} {bits:Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ}
variable (A:GroupStage W G price ε J U k) (native:W.graph.Edge↪ℕ) (S:DescentCompiler.AtomSchedule)
  (ready:A.StateBounds S i) (names:Stage.Host J U k↪ℕ) (C:Blocks (Stage.source A native) E) (marked:E→Prop)
  (R:Fin oldH→Fin D→Option (Fin oldH)) (symm:∀v u p,R v p=some u→∃z,R u z=some v)
  (Z:Measured C R X T V Q O K A.cap) (shelf:Measured.Shelf C R Z)
  (small:∀h path x (s:ParentFilter.Source (breadth D) Q K A.cap) f,Machine.fields R (Z.venue h) path (Z.loc x).1 s f<2^b)
  (orders:∀h (e f:Local C h),Incidence.srcKey C R symm Z h e<Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))
  (home:Fin blocks→Fin H→Fin groups→Option (Stage.Host J U k))
local notation "e₀" => (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩:SignedExtent)
local notation "census" => Incidence.of_measured C R symm Z orders
local notation "qr" => queryRaw C R symm Z shelf small orders home
local notation "ar" => itemRaw C R symm Z shelf small orders home
local notation "zhead" => DescentOrdinarySignedWindows.header A native S ready names C marked census home
local notation "target" => DescentOrdinarySignedWindows.target A native S ready names home

local notation "R₀" => Measured.roster C R symm Z
local notation "R₁" => Fused.fetched C R Z shelf small
local notation "flag" => signedControls C marked R symm Z home
local notation "walks" => Gather.reaching R
local notation "P" => breadth D


/-- Word bounds for the actual expressions of the three-column return path.
All components depend only on public address/width parameters. -/
structure ReturnRoom (s:SignedExtent) (I:s.Input) (base w:ℕ):Prop where
  oldRank:DescentOrdinaryDonorRankDirectory.Fits I.rankBanks base s.priorHosts s.reach w
  readRank:∀f,(DescentOrdinaryDonorRankDirectory.expression I.rankBanks s.priorHosts f).Fits w base
  head:∀i:Fin 3,(subbank base s.hdrRows i.val).Fits w (s.tailStart base)
  map:(subbank (s.mapBase base) s.viewRows 0).Fits w (s.tailStart base)
  transpose:∀l:Fin s.lowSites,(subbank (s.mapTranspose base) s.oldSlab l.val).Fits w (s.tailStart base)
  localBank:∀z f,(subbank (s.localStart base) s.slab (s.localId z f)).Fits w (s.tailStart base)
  donor:∀x o,(I.donorForward x o).Fits w base ∧ (I.donorLow x o).Fits w base
  reverse:I.reversePath.Fits w base
  reverseRows:s.priorHosts*s.reach≤I.reversePath.size
  reverseLookup:∀x o,DescentPackedChildNeighbor.SIMD.Room
    (DescentPackedChildNeighbor.SIMD.ROM.layout (s.reverseBase base) s.reach s.reverseBits s.reverseBits s.lanes
      (Nat.clog 2 s.oldSlab) I.reversePath) (I.donorForward x o) s.priorHosts s.groups s.reverseBits s.reverseBits s.lanes w (s.tailStart base)
  dir₁:∀x o,DescentPackedZip.Fits
    (DescentOrdinaryAtomFieldRAM.ROM.joined (DescentOrdinaryAtomFieldRAM.ROM.binary (SourceReturn.Query.forward s.reach s.lowSites) s.lanes)
      s.forwardBits (s.forwardBase base) id) (I.donorForward x o) (I.donorLow x o)
    (Packed.bits s.reach) (Packed.bits s.lowSites) s.lanes (s.tailStart base) w
  dir₂:∀x o,DescentPackedZip.Fits
    (DescentOrdinaryAtomFieldRAM.ROM.joined (DescentOrdinaryAtomFieldRAM.ROM.binary (SourceReturn.Query.finish s.reach s.lowSites) s.lanes)
      s.finishBits (s.backBase base) id)
    ((DescentOrdinaryAtomFieldRAM.ROM.joined (DescentOrdinaryAtomFieldRAM.ROM.binary (SourceReturn.Query.forward s.reach s.lowSites) s.lanes)
      s.forwardBits (s.forwardBase base) id).read (I.donorForward x o) (I.donorLow x o)) (s.backDigit I base x o)
    (Packed.bits (s.reach*s.lowSites)) (Packed.bits s.reach) s.lanes (s.tailStart base) w
  oldPort:∃B,Accessible I.ports B s.priorHosts s.groups s.lanes w base
  reach:∀c f l r,Accessible I.ports (subbank (s.projectedStart base) s.oldSlab (s.projectedId (s.sourceAt c r) f l))
    s.priorHosts s.groups s.lanes w (s.tailStart base)
  traverse:∀c f j,DescentPackedZip.Fits (SourceReturn.RAM.ROM.table s.reach s.lowSites s.fieldBits s.lanes (s.routeStart base) j)
    (s.routeQuery I base c.1.1 (s.priorSlot c).2) (peerExpr I.ports (subbank (s.projectedStart base) s.oldSlab (s.projectedId
      (s.sourceAt c (SourceReturn.RAM.parts j).2.2) f (SourceReturn.RAM.parts j).2.1)) s.priorHosts (SourceReturn.RAM.parts j).1)
    (Packed.bits s.routeTotal) s.fieldBits s.lanes (subbank (s.returnedStart base) s.oldSlab (s.returnedId c f)).base w
  returnEnd:∀c f,(subbank (s.returnedStart base) s.oldSlab (s.returnedId c f)).base+s.oldSlab<2^w
  cellRoot:(subbank (s.mapHost base) s.slab 0).Fits w (s.tailStart base)
  cellEnd:I.rankBanks.endpoints.Fits w (s.tailStart base)
  offset:(subbank (s.mapOffset base) s.priorHosts 0).Fits w (s.tailStart base)
  chunk:(subbank (s.mapChunk base) s.slab 0).Fits w (s.tailStart base)
  value:∀c f,(subbank (s.returnedStart base) s.oldSlab (s.returnedId c f)).Fits w (s.tailStart base)
  selectFit:∀(c:s.Consumer) f,DescentPackedZip.Fits (gateTable (s.gateStart base) s.fieldBits s.lanes)
    (s.flags I base (c.1.1,c.2.1)) (if c.1.2.val=2 then s.remoteWord I base c f else s.rawField base (s.socketAt c) f)
    (1*4) s.fieldBits s.lanes (s.tailStart base) w

variable (I:(⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩:SignedExtent).Input) (base:ℕ) (m:Memory w)
local notation "sheet"=>(e₀).installed I base m
local notation "cell" =>fun (z:(e₀).Socket)=>Fused.cell C R Z shelf small (home z.1) z.2
local notation "wide"=>(breadth D)*(breadth D)<2^b

include orders in
theorem phase_from_prior_heads (fits:(e₀).Fits I base w) (space:(e₀).roof base<2^w)
    (tech:(e₀).LocalRoom I base w) (addr:(e₀).ReturnRoom I base w)
    (size:wide) (degree:I.newDegree=A.degree) (emit:DescentResetWindowFields.Emission A native C marked)
    (real:DescentOrdinaryDonorRankDirectory.Reads R I.rankBanks m)
    (donors:(e₀).Donors I R cell base m) (v:(e₀).RouteDigits) (route:v.Earlier I m)
    (geo:RouteWitness A C R Z v I home)
    (ports:Mounted I.ports walks m groups M)
    (back:∀h p,m (I.reversePath.base+(DescentHaloWalkRAM.row h p).val)=(Rebase.value R .path h p:Word w))
    (tokens:∀x o h g,Packed.token (Packed.readToken P (v.forward x o h g))=v.forward x o h g)
    (mb:Fin blocks→Fin (P*O)→Fin H→Fin groups→Cell 1)
    (bits_:∀x j,Source (I.mark (x,j)) (mb x j) M m) (marks:∀z,(I.mark z).Fits w base)
    (known:∀x j h g u,home x h g=some u→∀e:Local C u,(R₀).address u e=j→((mb x j h g).val=1 ↔ marked e.val))
    (peerCode:(∀z f,Source ((e₀).rawField base z f) (fun h g=>Fused.columns (cell z h g) f) M sheet)→
      ∀x j,Source ((e₀).peerField I base (x,j)) (signedPeer (b:=b) A native S ready names C R symm Z home x j) M sheet)
    (digits:max (A.degree+1) (A.cap+1)<2^b) (codes:P*P*Q≤2^b) (tickets:K≤2^b):
    ((∀x axis j, let field:=(e₀).retainedRankField base x axis j
        field.Fits w ((e₀).roof base) ∧ Source field
          (fun h g=>(DescentOrdinarySignedRanks.result C census home (Stage.measured A native S ready) x axis j h g : Cell b))
          M ((e₀).phaseImage I base m)) ∧ (∀x j, let field:=(e₀).peerField I base (x,j)
        field.Fits w ((e₀).roof base) ∧ Source field
          (signedPeer (b:=b) A native S ready names C R symm Z home x j) M ((e₀).phaseImage I base m))) ∧
    ((e₀).phase I base w).Runs m ∧
    (∀x j,Reads ((e₀).page base x j) (fun h g=>DescentSignedCableCodec.encode (target x j h g)) M ((e₀).phaseImage I base m)) ∧
    (∀a,a<base ∨ (e₀).roof base≤a→(e₀).phaseImage I base m a=m a) ∧ CheapCode ((e₀).phase I base w).program:=by
  let controls:=(e₀).normalized_header I base m fits space R size real addr.oldRank addr.readRank addr.head addr.map
  have localRecords:=(e₀).local_records I base m R fits space cell size donors tech controls
  let data':=fun (z:(e₀).Socket) f h g=>Fused.columns (cell z h g) f
  have projection:=(e₀).projected_words I base m fits space data' localRecords addr.transpose addr.localBank
  let store:=fun l (z:(e₀).Socket) f h g=>((e₀).lifted I.hostPitch l h).elim 0 (fun u=>data' z f u g)
  have reverse:=fun x o=>(e₀).counted_back I base m fits space v R route x o (addr.donor x o).1 addr.reverse addr.reverseRows
    back (addr.reverseLookup x o) (tokens x o) (geo.back x o)
  obtain ⟨book,priorFit⟩:=addr.oldPort
  have remote:=(e₀).returned_records I base m fits space walks v route addr.donor reverse addr.dir₁ addr.dir₂ ports addr.reach
    book priorFit store projection addr.traverse addr.returnEnd
  have selected:∀c f,c.1.2.val=2→Source ((e₀).remoteWord I base c f) (routedValue C R Z shelf small home I v c f) M sheet:=by
    intro c f axis
    apply (e₀).remote_source I base m fits space R _ c f _ (remote c f axis) addr.cellRoot addr.cellEnd addr.oldRank.endpointsSize
      addr.offset addr.chunk (addr.value c f)
    intro h p
    have hi:(Ranks.id h p).val<I.rankBanks.endpoints.size:=(Ranks.id h p).isLt.trans_le addr.oldRank.endpointsSize
    exact (((e₀).installed_words I base m fits space).2 _ (by have:=addr.oldRank.endpoints.2.2;omega)).trans (real.visit h p)
  have oldFields:=fun x j=>localRecords (x,j)
  have flags:=signed_flags C marked R symm Z shelf small home I base m fits space mb bits_ marks known oldFields
  have paired (c:(e₀).Consumer) (f:Fin 11):Source ((e₀).operand I base c f) (fun h g=>Fused.columns (wanted C R symm Z shelf small orders home c h g) f) M sheet:=
    operand_gate C marked R symm Z shelf small orders home I base m v geo fits space c f (flags _ _).1
      (localRecords ((e₀).socketAt c) f) (selected c f) (addr.selectFit c f)
  have hdr:=signed_header_on A native S ready names C marked R symm Z shelf small orders home I base m fits space mb bits_ marks known oldFields degree digits (peerCode localRecords)
  have ranks := phase_issued_ranks A native S ready names C marked R symm Z shelf small orders home I base m degree fits space emit
    (fun x p j f => paired ((x,p),(j,0)) f) (fun x p j t f => paired ((x,p),(j,t.succ)) f)
    hdr (raw_header_lt A native S ready names C marked R symm Z orders home digits) digits codes tickets
  exact ⟨⟨ranks.1, fun x j => (e₀).retained_peer I base m fits space (x,j) _ (peerCode localRecords x j)⟩,ranks.2⟩

include orders in
theorem phase_from_prior (fits:(e₀).Fits I base w) (space:(e₀).roof base<2^w)
    (tech:(e₀).LocalRoom I base w) (addr:(e₀).ReturnRoom I base w)
    (size:wide) (degree:I.newDegree=A.degree) (emit:DescentResetWindowFields.Emission A native C marked)
    (real:DescentOrdinaryDonorRankDirectory.Reads R I.rankBanks m)
    (donors:(e₀).Donors I R cell base m) (v:(e₀).RouteDigits) (route:v.Earlier I m)
    (geo:RouteWitness A C R Z v I home)
    (ports:Mounted I.ports walks m groups M)
    (back:∀h p,m (I.reversePath.base+(DescentHaloWalkRAM.row h p).val)=(Rebase.value R .path h p:Word w))
    (tokens:∀x o h g,Packed.token (Packed.readToken P (v.forward x o h g))=v.forward x o h g)
    (mb:Fin blocks→Fin (P*O)→Fin H→Fin groups→Cell 1)
    (bits_:∀x j,Source (I.mark (x,j)) (mb x j) M m) (marks:∀z,(I.mark z).Fits w base)
    (known:∀x j h g u,home x h g=some u→∀e:Local C u,(R₀).address u e=j→((mb x j h g).val=1 ↔ marked e.val))
    (peerCode:(∀z f,Source ((e₀).rawField base z f) (fun h g=>Fused.columns (cell z h g) f) M sheet)→
      ∀x j,Source ((e₀).peerField I base (x,j)) (signedPeer (b:=b) A native S ready names C R symm Z home x j) M sheet)
    (digits:max (A.degree+1) (A.cap+1)<2^b) (codes:P*P*Q≤2^b) (tickets:K≤2^b):
    ((e₀).phase I base w).Runs m ∧
    (∀x j,Reads ((e₀).page base x j) (fun h g=>DescentSignedCableCodec.encode (target x j h g)) M ((e₀).phaseImage I base m)) ∧
    (∀a,a<base ∨ (e₀).roof base≤a→(e₀).phaseImage I base m a=m a) ∧ CheapCode ((e₀).phase I base w).program:=
  (phase_from_prior_heads A native S ready names C marked R symm Z shelf small orders home I base m
    fits space tech addr size degree emit real donors v route geo ports back tokens mb bits_ marks known peerCode digits codes tickets).2


end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
