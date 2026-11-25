import OAI.Hierarchy.DescentDatedSignedWords

namespace OAI
/-! Each of the eleven local record columns is derived in the actual
physical prefix from six prior donor digits and the original rank tables. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty.Chronology DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan
open DescentParallelBase DescentParallelBase.ParentFilter DescentHaloWalkRAM DescentOrdinaryDonorRankDirectory
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {w : ℕ}
variable (s:SignedExtent) (I:s.Input) (base:ℕ) (m:Memory w)
variable (R:Fin s.priorHosts→Fin s.degree→Option (Fin s.priorHosts))
local notation "P"=>s.reach
local notation "b"=>s.fieldBits
local notation "M"=>s.lanes
local notation "T"=>P*P
local notation "sheet"=>s.installed I base m
local notation "keyTable"=>DescentOrdinaryDonorSources.PathKeys.table (s.keyStart base) s.degree b b M
local notation "rchart" => fun (i : Fin 5) => DescentPackedChildNeighbor.SIMD.ROM.layout (s.lookupStart base) T b b M (Nat.clog 2 s.slab)
  (subbank (s.viewBase base) s.viewRows (fieldNumber (DescentOrdinaryDonorSources.tag i)))
local notation "rq" => fun z i => (keyTable).read (I.path z) (I.endpoints z (DescentOrdinaryDonorSources.PathKeys.side i))
local notation "pt"=>DescentOrdinaryDonorSources.ROM.table (s.peerStart base) s.lowSites b M
variable (ok:s.Fits I base w) (space:s.roof base<2^w)
variable (raw:s.Socket→Fin s.hosts→Fin s.groups→Option (Fused.Raw R s.lowSites s.tickets s.cap s.fieldBits))
variable (size:s.reach*s.reach<2^s.fieldBits)

def rack (pitch:ℕ) (h:Fin s.hosts):Option (Fin s.priorHosts):=
  if yes:0<pitch ∧ h.val/pitch < s.priorHosts then some ⟨_,yes.2⟩ else none
def directoryAt (pitch:ℕ) (f:DescentOrdinaryDonorRankDirectory.Field) (h:Fin s.hosts) (j:Fin T):Cell b:=
  (s.rack pitch h).elim 0 (fun u=>directory R size f u j)

/-- The donor snippets are earlier words, before the rank and route scans.
Every coordinate in these equations is either a prior port or the physical
receiver that selected it. -/
structure Donors (s:SignedExtent) (I:s.Input) (R:Fin s.priorHosts→Fin s.degree→Option (Fin s.priorHosts))
    (raw:s.Socket→Fin s.hosts→Fin s.groups→Option (Fused.Raw R s.lowSites s.tickets s.cap s.fieldBits)) (base:ℕ) (m:Memory w):Prop where
  pathValue:∀z,Source (I.path z) (fun h g=>(DescentOrdinaryDonorSources.PathKeys.issuedPath (raw z h g):Cell s.fieldBits)) s.lanes m
  endpointValue:∀z t,Source (I.endpoints z t) (fun h g=>(DescentOrdinaryDonorSources.PathKeys.selectedPath (raw z h g) t:Cell s.fieldBits)) s.lanes m
  material:∀z i,Source (I.donor z i) (fun h g=>DescentOrdinaryDonorSources.material R (raw z h g) i) s.lanes m
  pathEarly:∀z,(I.path z).Fits w base
  endEarly:∀z t,(I.endpoints z t).Fits w base
  donorEarly:∀z i,(I.donor z i).Fits w base
  origin:∀z h g u,raw z h g=some u→s.rack I.hostPitch h=some u.receiver.1
  selected:∀z h g u,raw z h g=some u→Gather.select (Gather.reaching R) u.receiver.1 u.path=some u.host

theorem lookup_book {w':ℕ} (mem:Memory w') (wide:∀j:Fin s.lookupWords,
      mem (s.lookupStart base+j.val)=(DescentPackedChildNeighbor.SIMD.ROM.numbers T b b M s.hosts s.groups j.val:Word w'))
    (i:Fin 5) (dirs:Fin s.hosts→Fin T→Cell b)
    (read:∀h j,mem ((rchart i).header.base+(h.val*T+j.val))=((dirs h j).val:Word w')):
    DescentPackedChildNeighbor.SIMD.Stored (rchart i) s.hosts s.groups b b M dirs mem:=by
  let read_ (u:DescentPackedChildNeighbor.SIMD.ROM.Index T b b M s.hosts s.groups):
      mem (DescentPackedChildNeighbor.SIMD.ROM.address (s.lookupStart base) u)=(DescentPackedChildNeighbor.SIMD.ROM.word u:Word w'):=by
    let t:=DescentPackedChildNeighbor.SIMD.ROM.index T b b M s.hosts s.groups u
    rw [DescentPackedChildNeighbor.SIMD.ROM.address_eq]
    exact (wide ⟨t.val,t.isLt.trans_le (Nat.le_add_right ..)⟩).trans (by
      simp [t,DescentPackedChildNeighbor.SIMD.ROM.numbers,(DescentPackedChildNeighbor.SIMD.ROM.index T b b M s.hosts s.groups u).isLt])
  constructor
  · exact read
  · intro p;exact (read_ (.inr (.inr (.inr (.inr (row s.hosts s.groups M p)))))).trans (by simp [DescentPackedChildNeighbor.SIMD.ROM.word])
  · intro u;exact read_ (.inl u)
  · intro j u;exact read_ (.inr (.inl (j,u)))
  · constructor
    · intro u;exact read_ (.inr (.inr (.inl u)))
    · intro u;exact read_ (.inr (.inr (.inr (.inl u))))

structure LocalRoom (s:SignedExtent) (I:s.Input) (base w:ℕ):Prop where
  path:∀z i,DescentPackedZip.Fits (DescentOrdinaryDonorSources.PathKeys.table (s.keyStart base) s.degree s.fieldBits s.fieldBits s.lanes)
    (I.path z) (I.endpoints z (DescentOrdinaryDonorSources.PathKeys.side i)) s.fieldBits s.fieldBits s.lanes (s.tailStart base) w
  lookup:∀z i,DescentPackedChildNeighbor.SIMD.Room (DescentPackedChildNeighbor.SIMD.ROM.layout (s.lookupStart base)
    (s.reach*s.reach) s.fieldBits s.fieldBits s.lanes (Nat.clog 2 s.slab) (subbank (s.viewBase base) s.viewRows (fieldNumber (DescentOrdinaryDonorSources.tag i))))
    ((DescentOrdinaryDonorSources.PathKeys.table (s.keyStart base) s.degree s.fieldBits s.fieldBits s.lanes).read (I.path z)
      (I.endpoints z (DescentOrdinaryDonorSources.PathKeys.side i))) s.hosts s.groups s.fieldBits s.fieldBits s.lanes w (s.tailStart base)
  field:∀z i j,DescentPackedZip.Fits (DescentOrdinaryDonorSources.ROM.table (s.peerStart base) s.lowSites s.fieldBits s.lanes)
    (.lookup (s.rankPage base z i) .row) (I.donor z j) s.fieldBits s.fieldBits s.lanes (s.tailStart base) w
  slab:2^Nat.clog 2 s.slab<2^w

include ok space in
theorem local_records (data:s.Donors I R raw base m) (tech:s.LocalRoom I base w)
    (heads:∀f (h:Fin s.hosts) (j:Fin T),sheet ((subbank (s.viewBase base) s.viewRows (fieldNumber f)).base+(h.val*T+j.val))=
      ((s.directoryAt R size I.hostPitch f h j).val:Word w)):
    ∀z f,Source (s.rawField base z f) (fun h g=>Fused.columns (raw z h g) f) M sheet:=by
  let t:=s.tailStart base
  have same:∀a<base,sheet a=m a:=(s.installed_words I base m ok space).2
  have Ppos:0<P:=by dsimp [reach,breadth];positivity
  have Plim:P<2^b:=(Nat.le_mul_of_pos_right P Ppos).trans_lt size
  have pathBound (z h g):DescentOrdinaryDonorSources.PathKeys.issuedPath (raw z h g)<2^b:=by
    cases now:raw z h g with
    | none=>exact Nat.two_pow_pos _
    | some r=>exact r.path.isLt.trans Plim
  have endBound (z t h g):DescentOrdinaryDonorSources.PathKeys.selectedPath (raw z h g) t<2^b:=by
    cases now:raw z h g with
    | none=>exact Nat.two_pow_pos _
    | some r=>exact (Nat.succ_le_of_lt (if t then r.parent.dst.path else r.parent.src.path).isLt).trans_lt Plim
  have key (z i):Source (rq z i) (fun h g=>(DescentOrdinaryDonorSources.key R (raw z h g) i:Cell b)) M sheet:=by
    apply DescentOrdinaryDonorSources.PathKeys.packed R (raw z) i _ _ (I.path z) (I.endpoints z) _ t sheet size
    · intro h g;exact Fin.val_cast_of_lt (pathBound z h g)
    · intro side h g;exact Fin.val_cast_of_lt (endBound z side h g)
    · exact tech.path z i
    · exact s.static_path I base m ok space
    · exact SignedPrefix.from_prior _ _ _ _ same (data.pathEarly z) (data.pathValue z)
    · intro side;exact SignedPrefix.from_prior _ _ _ _ same (data.endEarly z side) (data.endpointValue z side)
  have geometry (z i):Source (.lookup (s.rankPage base z i) .row) (fun h g=>DescentOrdinaryDonorSources.geometry R size (raw z h g) i) M sheet:=by
    let tag:=DescentOrdinaryDonorSources.tag i
    let vals:=s.directoryAt R size I.hostPitch tag
    let qs:=fun h g=>(DescentOrdinaryDonorSources.key R (raw z h g) i:Cell b)
    have step:=DescentPackedChildNeighbor.SIMD.measures (rchart i) (rq z i) t (tech.lookup z i) vals sheet
      (s.lookup_book base sheet (s.funded_lookup I base m ok space) i vals (heads tag)) qs (key z i) (List.finRange T)
    have point (h g):DescentPackedChildNeighbor.SIMD.lookup (vals h) (qs h g) (List.finRange T)=
        DescentOrdinaryDonorSources.geometry R size (raw z h g) i:=by
      cases hit:raw z h g with
      | none=>
        have zero:qs h g=0:=by simp [qs,hit,DescentOrdinaryDonorSources.key]
        rw [zero]
        apply DescentPackedChildNeighbor.SIMD.lookup_missing
        intro j same;simp at same
      | some u=>
        have orig:=data.origin z h g u hit
        have correct:DescentOrdinaryDonorSources.Correct R u.receiver.1 (some u):=by
          intro a eqn;obtain rfl:=Option.some.inj eqn;exact ⟨rfl,data.selected z h g u hit⟩
        have code:(DescentOrdinaryDonorSources.key R (some u) i)<2^b:=by
          change (PairRanks.pair u.path _).val+1<_;exact (Nat.succ_le_of_lt (PairRanks.pair u.path _).isLt).trans_lt size
        have dirEq : vals h = directory R size (DescentOrdinaryDonorSources.tag i) u.receiver.1 := by
          funext j
          simp only [vals,directoryAt,orig,Option.elim_some,tag]
        rw [dirEq]
        dsimp only [qs]
        rw [hit]
        exact DescentOrdinaryDonorSources.looked_up R size (some u) u.receiver.1 i correct (DescentOrdinaryDonorSources.key R (some u) i:Cell b) (Fin.val_cast_of_lt code)
    refine SignedPrefix.column_source sheet (s.rankPage base z i) _ ?_ (Nat.le_pow_clog (by decide) s.slab) tech.slab
    intro row
    exact (s.funded_rank I base m ok space z i (DescentSIMDLookup.row s.hosts s.groups M row)).trans (by simpa only [rankField,point] using step row)
  intro z f
  have source:=DescentOrdinaryDonorSources.source R pt (I.donor z) (fun i=>.lookup (s.rankPage base z i) .row) size sheet t (raw z)
    (data.selected z) (fun i=>SignedPrefix.from_prior _ _ _ _ same (data.donorEarly z i) (data.material z i))
    (geometry z) (tech.field z) (s.static_peer I base m ok space) f
  refine SignedPrefix.column_source sheet (subbank (s.localStart base) s.slab (s.localId z f)) _ ?_ (Nat.le_pow_clog (by decide) s.slab) tech.slab
  intro row;exact (s.funded_donor I base m ok space z f (DescentSIMDLookup.row s.hosts s.groups M row)).trans (source row)

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
