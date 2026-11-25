import OAI.Hierarchy.DescentDatedSignedWords
import OAI.Hierarchy.DescentOrdinaryCompactPeerRank

namespace OAI
/-! # The compact host peer directory measured by the actual shared prefix -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSharedCableNames DescentHaloWalkRAM DescentPackedChildNeighbor DescentPackedZip DescentSIMDLookup
open DescentDyadicSpan DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}
variable (s : SignedExtent) (I : s.Input) (base : ℕ) (m : Memory w)
local notation "sheet" => s.installed I base m
local notation "L₀" => s.reach*s.reach
local notation "head" => s.peerHeadBase base
local notation "pre" => DescentOrdinaryCompactPeer.ROM.layout head s.priorHosts s.hosts (L₀) s.lowSites I.priorRanks I.priorEnds I.newNeighbors
local notation "racks" => DescentOrdinaryCompactPeer.ROM.rack s.priorHosts I.hostPitch
local notation "chart" => SIMD.ROM.layout (s.peerROMBase base) s.peerKinds s.peerBits s.fieldBits s.lanes (Nat.clog 2 s.slab) (s.peerDirectory base)
variable (ok : s.Fits I base w) (space : s.roof base<2^w)

/-- Genuine old data windows, with their normalized counting bounds and the
public successor and raw low slot range. The compact dictionary is generated. -/
structure PeerInputs (s : SignedExtent) (I : s.Input) (base w : ℕ) where
  ranks : I.priorRanks.Fits w base ∧ s.priorHosts*(s.reach*s.reach)≤I.priorRanks.size
  ends : I.priorEnds.Fits w base ∧ s.priorHosts*(s.reach*s.reach)≤I.priorEnds.size
  neighbors : I.newNeighbors.Fits w base ∧ s.hosts*I.newDegree≤I.newNeighbors.size
  prior : s.priorHosts<2^w
  hosts : s.hosts<2^w
  kinds : s.reach*s.reach<2^w
  targets : ∀v : Fin s.priorHosts,∀g : Fin s.lowSites,v.val*I.hostPitch+g.val<2^w
  width : 0<w

private theorem first_head_le : base≤head :=by
  dsimp only [peerHeadBase,peerROMBase,peerKeyBase,gateStart,metaStart,rawStart,
    shapesStart,returnedStart,routeStart,backBase,forwardBase,projectedStart,
    localStart,peerStart,ranksStart,lookupStart,keyStart,viewBase,mapOffset,mapChunk,mapHost,
    mapTranspose,mapBase,DescentOrdinarySignedMeta.stop,DescentOrdinarySignedMeta.RawControls.stop,
    DescentOrdinaryDonorSources.ROM.endAddress,DescentOrdinaryDonorSources.PathKeys.endAddress]
  simp only [Nat.add_assoc]
  exact Nat.le_add_right ..

include ok space in
theorem compact_peer_header (good : s.PeerInputs I base w)
    (ends : Fin s.priorHosts→Fin (L₀)→Option (Fin s.priorHosts))
    (roster : Fin s.hosts→Fin I.newDegree→Option (Fin s.hosts)) (wide : I.newDegree<2^s.fieldBits)
    (ranks : ∀v j,m (I.priorRanks.base+(v.val*(L₀)+j.val))=(rank ends v j:Word w))
    (endpoints : ∀v j,m (I.priorEnds.base+(v.val*(L₀)+j.val))=(number (ends v j):Word w))
    (neighbors : ∀v j,m (I.newNeighbors.base+(v.val*I.newDegree+j.val))=(number (roster v j):Word w))
    (h : Fin s.hosts) (j : Fin s.peerKinds) :
    sheet ((s.peerDirectory base).base+(h.val*s.peerKinds+j.val))=
      ((DescentOrdinaryCompactPeer.directory ends roster I.hostPitch racks wide h j).val:Word w) := by
  have saved := (s.installed_words I base m ok space).2
  have top := s.prefix_room base
  rw [s.calibrated base] at top
  have last : s.peerHeadOut base+s.peerHeadRows<2^w :=
    (Nat.add_le_add_left (span_ge s.peerHeadRows) _).trans_lt (top.trans_lt space)
  have adj : DescentOrdinaryCompactPeer.ROM.output head s.priorHosts s.hosts (L₀) s.lowSites=s.peerHeadOut base := by
    simp only [DescentOrdinaryCompactPeer.ROM.output,peerHeadOut,peerHeadWords,peerHeadRows,peerKinds,span,Nat.add_assoc]
  have start := first_head_le s base
  have move (B : Bank) (fit : B.Fits w base) : B.Fits w head := ⟨fit.1,fit.2.1,fit.2.2.trans start⟩
  have fit := (DescentOrdinaryCompactPeer.ROM.arranged I.priorRanks I.priorEnds I.newNeighbors head I.hostPitch
    ⟨move _ good.ranks.1,good.ranks.2⟩ ⟨move _ good.ends.1,good.ends.2⟩ ⟨move _ good.neighbors.1,good.neighbors.2⟩
    good.prior good.hosts good.kinds good.targets good.width (adj ▸ last)).2
  have range_ {n k : ℕ} (i : Fin n) (r : Fin k) : i.val*k+r.val<n*k :=
    (Nat.add_lt_add_left r.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ i.isLt)
  have rd (B : Bank) {n k : ℕ} (fit : B.Fits w base ∧ n*k≤B.size) (i : Fin n) (r : Fin k) :
      sheet (B.base+(i.val*k+r.val))=m (B.base+(i.val*k+r.val)) :=
    saved _ ((Nat.add_lt_add_left ((range_ i r).trans_le fit.2) _).trans_le fit.1.2.2)
  have tables := DescentOrdinaryCompactPeer.ROM.mounted_on I.priorRanks I.priorEnds I.newNeighbors head I.hostPitch sheet
    ends roster (fun i=>s.funded_peer_head I base m ok space ⟨i.val,i.isLt.trans_le (by unfold peerHeadWords;omega)⟩)
    (fun v i=>(rd _ good.ranks v i).trans (ranks v i)) (fun v i=>(rd _ good.ends v i).trans (endpoints v i))
    (fun v i=>(rd _ good.neighbors v i).trans (neighbors v i))
  have scanned (q : DescentOrdinaryCompactPeer.Key s.hosts (L₀) s.lowSites) :=
    (s.funded_peer_value I base m ok space (DescentOrdinaryCompactPeer.index s.hosts (L₀) s.lowSites q)).trans
      (DescentOrdinaryCompactPeer.eval _ _ I.hostPitch _ racks fit ends roster sheet tables q)
  simpa only [peerDirectory,peerKinds,subbank,Nat.zero_mul,Nat.add_zero] using DescentOrdinaryCompactPeer.header_words ends roster
    I.hostPitch racks wide sheet (s.peerHeadOut base) (fun q => (scanned q).trans (by cases racks q.1 <;> rfl)) h j

include ok space in
theorem compact_peer_degree {D : ℕ} (degree : I.newDegree=D) (good : s.PeerInputs I base w)
    (ends : Fin s.priorHosts→Fin (L₀)→Option (Fin s.priorHosts))
    (roster : Fin s.hosts→Fin D→Option (Fin s.hosts)) (wide : D<2^s.fieldBits)
    (ranks : ∀v j,m (I.priorRanks.base+(v.val*(L₀)+j.val))=(rank ends v j:Word w))
    (endpoints : ∀v j,m (I.priorEnds.base+(v.val*(L₀)+j.val))=(number (ends v j):Word w))
    (neighbors : ∀v j,m (I.newNeighbors.base+(v.val*D+j.val))=(number (roster v j):Word w))
    (h : Fin s.hosts) (j : Fin s.peerKinds) :
    sheet ((s.peerDirectory base).base+(h.val*s.peerKinds+j.val))=
      ((DescentOrdinaryCompactPeer.directory ends roster I.hostPitch racks wide h j).val:Word w) := by
  subst D
  exact s.compact_peer_header I base m ok space good ends roster wide ranks endpoints neighbors h j

include ok space in
theorem peer_lookup_tables (values : Fin s.hosts→Fin s.peerKinds→Cell s.fieldBits)
    (header : ∀h j,sheet ((s.peerDirectory base).base+(h.val*s.peerKinds+j.val))=((values h j).val:Word w)) :
    SIMD.Stored chart s.hosts s.groups s.peerBits s.fieldBits s.lanes values sheet := by
  have word (i : SIMD.ROM.Index s.peerKinds s.peerBits s.fieldBits s.lanes s.hosts s.groups) :
      sheet (SIMD.ROM.address (s.peerROMBase base) i)=(SIMD.ROM.word i:Word w) := by
    let ix:=SIMD.ROM.index s.peerKinds s.peerBits s.fieldBits s.lanes s.hosts s.groups i
    have lt : ix.val<s.peerLookupWords := ix.isLt.trans_le (Nat.le_add_right ..)
    rw [SIMD.ROM.address_eq]
    refine (s.funded_peer_lookup I base m ok space ⟨ix.val,lt⟩).trans ?_
    unfold SIMD.ROM.numbers
    rw [dite_eq_left ix.isLt]
    exact congrArg (fun z => (SIMD.ROM.word z : Word w)) ((SIMD.ROM.index s.peerKinds s.peerBits s.fieldBits s.lanes s.hosts s.groups).symm_apply_apply i)
  refine ⟨header,?_,?_,?_,?_,?_⟩
  · intro p;exact (word (.inr (.inr (.inr (.inr (row s.hosts s.groups s.lanes p)))))).trans (by simp [SIMD.ROM.word])
  · intro i;exact word (.inl i)
  · intro j i;exact word (.inr (.inl (j,i)))
  · intro i;exact word (.inr (.inr (.inl i)))
  · intro i;exact word (.inr (.inr (.inr (.inl i))))

private theorem peer_slab_lt (space : s.roof base<2^w) (z : Socket s) : s.tailStart base+s.slab<2^w := by
  let start:=DescentOrdinarySignedParents.ROM.endAddress (s.tailStart base) s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes
  have before : s.tailStart base≤ start := by dsimp [start,DescentOrdinarySignedParents.ROM.endAddress];omega
  have tailBound:= (DescentOrdinarySignedAll.ordered (X:=s.blocks) (K:=s.candidates) (b:=s.fieldBits)
    (M:=s.lanes) (H:=s.hosts) (gg:=s.groups) (cap:=s.cap) start).2
  have count : 1≤(s.blocks*3)*s.candidates :=
    Nat.mul_pos (Nat.mul_pos (Nat.zero_lt_of_lt z.1.isLt) (by decide)) (Nat.zero_lt_of_lt z.2.isLt)
  have slots:=Nat.mul_le_mul_right (span s.slab) count
  rw [Nat.one_mul] at slots
  have a := span_ge s.slab
  have left : s.tailStart base+s.slab≤DescentOrdinarySignedAll.Tail start s.blocks s.candidates s.fieldBits s.lanes s.hosts s.groups := by
    change _≤ start+_+((s.blocks*3)*s.candidates)*span s.slab
    omega
  exact (left.trans tailBound).trans_lt (by simpa only [←s.calibrated base,phaseEnd,start] using space)

include space in
theorem peer_chart_room_of_gathered (z : Socket s)
    (gatherFit : (s.gathered base z).Fits w (s.tailStart base)) :
    SIMD.Room chart (DescentOrdinarySocketPeer.query (s.peerKeyBase base) s.fieldBits s.lanes (s.gathered base z))
      s.hosts s.groups s.peerBits s.fieldBits s.lanes w (s.tailStart base) := by
  let a:=s.peerBits
  let b:=s.fieldBits
  let n:=s.slab
  let head₀:=s.peerROMBase base
  let hi:=s.tailStart base
  let sh:=2^(a*s.lanes)
  let tab:=2^(a*s.lanes+b)
  let left:=2^(b*s.lanes)
  let join:=2^((b+b)*s.lanes)
  have last : hi+s.slab<2^w := peer_slab_lt s base space z
  have full : head₀+sh+s.peerKinds*tab+left+join+span n≤hi := by
    have enough:=span_ge n
    dsimp only [hi,head₀,sh,tab,left,join,a,b,n,tailStart,peerHeadOut,peerHeadBase,peerLookupWords,SIMD.ROM.cells]
    change _+_+_+_+_+span s.slab≤_+(_+(_+(_+(_+s.slab)))+(span s.slab-s.slab))+_+_
    omega
  have toJoin : head₀+sh+s.peerKinds*tab+left+join≤hi := (Nat.le_add_right ..).trans full
  have toLeft : head₀+sh+s.peerKinds*tab+left≤hi := (Nat.le_add_right ..).trans toJoin
  have toTable : head₀+sh+s.peerKinds*tab≤hi := (Nat.le_add_right ..).trans toLeft
  have toShape : head₀+sh≤hi := (Nat.le_add_right ..).trans toTable
  have fit (B : Bank) (ext : B.base+B.size≤hi) : B.Fits w hi :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (ext.trans_lt ((Nat.le_add_right ..).trans_lt last)),ext⟩
  have key : (Bank.mk (s.peerKeyBase base) (DescentOrdinarySocketPeer.bits b s.lanes)).Fits w hi :=
    fit _ ((Nat.le_add_right ..).trans toShape)
  have old : (s.gathered base z).Fits w hi := gatherFit
  refine ⟨⟨key,old⟩,fit _ ?_,fit _ ?_,fit _ ?_,?_,fit _ ?_,fit _ ?_,span_ge s.peerHeadRows,span_ge s.slab,
    rfl,fun _=>rfl,rfl,rfl,last⟩
  · change s.peerHeadOut base+0*span s.peerHeadRows+span s.peerHeadRows≤ s.tailStart base
    simp [tailStart]
  · change head₀+sh+s.peerKinds*tab+left+join+span n≤hi
    exact full
  · exact toShape
  · intro j
    apply fit
    have h:=Nat.mul_le_mul_right tab j.isLt
    rw [Nat.succ_mul] at h
    change head₀+sh+j.val*tab+tab≤hi
    rw [Nat.add_assoc]
    exact (Nat.add_le_add_left h _).trans toTable
  · exact toLeft
  · exact toJoin

include ok space in
theorem peer_chart_room (z : Socket s) :
    SIMD.Room chart (DescentOrdinarySocketPeer.query (s.peerKeyBase base) s.fieldBits s.lanes (s.gathered base z))
      s.hosts s.groups s.peerBits s.fieldBits s.lanes w (s.tailStart base) :=
  s.peer_chart_room_of_gathered base space z (ok.header z.1 z.2).2.2.2.2.2.2

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
