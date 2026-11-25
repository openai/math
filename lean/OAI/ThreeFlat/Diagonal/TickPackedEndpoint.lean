import OAI.ThreeFlat.Diagonal.TickScheduledTeam
import OAI.ThreeFlat.Diagonal.NavigationLeafPairs
import OAI.ThreeFlat.RAM.TickSelectedPins

namespace OAI
/-! # From a seed's interleaved H endpoint to its physical group pair pin -/

namespace ThreeFlat.Diagonal.TickPhaseModel.Buckets
open HistoryContraction TickChronology TickAuxiliary RAM ApproximateImage
open scoped Classical
noncomputable section

def pairIndex {n : ℕ} (i : Fin (2*n)) : Fin n := ⟨i.val/2,by have:=i.isLt; omega⟩
def pairSide {n : ℕ} (i : Fin (2*n)) : Bool := decide (i.val%2≠0)

variable {period width a : ℕ} (c : Clock) (hc : c.chunks=2*(period*width))
local notation "L" => period*width*a+period*width*a
local notation "O" => AlignedChunks.order c hc

def endpointPoint (i : Fin L) : Fin c.chunks×Fin a :=
  finProdFinEquiv.symm (i.cast (by rw [hc];ring))

theorem endpointPoint_address (i : Fin L) : ClippedPairBuckets.address (endpointPoint c hc i)=i.val := by
  let z:=endpointPoint c hc i
  have eq : (finProdFinEquiv z).val=i.val :=
    congrArg Fin.val (finProdFinEquiv.apply_symm_apply (i.cast (by rw [hc];ring)))
  change z.1.val*a+z.2.val=i.val
  change z.2.val+a*z.1.val=i.val at eq
  rw [Nat.mul_comm a z.1.val] at eq
  omega

theorem endpointPoint_read (i : Fin L) (x : Ext c a) :
    PhysicalPinsInput.externalBits (TickPhysicalOrder.unpack O x) i=
      x (endpointPoint c hc i).1 (endpointPoint c hc i).2 := by
  obtain ⟨k,j,atI,point⟩:=physicalBit_address c hc i
  let z:=endpointPoint c hc i
  have addr:=endpointPoint_address c hc i
  have same : (k,j)=z := by
    apply finProdFinEquiv.injective
    apply Fin.ext
    change j.val+a*k.val=z.2.val+a*z.1.val
    change k.val*a+j.val=i.val at atI
    change z.1.val*a+z.2.val=i.val at addr
    rw [Nat.mul_comm a k.val,Nat.mul_comm a z.1.val]
    omega
  change _=x z.1 z.2
  rw [←same]
  exact point x

variable {F : Type*} [CommSemiring F] {S : Shape} {P : Plan F S} {bits : P.History→ℕ} {lanes span cap : ℕ}
variable (T : Buckets P bits c a lanes span) (v : Plan.Terminal P bits) (g : Fin c.groups)
variable (fit : 1+cap+2*T.length v g.val≤a) (q nt ns np : ℕ)

/-- Total seed-pin map. The selected owner uses the unique packed ordinal
emitted by the physical scan. Unselected original endpoints use the marker. -/
def packEndpoint (i : Fin (2*L)) : Fin (pinCount q nt ns np a) :=
  let z : Fin c.chunks × Fin a := endpointPoint c hc (pairIndex i)
  if live : T.code v g.val z.1 z.2≠0 then
    TickSelectedPins.pair (a:=a) (cap:=cap) (n:=T.length v g.val) fit q nt ns np
      (pairSide i) (T.packed v g ⟨z,live⟩)
  else
    TickSelectedPins.incoming (a:=a) q nt ns np ⟨0,by
      calc
        0 < 1 := Nat.zero_lt_one
        _ ≤ 1+cap := Nat.le_add_right _ _
        _ ≤ 1+cap+2*T.length v g.val := Nat.le_add_right _ _
        _ ≤ a := fit⟩

theorem packEndpoint_owned (i : Fin (2*L)) (home : T.owner v (endpointPoint c hc (pairIndex i))=g) :
    packEndpoint c hc T v g fit q nt ns np i =
      TickSelectedPins.pair fit q nt ns np (pairSide i)
        (T.packed v g ⟨endpointPoint c hc (pairIndex i),(T.hit v g (endpointPoint c hc (pairIndex i))).mpr home⟩) := by
  simp only [packEndpoint,dite_eq_left ((T.hit v g (endpointPoint c hc (pairIndex i))).mpr home)]

/-- The Boolean lookup agrees at the true absolute H endpoint, using the
original side parity and the current group proposal in incoming AUX. -/
theorem packEndpoint_read (i : Fin (2*L)) (home : T.owner v (endpointPoint c hc (pairIndex i))=g)
    (D : Fin q→Bool) (team : Fin nt→Bool) (step : Fin ns→Bool) (params : Fin np→Bool)
    (oa na oc nc : Fin a→Bool) :
    let reg:=project (TickPairHeader.layout cap (T.length v g.val) fit) oa
    let get:=fun p=>PhysicalPinsInput.externalBits (TickPhysicalOrder.unpack O (T.extend v g p))
    fields D team step params oa na oc nc (packEndpoint c hc T v g fit q nt ns np i)=
      TraceBitHeader.endpointPin (get (oldPair fit reg.pairs)) (get (newPair fit reg.pairs)) i := by
  intro reg get
  let z:=endpointPoint c hc (pairIndex i)
  have live : T.code v g.val z.1 z.2≠0 := (T.hit v g _).mpr home
  have read (p : Fin (T.length v g.val)→Bool) : get p (pairIndex i)=p (T.packed v g ⟨z,live⟩) := by
    change PhysicalPinsInput.externalBits (TickPhysicalOrder.unpack O (T.extend v g p)) (pairIndex i)=_
    rw [endpointPoint_read c hc]
    change (if h:T.code v g.val z.1 z.2≠0 then p (T.packed v g ⟨(z.1,z.2),h⟩) else false)=_
    rw [dite_eq_left live]
  rw [packEndpoint_owned c hc T v g fit q nt ns np i home,TickSelectedPins.pair_read]
  change (if pairSide i then newPair fit reg.pairs _ else oldPair fit reg.pairs _)=
    (if i.val%2=0 then get (oldPair fit reg.pairs) (pairIndex i) else get (newPair fit reg.pairs) (pairIndex i))
  by_cases zero : i.val%2=0 <;> simp [pairSide,zero,read] <;> rfl

/-- The ordinal and bus side read by the real interval cursor as a raw
memory address. Its code word is the one-plus packed ordinal. -/
theorem packEndpoint_address {age teams hidden : ℕ} (i : Fin (2*L))
    (home : T.owner v (endpointPoint c hc (pairIndex i))=g) :
    let z:=endpointPoint c hc (pairIndex i)
    BitLayout.sourceAddress (n:=hidden) (.pin (packEndpoint c hc T v g fit q nt ns np i))=
      (TickPhysicalABI.mounted age a teams cap q nt ns np).oldAux+1+cap+
        (if pairSide i then T.length v g.val else 0)+(T.code v g.val z.1 z.2-1) := by
  intro z
  rw [packEndpoint_owned c hc T v g fit q nt ns np i home,
    TickSelectedPins.pair_address (u:=age) (teams:=teams) (hidden:=hidden),T.addr]


end
end ThreeFlat.Diagonal.TickPhaseModel.Buckets

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor TraceSuffix HistoryContraction RAM TickPhaseModel TickChronology
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] [Fintype F] {w p r n S base f q low : ℕ}
    (M : Machine w p r n) (t : NativeTrace.Fits M S base ((q+1)+low) f) (hF : Fintype.card F≤2^w)
    (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
local notation "A" => B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
  (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells
variable {period width a : ℕ} (c : Clock) (hc : c.chunks=2*(period*width))
local notation "L" => period*width*a+period*width*a
variable (extent : 2*(period*width*a+period*width*a)≤S)
local notation "U" => (seedWordLayout M t hF st B hk extent).ports
variable (P : Plan F (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells).shape)
    {bits : P.History→ℕ} (T : Buckets P bits c a (2^(q+1)) (2^low))

set_option Elab.async false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem seedEndpoint_owner (leaves : ∀ lane : Lane (q+1),T.site (finFunctionFinEquiv lane)=(0,lane))
    (v : Plan.Terminal P bits) (g : Fin c.groups) (u : (A).Site) (j : Fin ((U).ext u))
    (own : T.group v.1 (P.destination v.1 u)=g) :
    T.owner v (Buckets.endpointPoint c hc (Buckets.pairIndex (seedEndpoint L low u j)))=g := by
  let z:=Buckets.endpointPoint c hc (Buckets.pairIndex (seedEndpoint L low u j))
  obtain ⟨first,index⟩:=seedEndpoint_lane (q:=q) (T:=L) (low:=low) u j
  have atI:=Buckets.endpointPoint_address c hc (Buckets.pairIndex (seedEndpoint L low u j))
  have loc : ClippedPairBuckets.lane (2^low) T.positive T.fit z=finFunctionFinEquiv u.2 := by
    apply Fin.ext
    change ClippedPairBuckets.address z/2^low=(finFunctionFinEquiv u.2).val
    exact (congrArg (·/2^low) atI).trans index
  change T.group v.1 (P.destination v.1 (T.site (ClippedPairBuckets.lane _ _ _ z)))=g
  have id : ((0, u.2) : (A).Site) = u := Prod.ext first.symm rfl
  have atSite : T.site (ClippedPairBuckets.lane _ _ _ z) = u :=
    ((congrArg T.site loc).trans (leaves u.2)).trans id
  exact (congrArg (fun s : (A).Site => T.group v.1 (P.destination v.1 s)) atSite).trans own

set_option Elab.async false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
/-- Seed pin read in the actual paired H word layout, with the public fixed
fields of a complete physical tick input and its own group's incoming AUX. -/
theorem seedPacked_read (leaves : ∀ lane : Lane (q+1),T.site (finFunctionFinEquiv lane)=(0,lane))
    (v : Plan.Terminal P bits) (g : Fin c.groups) (u : (A).Site) (j : Fin ((U).ext u))
    (own : T.group v.1 (P.destination v.1 u)=g)
    {cap advice nt ns np : ℕ} (room : 1+cap+2*T.length v g.val≤a)
    (D : Fin advice→Bool) (team : Fin nt→Bool) (step : Fin ns→Bool) (params : Fin np→Bool)
    (oa na oc nc : Fin a→Bool) :
    let reg:=TickAuxiliary.project (TickPairHeader.layout cap (T.length v g.val) room) oa
    let get:=fun pars=>PhysicalPinsInput.externalBits (TickPhysicalOrder.unpack (AlignedChunks.order c hc) (T.extend v g pars))
    ApproximateImage.fields D team step params oa na oc nc
      (Buckets.packEndpoint c hc T v g room advice nt ns np (seedEndpoint L low u j))=
      (U).pin u (endpointPin (get (TickAuxiliary.oldPair room reg.pairs)) (get (TickAuxiliary.newPair room reg.pairs))) j := by
  exact Buckets.packEndpoint_read c hc T v g room advice nt ns np (seedEndpoint L low u j)
    (seedEndpoint_owner M t hF st B hk c hc extent P T leaves v g u j own) D team step params oa na oc nc


end
end ThreeFlat.Diagonal.TraceBitHeader

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open HistoryContraction TickPhaseModel TickChronology TickGroupIntervals
open scoped Classical
noncomputable section

/-- The complete published S5 row at this ordinal, including its group-local
prefix, comes from the corresponding original clipped lane. -/
theorem packed_lane_row (nav : RootArchive) (groups : Fin nav.initialLanes→Fin nav.groups) (ix : Fin nav.initialLanes) :
    nav.packedRow groups ix=⟨groups ix,(nav.lane ix).lo,(nav.lane ix).hi,nav.packedStart groups ix⟩ := by
  let xs:=List.ofFn nav.lane
  let pre:=xs.take ix.val
  let post:=xs.drop (ix.val+1)
  have live : ix.val<xs.length:=by simp [xs]
  have nth : xs[ix.val]=nav.lane ix:=by simp [xs]
  have split : pre++nav.lane ix::post=xs:=by
    change xs.take ix.val++_::xs.drop (ix.val+1)=xs
    rw [←nth,List.getElem_cons_drop,List.take_append_drop]
  have size : (BucketRows.pack groups (fun _=>0) pre).length=ix.val:=by
    simp [pre,xs,BucketRows.pack_length]
  have eq:=BucketRows.middle groups pre (nav.lane ix) post
  rw [split] at eq
  have obs:=congrArg (fun l : List (BucketRow (Fin nav.groups))=>l[ix.val]?) eq
  have ok : ix.val<(BucketRows.pack groups (fun _=>0) xs).length:=by simpa [BucketRows.pack_length] using live
  rw [List.getElem?_eq_getElem ok,List.getElem?_append_right (by omega),size,Nat.sub_self] at obs
  exact Option.some.inj obs

variable {F : Type*} [Field F] [Fintype F] {S : Shape} {P : Plan F S} {bits : P.History→ℕ} {c : Clock}
  {aux lanes span : ℕ} (nav : RootArchive) (T : Buckets P bits c aux lanes span)
  (v : Plan.Terminal P bits) (total : nav.totalPairs=c.chunks*aux) (width : nav.pairsPerLane=span)
  (lanesEq : nav.initialLanes=lanes) (groupsEq : nav.groups=c.groups) (groups : Fin nav.initialLanes→Fin nav.groups)
  (home : ∀ i,finCongr groupsEq (groups i)=T.group v.1 (P.destination v.1 (T.site (finCongr lanesEq i))))

include total width lanesEq groupsEq home in
omit [Fintype F] in
theorem published_pair_count (ix : Fin nav.initialLanes) :
    T.length v (groups ix).val=BucketRows.count groups (List.ofFn nav.lane) (groups ix) := by
  subst lanes
  exact group_count (A₀ := RAM.TickPhysicalABI.mounted nav.age aux c.groups 0 0 0 0 0)
    nav T v total width groupsEq groups home (groups ix)

include total width lanesEq groupsEq home in
omit [Fintype F] in
/-- The code produced for an address in this physical row is one plus its
local ordinal, even if earlier lanes lie in different groups. -/
theorem published_pair_code (ix : Fin nav.initialLanes) (k : Fin c.chunks) (j : Fin aux)
    (inside : (nav.lane ix).lo≤k.val*aux+j.val ∧ k.val*aux+j.val<(nav.lane ix).hi) :
    T.code v (groups ix).val k j=1+nav.packedStart groups ix+(k.val*aux+j.val-(nav.lane ix).lo) := by
  subst lanes
  let layout := RAM.TickPhysicalABI.mounted nav.age aux c.groups 0 0 0 0 0
  let e:=BucketFiniteLabels.decode (nav.packedRow groups ix)
  have member : e∈T.finiteRows (A := layout) v := by
    rw [groups_rows (A₀ := layout) nav T v total width groupsEq groups home,nav.packed_rows groups]
    exact List.mem_map.mpr ⟨nav.packedRow groups ix,List.mem_ofFn.mpr ⟨ix,rfl⟩,rfl⟩
  have form : e=⟨(groups ix).val,(nav.lane ix).lo,(nav.lane ix).hi,nav.packedStart groups ix⟩:=by
    dsimp only [e]
    rw [packed_lane_row]; rfl
  have same := pairCode_owned (groups ix).val (k.val*aux+j.val) (finite_rows_disjoint (A₀ := layout) nav T v) member
    (by rw [form]) (by simpa only [form,Interval.inside] using inside)
  rw [form] at same
  rw [T.finite_values (A := layout) v] at same
  exact same


end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM LaneCursor TraceSuffix HistoryContraction RAM TickPhaseModel TickChronology NavigationPass
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type*} [Field F] [Fintype F] {S : Shape} {P : Plan F S} {bits : P.History→ℕ}
    {period width aux lanes q low : ℕ} (c : Clock) (hc : c.chunks=2*(period*width))
local notation "L" => period*width*aux+period*width*aux

omit [Fintype F] in
/-- Each genuinely emitted S12 endpoint word contains the public pin address
of its trace seed. The S5 row and S7 count determine the packed ordinal. -/
theorem seedPacked_address_published {W cap nD nt ns np hidden : ℕ}
    (nav : RootArchive) (T : Buckets P bits c aux lanes (2^low)) (v : Plan.Terminal P bits)
    (total : nav.totalPairs=c.chunks*aux) (widthEq : nav.pairsPerLane=2^low)
    (lanesEq : nav.initialLanes=lanes) (groupsEq : nav.groups=c.groups)
    (groups : Fin nav.initialLanes→Fin nav.groups)
    (home : ∀ i,finCongr groupsEq (groups i)=T.group v.1 (P.destination v.1 (T.site (finCongr lanesEq i))))
    (ix : Fin nav.initialLanes) (u : Fin (q+1)×Lane (q+1)) (laneId : ix.val=(finFunctionFinEquiv u.2).val)
    (j : Fin (seedExt L low u)) (ext packedCount : ℕ)
    (count : BucketRows.count groups (List.ofFn nav.lane) (groups ix)=packedCount)
    (fit : 1+cap+2*packedCount≤aux) :
    let g:=finCongr groupsEq (groups ix)
    let fitT : 1+cap+2*T.length v g.val≤aux:=by
      change 1+cap+2*T.length v (groups ix).val≤aux
      rwa [RootArchive.published_pair_count (nav:=nav) (T:=T) (v:=v) (groups:=groups)
        (total:=total) (width:=widthEq) (lanesEq:=lanesEq) (groupsEq:=groupsEq) (home:=home) ix,count]
    HistoryInitialSeed.pairAt (W:=W) fit nD nt ns np hidden (nav.packedStart groups ix) ext (ext+j.val)=
      ((2+(Buckets.packEndpoint (c:=c) (hc:=hc) (T:=T) (v:=v) (g:=g) (fit:=fitT)
        (q:=nD) (nt:=nt) (ns:=ns) (np:=np) (seedEndpoint L low u j)).val:ℕ):Word W) := by
  intro g fitT
  have len : T.length v g.val=packedCount :=
    (RootArchive.published_pair_count (nav:=nav) (T:=T) (v:=v) (groups:=groups)
      (total:=total) (width:=widthEq) (lanesEq:=lanesEq) (groupsEq:=groupsEq) (home:=home) ix).trans count
  cases len
  let endpoint:=seedEndpoint L low u j
  let z:=Buckets.endpointPoint c hc (Buckets.pairIndex endpoint)
  let base:=ix.val*2^low
  have e : endpoint.val=2*base+j.val:=by
    change laneStart low (finFunctionFinEquiv u.2).val+j.val=_
    rw [←laneId];unfold laneStart base;ring
  have atI : z.1.val*aux+z.2.val=base+j.val/2:=by
    have addr:=Buckets.endpointPoint_address c hc (Buckets.pairIndex endpoint)
    change z.1.val*aux+z.2.val=endpoint.val/2 at addr
    omega
  have globals : nav.totalPairs=L:=by rw [total,hc];ring
  have inStream : base+j.val/2<nav.totalPairs:=by have ee:=endpoint.isLt;rw [globals];omega
  have clipped : (nav.lane ix).lo=base:=by
    change min (ix.val*nav.pairsPerLane) nav.totalPairs=base
    rw [widthEq];exact Nat.min_eq_left (by dsimp only [base] at inStream ⊢;omega)
  have localBound : j.val/2<2^low:=by
    have lt:=j.isLt
    have stage:=(seedEndpoint_lane u j).1
    simp only [seedExt,stage,ite_true,retained,pairs,←laneId] at lt
    have:=Nat.min_le_left (2^low) (L-ix.val*2^low)
    omega
  have last : base+j.val/2<(nav.lane ix).hi:=by
    change base+j.val/2< min ((ix.val+1)*nav.pairsPerLane) nav.totalPairs
    rw [widthEq,Nat.add_mul,Nat.one_mul]
    exact lt_min (by dsimp only [base];omega) inStream
  have code : T.code v g.val z.1 z.2=1+nav.packedStart groups ix+j.val/2:=by
    change T.code v (groups ix).val z.1 z.2=_
    rw [RootArchive.published_pair_code (nav:=nav) (T:=T) (v:=v) (groups:=groups)
      (total:=total) (width:=widthEq) (lanesEq:=lanesEq) (groupsEq:=groupsEq) (home:=home) ix z.1 z.2
      ⟨by rw [atI,clipped];omega,atI.trans_lt last⟩,atI,clipped]
    omega
  have live : T.code v g.val z.1 z.2≠0:=by omega
  let l : PackedChunkTransfer.Live (T.code v g.val):=⟨z,live⟩
  have index : (T.packed v g l).val=nav.packedStart groups ix+j.val/2:=by
    rw [T.addr];change T.code v g.val z.1 z.2-1=_;omega
  have below : nav.packedStart groups ix+j.val/2<T.length v g.val:=by
    rw [←index];exact (T.packed v g l).isLt
  have pin : Buckets.packEndpoint (c:=c) (hc:=hc) (T:=T) (v:=v) (g:=g) (fit:=fitT)
      (q:=nD) (nt:=nt) (ns:=ns) (np:=np) endpoint =
      TickSelectedPins.pair fitT nD nt ns np (decide (j.val%2=1)) ⟨nav.packedStart groups ix+j.val/2,below⟩ := by
    rw [Buckets.packEndpoint_owned (c:=c) (hc:=hc) (T:=T) (v:=v) (g:=g) (fit:=fitT)
      (q:=nD) (nt:=nt) (ns:=ns) (np:=np) endpoint ((T.hit v g z).mp live)]
    have side : Buckets.pairSide endpoint=decide (j.val%2=1):=by
      unfold Buckets.pairSide
      apply decide_eq_decide.mpr
      omega
    rw [side]
    exact congrArg (TickSelectedPins.pair fitT nD nt ns np (decide (j.val%2=1))) (Fin.ext index)
  change HistoryInitialSeed.pairAt (W:=W) fit nD nt ns np hidden (nav.packedStart groups ix) ext
    (ext+j.val) = ((2+(Buckets.packEndpoint (c:=c) (hc:=hc) (T:=T) (v:=v) (g:=g) (fit:=fitT)
      (q:=nD) (nt:=nt) (ns:=ns) (np:=np) endpoint).val:ℕ):Word W)
  rw [pin]
  simp only [HistoryInitialSeed.pairAt,Nat.add_sub_cancel_left,below,dite_eq_left,BitLayout.sourceAddress]


end
end ThreeFlat.Diagonal.TraceBitHeader

end OAI
