import OAI.Hierarchy.DescentDatedOriginalParentPaths
import OAI.Hierarchy.DescentDatedOriginalParentMass
import OAI.Hierarchy.DescentOrdinaryParallelSide
import OAI.Hierarchy.DescentOrdinaryParentGroups
import OAI.Hierarchy.DescentDatedOriginalParentRecord

namespace OAI
/-! # Two forward ranks in the true previous donor chart determine chronological orientation -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w short a : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
set_option quotPrecheck false
attribute [local irreducible] Stage.nativeParts physicalRows DepotRAM.chip packDonor StarKeys.nativeKey
local notation "A" => prior.placement
local notation "J" => Fin (S.groupCount i)
local notation "V" => prior.V
local notation "native" => prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)
variable {he : 0≤ε} {choice : (prior.placement.stage.result he).Choice}
    {n : Normalize ((prior.placement.stage.result he).state choice)}
variable {z' D' : ℕ} {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he prior.placement.stage choice n next) (port : MeterPort prior)
local notation "H" => port.hosts
local notation "T" => (A).stage
local notation "home" => scanHomeAt he T
local notation "color" => scanColorAt he T
local notation "addr" => nativeAddress he T
local notation "r" => 2^k
local notation "rr" => BitDescription.scannedRows he T
local notation "lay" => bestLayout (branchWidth G (fun _ : (rr).pairs=>(T).z) ((rr).profile choice))
local notation "bytes" => donorNameBits (T).k (T).Δ
local notation "slots" => 2^(packExponent 20 (T).Δ)+2
local notation "gain" => gainExponent 20 (T).Δ
local notation "peers" => rotor A rank
local notation "grp" => Equiv.refl J
local notation "hosts" => port.vertex
variable (win : Fin (S.groupCount i)×prior.V→Fin (2^k)→Cell a) (hm : 0<port.groupsPerWord)
variable (named : prior.placement.SiteNamed (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)))
    (fit : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val<2^short)
    (winner : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val=
      1+2*heap (nativeAddress he prior.placement.stage (scanHomeAt he prior.placement.stage u)).2+
        (scanColorAt he prior.placement.stage u).toNat)
    (df : prior.placement.degree<2^short)
    (order : ∀e f,(prior.order e).val<(prior.order f).val ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
variable (profile : ℕ)
variable (b : ℕ) (m : Memory w)
    (sumSize : (shape (2^k) prior.placement.degree (2*prior.placement.cap) profile).outputBits*port.groupsPerWord≤w)
    (stored :
      let rankAt:=groupRank (Fin.valEmbedding : Fin (S.groupCount i) ↪ ℕ) (prior.vertex.trans Fin.valEmbedding)
      let shape₀:=shape (2^k) prior.placement.degree (2*prior.placement.cap) profile
      let world:=terrain (short:=short) prior.placement (prior.order.trans Fin.valEmbedding)
        S prior.valid (cableNames k rankAt) win (rotor prior.placement rankAt)
      let partsAt:=spread (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex world
      let inputs:=Gather.flat (Gather.descriptorInputs (K:=2^(k+1)) shape₀ prior.placement.cap partsAt)
      ∀j,m (b+j.val)=((DescentPacking.PackedMatch.topologyWords (M:=port.groupsPerWord) shape₀ inputs j).val:Computability.VPVNP.BurstRAM.Word w))
variable (dest : ℕ) (issued : Memory w)
    (roster : Fin port.hosts→Fin prior.placement.degree→Option (Fin port.hosts))
    (mounted : ∀(z : Fin (S.groupCount i)×prior.V) j,roster (port.vertex z.2) j=
      (rotor prior.placement (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)) z j).map
        (fun h=>port.vertex h.2))
local notation "fmt" => Stage.shapeOf (short:=short) A bytes
local notation "measured" => Stage.nativeParts (short:=short) A native S prior.valid rank win grp hosts hm profile dest issued roster (A).hub lay bytes

open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator

local notation "sampleSlot" => DescentRawCablePanel.slot A S prior.valid native hosts grp (rr).pick
local notation "oldPorts" => S.groupCount i*r*(A).cap

variable (birth :
    let stage:=prior.placement.stage
    let actor:=scanHomeAt he stage
    let tint:=scanColorAt he stage
    let flow:=nativeTraffic W.graph W.core actor
    let limit:=prior.placement.cap
    let shape₀:=shape (2^k) prior.placement.degree (2*limit) profile
    let cellAt:=Stage.slot he prior.placement (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex hm
    ∀c : ScanColonies he stage,∀e : Matched flow limit (thinList actor tint c) (thickList actor tint c),
      ∃j : Fin shape₀.pairs,j.val=(pairNumber (DescentPacking.amount (live flow))
        (slabPacking flow limit (thinList actor tint c) (thickList actor tint c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=DescentPacking.PackedMatch.SixBirths.slot (cellAt c).2 j q
        DescentPacking.PackedMatch.SixBirths.atom stage.z (digit (shape₀.digit+1) ip.val (issued (dest+(cellAt c).1.val)).val) ip.val=
          some (stage.z,DescentTerminalEpochFlags.encode ((BitDescription.scannedRows he stage).profile choice ⟨c,e⟩),q.val))

open DescentGroupPeerOrder DescentSharedCableNames DescentHaloWalkRAM DescentPackedColony
local notation "N" => rawGraph he T choice
local notation "owner" => rawOwner he T choice n ((rr).state choice) (originalId _)
local notation "positiveRows" => DescentRawCablePanel.Live A (rr).pick
local notation "homeAt" => newSite W.graph (rr).pick lay (rr).pack
local notation:max "targetAt" e:arg side:arg => ticket.donorKey (homeAt (if side then (N).dst (e).val else (N).src (e).val))

local notation:max "dest_" x:arg => n.destination (rawInput he T choice ((rr).state choice) x)
local notation:max "trim_" x:arg => mergeHub ticket.donorHub (T).k gain (ticket.donorKey (homeAt x))
local notation:max "lo_" h:arg j:arg side:arg => (roleLow (T).k gain slots side
  (DepotRAM.seatDonor fmt profile G.b slots (measured h (groupSeat j).1) (groupSeat j).2.1 (groupSeat j).2.2.1)
  (groupSeat j).2.2.2).val

private theorem merge_first {U:Type} (flag:U→Bool)(k g:ℕ)(x:Key U):
    (mergeHub flag k g x).1=x.1:=by
  unfold mergeHub
  split <;> rfl

set_option maxHeartbeats 700000 in
include named fit winner df order profile in
private theorem old_endpoint_groups (e:positiveRows)(different:owner ((N).src e.val)≠owner ((N).dst e.val)):
    (trim_ ((N).src e.val)).1.1=(trim_ ((N).dst e.val)).1.1:=by
  let anch:DescentSharedCableNames.Stage.Positive A:=⟨anchor (rr).pick e.val,e.property⟩
  let orig:=Stage.parentRows (short:=short) A native S prior.valid rank win profile lay anch (role e.val)
  have seen:=Stage.parent_actual (short:=short) A native S prior.valid rank win he prior.valid.coordinates named fit
    winner df order profile ticket.donorChart.same lay e
  have chart:ticket.donorChart.col=addr:=eq_of_heq ticket.donorChart.native
  have key:ticket.donorKey=StarKeys.nativeKey W.graph W.core home color (T).cap addr ticket.donorChart.same lay :=by
    unfold OrdinaryLink.donorKey IssuedDonorChart.key
    exact congrArg (fun loc => StarKeys.nativeKey W.graph W.core home color (T).cap loc ticket.donorChart.same lay) chart
  have live : orig≠none :=by
    intro empty
    have same:=seen.1 empty
    have raw : n.destination (rawInput he T choice ((rr).state choice) ((N).src e.val)) =
        n.destination (rawInput he T choice ((rr).state choice) ((N).dst e.val)) :=
      ((IssuedRows.common_chart he T choice ticket.issued ((rr).state choice)).choose_spec.1.2 _ _).2
        (congrArg (fun x=>mergeHub ticket.donorHub (T).k gain (ticket.donorKey x)) same)
    exact different (congrArg (originalId _) raw)
  obtain ⟨p,got⟩:=Option.ne_none_iff_exists'.mp live
  have routed:=seen.2 p got
  have both: (ticket.donorKey (homeAt ((N).src e.val))).1.1=(ticket.donorKey (homeAt ((N).dst e.val))).1.1:=by
    rw [key]
    exact (Stage.walked_group A rank routed.src).trans (Stage.walked_group A rank routed.dst).symm
  simpa only [merge_first] using both

set_option maxHeartbeats 700000 in
private theorem end_host_order (e:positiveRows)
    (shared:(trim_ ((N).src e.val)).1.1=(trim_ ((N).dst e.val)).1.1):
    let u:=trim_ ((N).src e.val)
    let v:=trim_ ((N).dst e.val)
    (hosts v.1.2).val*((2^((T).k+1)-1)*slots)+SiteDecode.localNumber (T).k slots v <
      (hosts u.1.2).val*((2^((T).k+1)-1)*slots)+SiteDecode.localNumber (T).k slots u
      ↔ owner ((N).dst e.val)<owner ((N).src e.val):=by
  intro u v
  obtain ⟨ht,rad,chart,positions,ord⟩:=ticket.venueRows
  let src:=dest_ ((N).src e.val)
  let dst:=dest_ ((N).dst e.val)
  let dgs:=S.groupDigits ht rad
  have loc (x:(N).Site):
      ((next.placement.pos (dest_ x)).1,next.placement.block (dest_ x))=dgs (trim_ x).1.1 ∧
      (next.vertex (next.placement.pos (dest_ x)).2).val=
        (hosts (trim_ x).1.2).val*((2^((T).k+1)-1)*slots)+SiteDecode.localNumber (T).k slots (trim_ x):=by
    have where_:=positions ((rr).state choice) ticket.donorChart x
    refine ⟨where_.1,?_⟩
    rw [ord,where_.2]
    change ((prior.vertex (trim_ x).1.2).val*(2^(k+1)-1)+nodeNumber (trim_ x).2.1.1 (trim_ x).2.1.2)*slots+
      (trim_ x).2.2=(prior.vertex (trim_ x).1.2).val*((2^(k+1)-1)*slots)+
      ((0*2^(k+1)+nodeNumber (trim_ x).2.1.1 (trim_ x).2.1.2)*slots+(trim_ x).2.2)
    ring
  have l:=loc ((N).src e.val)
  have r₁:=loc ((N).dst e.val)
  have same:=r₁.1.trans ((congrArg dgs shared.symm).trans l.1.symm)
  have gEq:(next.placement.pos dst).1=(next.placement.pos src).1:=congrArg (fun v : Fin (S.groupCount (i+1)) × Fin (2^k) => v.1) same
  have xEq:next.placement.block dst=next.placement.block src:=congrArg (fun v : Fin (S.groupCount (i+1)) × Fin (2^k) => v.2) same
  rw [←l.2,←r₁.2]
  change _ ↔ originalId _ dst<originalId _ src
  rw [next.siteName (by omega) dst,next.siteName (by omega) src]
  let pos:=next.placement.siteSlot next.vertex next.valid.coordinates
  have ordered:=DescentPhysicalOrder.physical_lt_iff (DescentSiteTape.rank pos) dst src
  change _ ↔ (DescentPhysicalOrder.physical (DescentSiteTape.rank pos) dst).val <
    (DescentPhysicalOrder.physical (DescentSiteTape.rank pos) src).val
  rw [show ((DescentPhysicalOrder.physical (DescentSiteTape.rank pos) dst).val <
    (DescentPhysicalOrder.physical (DescentSiteTape.rank pos) src).val) ↔ (pos dst).val<(pos src).val from ordered]
  dsimp only [pos]
  rw [GroupStage.siteSlot_val,GroupStage.siteSlot_val,gEq,xEq,Nat.add_lt_add_iff_right,
    Nat.mul_lt_mul_right (Nat.two_pow_pos _),Nat.add_lt_add_iff_left]


local notation:max "pathAt" side:arg donor:arg q:arg => DepotRAM.atSeat fmt profile G.b slots side donor (q).1 (q).2.1 (q).2.2

private theorem compare_rank_digits
    {idxL idxR rankL rankR seenL seenR hostL hostR lowL lowR numL numR baseWidth : ℕ}
    (iL : idxL = rankL) (iR : idxR = rankR) (hL : seenL = hostL) (hR : seenR = hostR)
    (lL : lowL = numL) (lR : lowR = numR)
    (forward : rankL < rankR ↔ seenL < seenR) (reverse : rankR < rankL ↔ seenR < seenL)
    (fitsL : numL < baseWidth) (fitsR : numR < baseWidth) :
    idxL*baseWidth+lowL < idxR*baseWidth+lowR ↔ hostL*baseWidth+numL < hostR*baseWidth+numR := by
  subst idxL idxR hostL hostR lowL lowR
  have ranks_eq : rankL = rankR ↔ seenL = seenR := by omega
  simp only [DescentOrdinaryDonorHalo.lex fitsL fitsR, forward, ranks_eq]

set_option maxHeartbeats 1400000 in
include ticket named fit winner df order sumSize stored mounted birth in
theorem original_upper (e:positiveRows)(different:owner ((N).src e.val)≠owner ((N).dst e.val)):
    let h:=(sampleSlot e).1
    let q:=groupSeat (sampleSlot e).2
    let donor:=measured h q.1
    let idx (side:Bool):=DepotRAM.Material.ranked fmt donor.chart (pathAt side donor q.2)
    let room:=(2^((T).k+1)-1)*slots
    decide (idx true*room+lo_ h (sampleSlot e).2 true < idx false*room+lo_ h (sampleSlot e).2 false)=
      decide (owner ((N).dst e.val)<owner ((N).src e.val)):=by
  intro h q donor idx room
  obtain ⟨p,found⟩:=original_parent_endpoints (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile dest issued roster mounted e different
  let pathNo (s:Bool):=ActorPath.index (A).degree (if s then p.2 else p.1)
  let endp:=DescentHaloCompilation.reached roster
  let atEnd (s:Bool):=endp h (pathNo s)
  have val (b₀:Bool):atEnd b₀=(hosts (targetAt e b₀).1.2).val:=by
    have got:Gather.reaching roster h (pathNo b₀)=some (hosts (targetAt e b₀).1.2):=(found b₀).2
    change number (Gather.reaching roster h (pathNo b₀))=_
    rw [got]; rfl
  have earlier (b₀:Bool):idx b₀=Ranks.earlier endp h (atEnd b₀):=by
    have token:pathAt b₀ donor q.2=Packed.token (some (pathNo b₀)):=(found b₀).1
    have chartAt : donor.chart = DescentHaloPackedRebase.digest (Stage.ordinalChart A roster h) := by
      unfold donor Stage.nativeParts
      rfl
    dsimp only [idx]
    rw [chartAt,token]
    exact DepotRAM.Material.ranked_read fmt (Stage.ordinalChart A roster h) (pathNo b₀)
  have small (z₀:(N).Site):SiteDecode.localNumber (T).k slots (trim_ z₀)<room:=by
    apply SiteDecode.local_number_pitch
    exact merged_mem_keys _ _ _ _ ((IssuedRows.common_chart he T choice ticket.issued ((rr).state choice)).choose_spec.1.1 _)
  have sl:=original_parent_low (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth false e different
  have tl:=original_parent_low (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth true e different
  change lo_ h (sampleSlot e).2 false=SiteDecode.localNumber (T).k slots (trim_ ((N).src e.val)) at sl
  change lo_ h (sampleSlot e).2 true=SiteDecode.localNumber (T).k slots (trim_ ((N).dst e.val)) at tl
  have lt:=Ranks.compare endp h (pathNo true) (pathNo false)
  have gt:=Ranks.compare endp h (pathNo false) (pathNo true)
  change _ ↔ atEnd true<atEnd false at lt
  change _ ↔ atEnd false<atEnd true at gt
  have ltv : atEnd true = (hosts (trim_ ((N).dst e.val)).1.2).val := by
    refine (val true).trans ?_
    simp only [merge_first]
    apply congrArg (fun x : (N).Site => (hosts (ticket.donorKey (homeAt x)).1.2).val)
    exact ite_eq_left True.intro
  have rtv : atEnd false = (hosts (trim_ ((N).src e.val)).1.2).val := by
    refine (val false).trans ?_
    simp only [merge_first]
    apply congrArg (fun x : (N).Site => (hosts (ticket.donorKey (homeAt x)).1.2).val)
    exact ite_eq_right (by decide)
  have out:=end_host_order ticket port e (old_endpoint_groups ticket win named fit winner df order profile e different)
  apply decide_eq_decide.mpr
  exact (compare_rank_digits (earlier true) (earlier false) ltv rtv tl sl lt gt
    (small ((N).dst e.val)) (small ((N).src e.val))).trans out

local notation "pitch" => (2^((T).k+1)-1)*slots
variable (fieldBits : ℕ)
local notation "form" => rawFormat (G:=G) (prior:=prior) profile pitch fieldBits
local notation:max "cell" h:arg j:arg => originalRecord ticket port win hm named fit winner df order profile b m sumSize stored
  dest issued roster mounted birth pitch fieldBits h (groupSeat j).1 (groupSeat j).2
local notation:max "physicalSide" e:arg => DescentParallelBase.side (originalId _) (dest_ ((N).src (e).val)) (dest_ ((N).dst (e).val))

set_option maxHeartbeats 1400000 in
/-- The orientation in every emitted live record agrees with the actual chronological site names. -/
theorem original_record_upper (pathWidth:breadth (A).degree<2^fieldBits)
    (ticketWidth:(breadth (A).degree+1)*DepotRAM.Material.roles fmt≤2^fieldBits)
    (e:positiveRows)(cross:owner ((N).src e.val)≠owner ((N).dst e.val))(paid:0<(N).width e.val/(A).z) :
    let d:=sampleSlot e
    ∀record,cell d.1 d.2=some record→(record).upper=physicalSide e :=by
  intro d r₀ present
  have weight:=original_parent_mass ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth e
  simp only [ite_eq_right cross] at weight
  obtain ⟨p,both⟩:=original_parent_endpoints (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile dest issued roster mounted e cross
  let q₀:=groupSeat d.2
  let donor:=measured d.1 q₀.1
  have fit₀ : DepotRAM.Material.ParentRoom fmt form donor
      (DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt roster d.1))
      q₀.2 (2^((T).k+1)*slots) ((breadth (A).degree+1)*DepotRAM.Material.roles fmt) next.placement.cap :=
    original_parent_room ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits roster d.1 q₀.1 q₀.2
  obtain ⟨s₀,stored₀,_,_,_,_,_,side,_⟩:=DepotRAM.Material.parent_emitted fmt form donor q₀.2
    («H»:=H) (Q:=2^((T).k+1)*slots) (K:=(breadth (A).degree+1)*DepotRAM.Material.roles fmt) (L:=next.placement.cap)
    roster d.1 fit₀
    (ActorPath.index (A).degree p.1) (ActorPath.index (A).degree p.2) (both false).1 (both true).1
    (weight.trans_gt paid).ne' pathWidth ticketWidth
  have eq:s₀=r₀:=Option.some.inj (stored₀.symm.trans present)
  exact eq ▸ side.trans (original_upper ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth e cross)

/-- The final naming permutation in an arbitrary signed-stage case preserves exactly its
selected source-site order. This requires neither an identity permutation nor occupied edges. -/
theorem orientation_after_naming {U:Type*} [Fintype U] (site:U↪ℕ) (src dst:U) :
    decide (originalId U (DescentPhysicalOrder.rename site dst) <
      originalId U (DescentPhysicalOrder.rename site src)) = decide (site dst < site src) := by
  apply decide_eq_decide.mpr
  change (Fintype.equivFin U (DescentPhysicalOrder.rename site dst)).val <
    (Fintype.equivFin U (DescentPhysicalOrder.rename site src)).val ↔ site dst<site src
  simp only [DescentPhysicalOrder.code_rename]
  exact DescentPhysicalOrder.physical_lt_iff site dst src

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
