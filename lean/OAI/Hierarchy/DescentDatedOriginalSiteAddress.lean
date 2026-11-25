import OAI.Hierarchy.DescentDatedOriginalMeasuredShelf
import OAI.Hierarchy.DescentOrdinarySignedEmission

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w short a : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
set_option quotPrecheck false
attribute [local irreducible] Stage.nativeParts physicalRows DepotRAM.chip packDonor StarKeys.nativeKey OrdinaryLink.donorKey OrdinaryLink.measuredDonors
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
local notation "rr" => BitDescription.scannedRows he T
local notation "lay" => bestLayout (branchWidth G (fun _ : (rr).pairs=>(T).z) ((rr).profile choice))
local notation "bytes" => donorNameBits (T).k (T).Δ
local notation "slots" => 2^(packExponent 20 (T).Δ)+2
local notation "gain" => gainExponent 20 (T).Δ
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
local notation "oldPorts" => S.groupCount i*(2^k)*(A).cap

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

local notation "N" => rawGraph he T choice
local notation "owner" => rawOwner he T choice n ((rr).state choice) (originalId _)
local notation "positiveRows" => DescentRawCablePanel.Live A (rr).pick
local notation:max "units" h:arg j:arg => liveMass (report (T).k gain slots
  (DepotRAM.seatDonor fmt profile G.b slots (measured h (groupSeat j).1) (groupSeat j).2.1 (groupSeat j).2.2.1)
  (groupSeat j).2.2.2)

open DescentSharedCableNames DescentHaloPackedRebase DescentParallelBase.ParentFilter
local notation "homeAt" => newSite W.graph (rr).pick lay (rr).pack
local notation:max "ctr" e:arg => mergeHub ticket.donorHub (T).k gain (ticket.donorKey (homeAt e))
local notation "P₀" => breadth (A).degree
local notation "Q" => 2^((T).k+1)*slots
local notation "K₀" => (P₀+1)*DepotRAM.Material.roles fmt
local notation "pitch" => (2^((T).k+1)-1)*slots
variable (fieldBits : ℕ)
local notation "form" => rawFormat (G:=G) (prior:=prior) profile pitch fieldBits
local notation "roomAt" => original_parent_room ticket port win hm named fit winner df order profile b m sumSize stored
                            dest issued roster mounted birth pitch fieldBits roster
local notation:max "rev" h:arg => digest (DepotRAM.Material.reverseEntries fmt roster h)

local notation:max "cell" h:arg j:arg => originalRecord ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits h (groupSeat j).1 (groupSeat j).2
local notation:max "current" x:arg => n.destination (rawInput he T choice ((rr).state choice) x)
local notation:max "venue" x:arg => ticket.parentVenue port.enough (next.placement.pos (current x)).2
local notation:max "endRack" e:arg => hosts (ticket.donorKey (homeAt e)).1.2
local notation:max "endLow" e:arg => SiteDecode.localNumber (T).k slots (ctr e)

variable (age:i<S.length) (radix:S.radix=2^k)

variable (B:OrdinaryModel he prior.placement.stage choice (Fin (S.groupCount i)×prior.V))
local notation "world" => (B.named he T choice prior.order).result
local notation "act" => B.rawSite he T choice
variable (coh:n.result=(B.named he prior.placement.stage choice prior.order).result)
variable (places:∀x:(rawGraph he prior.placement.stage choice).Site,
  cast (congrArg (fun u:MarkedWorld F d P bits=>u.graph.Site) coh)
    (n.destination (rawInput he prior.placement.stage choice ((BitDescription.scannedRows he prior.placement.stage).state choice) x))=
    B.rawSite he prior.placement.stage choice x)
local notation "A₁" => modelStage (next:=next) B coh
local notation:max "raster₁" x:arg => ticket.parentVenue port.enough ((A₁).pos (act x)).2
local notation "key" => B.chart.key he T choice
local notation "last" => DescentSixParty.MarkedWorld.address (W.selected G (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice))
  key B.chart.hub (T).k gain
local notation:max "survives" e:arg => last (homeAt ((N).src (e).val))≠last (homeAt ((N).dst (e).val))
local notation:max "valueAt" e:arg => cell (sampleSlot e).1 (sampleSlot e).2
variable (pathWidth:breadth prior.placement.degree<2^fieldBits)
  (ticketWidth:(breadth prior.placement.degree+1)*DepotRAM.Material.roles
    (Stage.shapeOf (short:=short) prior.placement (donorNameBits prior.placement.stage.k prior.placement.stage.Δ))≤2^fieldBits)
local notation "full" => original_record_full (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits age radix pathWidth ticketWidth

open DescentParallelBase DescentOrdinaryParentSupport DescentSharedCableNames DescentSixParty.MarkedWorld
local notation "targetRows" => Source P₀ Q K₀ next.placement.cap
local notation "dataAt" => fun e:positiveRows=>valueAt e
local notation "pairNo" => PairRAM.globalNumberBy W.graph W.core home color (T).cap (originalId (ScanColonies he T))
local notation "oldCut" => B.old
local notation "chosenCut" => B.used
local notation "stageCut" => fun _ : (rr).pairs=>dvd_refl (T).z
local notation "ok" => model_bounds (next:=next) B coh
local notation "eqG" => model_grain ticket B coh
local notation "paths" => modelPaths (short:=short) (prior:=prior) (choice:=choice) win profile
local notation "routes" => model_paths (short:=short) (prior:=prior) (choice:=choice) win named fit winner df order profile B
local notation "groups'" => S.groupDigits age radix
local notation "placed" => fun x=> (model_sites ticket port age radix B coh places x).1
local notation "atV" => ticket.parentVenue port.enough
local notation "host" => DescentSharedCableNames.Stage.Host (Fin (S.groupCount (i+1))) next.V k
local notation "C₀" => DescentOrdinaryParentBlocks.blocks W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁ (T).unitPos
local notation "donors" => DescentOrdinaryParentSupport.donorRows W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁ S ok eqG (T).unitPos A prior.valid
local notation "heads" => DescentOrdinaryParentBlocks.head W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁
local notation "headEnds" => DescentOrdinaryParentBlocks.head_ends W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁
local notation "addr'" => DescentOrdinaryParentSupport.parentAddress W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁ S ok eqG (T).unitPos A prior.valid rank groups' paths routes placed hosts grp
local notation "sub" => (B.normalized he T choice).result
local notation "order₀" => (B.tape he T choice prior.order).sourceKey (sub).graph.src B.site (sub).graph.width
local notation "fields" => model_original_fields (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth
local notation "exists_" => model_original_present (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth fieldBits B coh places pathWidth ticketWidth

variable (reciprocal:∀v u j,roster v j=some u→∃l,roster u l=some v)
local notation "Z" => originalMeasurement (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal
local notation "shelf" => originalShelf (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal
local notation "O" => 2^k*(A).cap*11
local notation "shortAddr" => shortSlot A S prior.valid native hosts (rr).pick
local notation:max "band" h:arg => (groups').symm ((h).1.1,(h).2)
local notation "orig" => originalRecord ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth pitch fieldBits

def fullSeat {groups blocks cap:ℕ} (g:Fin groups) (q:Fin blocks×Fin cap×Fin 11) : Fin ((groups*blocks*cap)*11) :=
  finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (g,q.1),q.2.1),q.2.2)

theorem fullSeat_read {groups blocks cap:ℕ} (g:Fin groups) (q:Fin blocks×Fin cap×Fin 11) :
    groupSeat (fullSeat g q)=(g,q):=by simp only [groupSeat,fullSeat,Equiv.symm_apply_apply]

def splitSeat {k cap:ℕ} (o : Fin (2^k*cap*11)) : Fin (2^k)×Fin cap×Fin 11 :=
  let a:=finProdFinEquiv.symm o
  let t:=finProdFinEquiv.symm a.1
  (t.1,t.2,a.2)

private theorem splitSeat_pack {k cap : ℕ} (x : Fin (2^k)) (v : Fin cap) (j : Fin 11) :
    splitSeat (finProdFinEquiv (finProdFinEquiv (x,v),j)) = (x,v,j) := by
  simp only [splitSeat, Equiv.symm_apply_apply]

theorem seat_index (o:Fin O) : (DepotRAM.Material.seatIndex fmt (splitSeat (k:=k) (cap:=(A).cap) o)).val=o.val :=by
  obtain ⟨⟨s,j⟩,rfl⟩ := (@finProdFinEquiv (2^k*(A).cap) 11).surjective o
  obtain ⟨⟨x,t⟩,rfl⟩ := (@finProdFinEquiv (2^k) (A).cap).surjective s
  erw [splitSeat_pack x t j]
  change (finProdFinEquiv (x, finProdFinEquiv (t,j))).val = (finProdFinEquiv (finProdFinEquiv (x,t),j)).val
  simp only [finProdFinEquiv_apply_val]
  ring

theorem splitSeat_eq (o:Fin O) :
    splitSeat o=(DepotRAM.Material.seatIndex fmt).symm
      (Fin.cast (show O=DepotRAM.Material.roles fmt by exact Nat.mul_assoc _ _ _) o) :=by
  apply (DepotRAM.Material.seatIndex fmt).injective
  rw [Equiv.apply_symm_apply]
  exact Fin.ext (seat_index o)

private theorem sample_coord (e:positiveRows) :
    let pos:=sampleSlot e
    let raw:=shortAddr e
    pos.1=raw.1 ∧ groupSeat pos.2=(birthGroup A (rr).pick e,splitSeat raw.2) :=
  ⟨rfl,by simp [DescentRawCablePanel.slot,shortSlot,groupSeat,birthGroup,splitSeat_pack]⟩

private theorem splitSeat_injective {k cap:ℕ} : Function.Injective (splitSeat (k:=k) (cap:=cap)) :=by
  intro e f eqn
  obtain ⟨⟨ex,ej⟩,rfl⟩:=finProdFinEquiv.surjective e
  obtain ⟨⟨fx,fj⟩,rfl⟩:=finProdFinEquiv.surjective f
  obtain ⟨⟨a,b⟩,rfl⟩:=finProdFinEquiv.surjective ex
  obtain ⟨⟨x,y⟩,rfl⟩:=finProdFinEquiv.surjective fx
  simp only [splitSeat,Equiv.symm_apply_apply,Prod.mk.injEq] at eqn
  rcases eqn with ⟨rfl,rfl,rfl⟩
  rfl

/-- Read any original donor address, including nonexistent roles, exactly once.
No source record is postulated at the receiving endpoint. -/
theorem original_shelf_read (h:host) (d:Fin H) (o:Fin O) :
    (shelf).issued h (d,o)=orig d (band h) (splitSeat o) :=by
  let priorAt₀:=priorAt (W:=W) (G:=G) (stage:=k) (edge:=prior.order) (pick:=(rr).pick) (S:=S) (prior:=A)
    (installed:=prior.valid) (digits:=groups') (name:=hosts) h (d,o)
  change priorAt₀.bind (fun e=>valueAt e)=_
  unfold priorAt₀ priorAt
  split
  next found=>
    have atD:=found.choose_spec.2
    have coord:=sample_coord port found.choose
    rw [atD] at coord
    simp only [Option.bind_some,coord.1,coord.2,found.choose_spec.1]
    rfl
  next vacant=>
    simp only [Option.bind_none]
    let j:=fullSeat (band h) (splitSeat o)
    have empty:=originalRecord_absent ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted
      birth pitch fieldBits d j
    have gap:¬∃e:positiveRows,sampleSlot e=(d,j) ∧ owner ((N).src e.val)≠owner ((N).dst e.val) ∧ 0<(N).width e.val/(A).z:=by
      rintro ⟨e,where_,_,_⟩
      have coord:=sample_coord port e
      have rawHost : (shortAddr e).1=d := coord.1.symm.trans (congrArg Prod.fst where_)
      have rawSeat : (birthGroup A (rr).pick e,splitSeat (shortAddr e).2)=(band h,splitSeat o) :=
        coord.2.symm.trans ((congrArg groupSeat (congrArg Prod.snd where_)).trans (fullSeat_read _ _))
      apply vacant
      exact ⟨e,congrArg Prod.fst rawSeat,Prod.ext rawHost (splitSeat_injective (congrArg Prod.snd rawSeat))⟩
    have z:=empty gap
    change orig d (groupSeat j).1 (groupSeat j).2=none at z
    rw [show groupSeat j=(band h,splitSeat o) from fullSeat_read _ _] at z
    exact z.symm

local notation "seen" => original_shelf_read (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal
local notation:max "srcFace" t:arg => (⟨(t).val,(t).property.1,Or.inl rfl⟩:Local C₀ ((C₀).src (t).val))

set_option maxHeartbeats 1400000 in
/-- Launch from the source face of each real retained parent. The extent and all sibling
offsets share this original address on the previous host, even at the opposite endpoint. -/
theorem original_launch_row (h:host) (t:Local C₀ h) :
    let a:=(Z).loc ((Z).raw h t)
    orig a.1 (band h) (splitSeat a.2)=some ((Z).read ((C₀).src t.val) (srcFace t)) :=by
  let rowAddr := (Z).loc ((Z).raw h t)
  have read := seen h rowAddr.1 rowAddr.2
  have shared : (Z).read h t=(Z).read ((C₀).src t.val) (srcFace t) := rfl
  exact read.symm.trans (((shelf).covers h t).trans (congrArg some shared))

/-- The physical donor address is shared by the two genuine faces of a retained parent. -/
theorem original_address_both (h:host) (t:Local C₀ h) :
    (Z).loc ((Z).raw h t)=(Z).loc ((Z).raw ((C₀).src t.val) (srcFace t)) :=rfl


end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

-- Premise selection traverses the expanded chronological signatures during export.
-- The filter here applies only while exporting this module.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun current =>
    ["original_shelf_read", "original_launch_row", "original_address_both"] ++ current

end OAI
