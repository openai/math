import OAI.Hierarchy.DescentOrdinarySignedEmission
import OAI.Hierarchy.DescentOrdinaryOriginalMarkBits
import OAI.Hierarchy.DescentDatedSignedDrawing
import OAI.Hierarchy.DescentDatedSignedNumbers
import OAI.Hierarchy.DescentDatedOriginalMarkKnown
import OAI.Hierarchy.DescentDatedOriginalSiteAddress
import OAI.Hierarchy.DescentOrdinaryPaddedParentGather

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.SignedDrawing
open DescentSixParty DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentHaloWalkRAM DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F Pin U : Type} [Field F] [Fintype U] [DecidableEq U]
  {d H prior degree Q O K L b groups k age : ℕ} {bits : Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ} {A:GroupStage W G price ε (Fin groups) U k}
  {native:W.graph.Edge↪ℕ} {R:Fin prior→Fin degree→Option (Fin prior)}
  {symm:∀u v j,R u j=some v→∃n,R v n=some u} {host:U↪Fin H} {pitch:ℕ}
  {space:Fused.capacity degree Q K L≤2^b}
  {before:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Option (Fused.Raw R Q K L b)}
  {parent:Fin (2^k)→Fin O→Fin prior→Fin groups→Option (ParentFilter.Source (breadth degree) Q K L)}
  {marks:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Cell 1}
variable (d₀:SignedDrawing A native R symm host pitch space before parent marks)
    (S:DescentCompiler.AtomSchedule) (ready:A.StateBounds S age)

variable (capacity : A.cap=L)


private def reindexDrawing
    {before' : Fin (2^k) → Fin (breadth degree*O) → Fin H → Fin groups → Option (Fused.Raw R Q K L b)}
    {parent' : Fin (2^k) → Fin O → Fin prior → Fin groups → Option (ParentFilter.Source (breadth degree) Q K L)}
    (sameInput : before' = before) (sameParent : parent' = parent) :
    { drawing : SignedDrawing A native R symm host pitch space before' parent' marks //
      drawing.numbered S ready capacity = d₀.numbered S ready capacity ∧ HEq drawing d₀ } := by
  subst before' parent'
  exact ⟨d₀,rfl,HEq.rfl⟩


end
end Hierarchy.DescentDatedAddressBook.SignedDrawing

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
local notation "peers" => rotor A rank
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
local notation "Z" => originalMeasurement ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal
local notation "shelf" => originalShelf ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal
local notation "O" => 2^k*(A).cap*11
local notation "shortAddr" => shortSlot A S prior.valid native hosts (rr).pick
local notation:max "band" h:arg => (groups').symm ((h).1.1,(h).2)
local notation "orig" => originalRecord ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth pitch fieldBits

open DescentDatedAddressBook DescentRawCablePanel.DepotRAM.Material.Route
variable {newH:ℕ} (hostRoom:Fintype.card next.V≤newH)
local notation "newHost" => next.vertex.trans (Fin.castLEEmb hostRoom)
local notation "who" => SignedExtent.wholeHost (Equiv.refl (Fin (S.groupCount (i+1)))).toEmbedding newHost
variable (groupPositive:0<S.groupCount i)
include mounted reciprocal groupPositive in
private theorem old_closed (v u:Fin H) (a:Fin (A).degree) (past:Fintype.card V≤v.val) (step:roster v a=some u) :
    Fintype.card V≤u.val:=by
  by_contra! within
  have onto:=((Fintype.bijective_iff_injective_and_card prior.vertex).2 ⟨prior.vertex.injective,by simp⟩).2
  obtain ⟨old,found⟩:=onto ⟨u.val,within⟩
  have sameValue := congrArg Fin.val found
  have write : hosts old = u := Fin.ext sameValue
  obtain ⟨back,at_⟩:=reciprocal v u a step
  let g:J:=⟨0,groupPositive⟩
  rw [←write,mounted (g,old) back] at at_
  cases peer:peers (g,old) back with
  | none=>simp [peer] at at_
  | some dest=>
    have equal:hosts dest.2=v:=Option.some.inj (by simpa only [peer,Option.map_some] using at_)
    exact Nat.not_lt_of_ge past ((congrArg Fin.val equal) ▸ (prior.vertex dest.2).isLt)

local notation "received" => DescentRawCablePanel.DepotRAM.Material.Route.fromDonor
local notation "lowRead" => original_shelf_read ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal
variable (space :
    let stage := prior.placement.stage
    let sourceCount := 2^(stage.k+1)*(2^(packExponent 20 stage.Δ)+2)
    let localRoles := DepotRAM.Material.roles
      (Stage.shapeOf (short:=short) prior.placement (donorNameBits stage.k stage.Δ))
    Fused.capacity prior.placement.degree sourceCount
      ((breadth prior.placement.degree+1)*localRoles) next.placement.cap≤2^fieldBits)
private theorem witnessPitchPositive (level width : ℕ) : 0 < (2^(level+1)-1)*(width+2) :=
  Nat.mul_pos (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.zero_lt_succ level).ne')) (Nat.succ_pos _)
private theorem witnessCapacity {D Q₁ K ids L bits : ℕ} (address : ids = K)
    (budget : Fused.capacity D Q₁ ids L ≤ 2^bits) : Fused.capacity D Q₁ K L ≤ 2^bits :=
  address ▸ budget

local notation "pitchPos" => witnessPitchPositive ((T).k) (2^(packExponent 20 (T).Δ))
local notation "pitchBound" => Nat.mul_le_mul_right slots (Nat.sub_le (2^((T).k+1)) 1)
local notation:max "fetch" o:arg => fun (physicalRack:Fin H) (physicalGroup:Fin (S.groupCount (i+1)*2^k)) =>
  orig physicalRack ((groups').symm (finProdFinEquiv.symm physicalGroup)) (splitSeat (k:=k) (cap:=(A).cap) o)

private theorem receiverFromOrdinal {newRackCount oldRackCount localSlotCount pitch₀ : ℕ}
    (positive : 0 < pitch₀) (host₀ : Fin newRackCount) (place : Fin oldRackCount × Fin localSlotCount)
    (ordinal : host₀.val = place.1.val * pitch₀ + place.2.val)
    (low : place.2.val < pitch₀) :
    DescentRawCablePanel.DepotRAM.Material.Route.receiver oldRackCount pitch₀ host₀ = some place.1 ∧ place.2.val = host₀.val % pitch₀ := by
  have divided : host₀.val / pitch₀ = place.1.val := by
    rw [ordinal, Nat.mul_comm _ pitch₀, Nat.mul_add_div positive, Nat.div_eq_of_lt low, Nat.add_zero]
  constructor
  · unfold DescentRawCablePanel.DepotRAM.Material.Route.receiver
    rw [dite_eq_left ⟨positive, divided ▸ place.1.isLt⟩]
    exact congrArg some (Fin.ext divided)
  · rw [ordinal, Nat.mul_add_mod_of_lt low]

private theorem fetchedBlankAt {Index SeatQ Result : Type} (entry : Index → SeatQ → Option Result)
    (grp₀ : Index) (seat₀ : SeatQ) (position : Index × SeatQ) (value : Option Result)
    (fetchedAt : value = entry grp₀ seat₀) (decoded : position = (grp₀,seat₀))
    (blankAt : entry position.1 position.2 = none) : value = none :=
  fetchedAt.trans ((congrArg (fun pair : Index × SeatQ => entry pair.1 pair.2) decoded.symm).trans blankAt)

set_option maxHeartbeats 180000 in
/-- The eligible raw data in the prior material fetch is precisely the signed parent shelf,
including all inherited bytes outside the genuine target host roster. -/
theorem original_incoming
    (small:∀h p raw (s:Source P₀ Q K₀ next.placement.cap) f,Machine.fields roster ((Z).venue h) p ((Z).loc raw).1 s f<2^fieldBits)
    (x:Fin (2^k)) (p:Fin P₀) (o:Fin O) (h:Fin newH) (g:Fin (S.groupCount (i+1))) :
    received roster pitch pitchPos pitchBound space p x (fetch o) h g =
      Fused.cell C₀ roster Z shelf small (who x) (finProdFinEquiv (p,o)) h g :=by
  let rseat := splitSeat (k:=k) (cap:=(A).cap) o
  let groupsAt := (groups').symm (g,x)
  have fetched (v : Fin H) :
      (fetch o) v (finProdFinEquiv (g,x)) = orig v groupsAt rseat :=
    congrArg (fun pair => orig v ((groups').symm pair) rseat)
      (finProdFinEquiv.symm_apply_apply (g,x))
  apply original_shelf C₀ roster Z shelf small rfl pitch pitchPos pitchBound space p o x (fetch o) (who x) h g
  ·
    intro u some_
    have seen := (SignedExtent.wholeHost_iff (Equiv.refl (Fin (S.groupCount (i+1)))).toEmbedding
      newHost x h g u).mp some_
    have ordinal : h.val = (ticket.parentVenue port.enough u.1.2).1.val*pitch+
        (ticket.parentVenue port.enough u.1.2).2.val := (congrArg Fin.val seen.2.1).symm.trans
          (ticket.parentVenue_ordinal port.enough u.1.2)
    exact receiverFromOrdinal pitchPos h (ticket.parentVenue port.enough u.1.2) ordinal
      (ticket.parentVenue_low port.enough u.1.2)
  ·
    intro u some_ d
    have foundHost := (SignedExtent.wholeHost_iff (Equiv.refl (Fin (S.groupCount (i+1)))).toEmbedding
      newHost x h g u).mp some_
    have sameGroup : (g,x) = (u.1.1,u.2) := Prod.ext foundHost.1.symm foundHost.2.2.symm
    exact (fetched d).trans ((congrArg (fun pair => orig d ((groups').symm pair) rseat) sameGroup).trans
      (lowRead u d o).symm)
  ·
    intro hole v sourceHit d pick_
    let map':next.V≃Fin (Fintype.card next.V):=Equiv.ofBijective next.vertex
      ((Fintype.bijective_iff_injective_and_card _).2 ⟨next.vertex.injective,by simp⟩)
    have past:=SignedExtent.padded_receiver (n:=Fintype.card V) (Equiv.refl _) map' hostRoom
      (show Fintype.card next.V=Fintype.card V*pitch by
        change Fintype.card next.V = Fintype.card V * ((2^(k+1)-1)*(2^packExponent 20 prior.placement.degree+2))
        simpa only [Nat.mul_assoc] using ticket.hostCount)
      pitchPos x h g hole sourceHit
    have old:=SignedExtent.closed_donor roster (old_closed port roster mounted reciprocal (Nat.zero_lt_of_lt (((groups').symm (g,x)).isLt))) v d past p pick_
    let j:=fullSeat ((groups').symm (g,x)) (splitSeat (k:=k) (cap:=(A).cap) o)
    have blank:=originalRecord_padded (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted
      birth pitch fieldBits d j old
    have result := fetchedBlankAt (orig d) groupsAt rseat
      (groupSeat (G:=S.groupCount i) (r:=2^k) (cap:=(A).cap) j) ((fetch o) d (finProdFinEquiv (g,x))) (fetched d)
      (fullSeat_read groupsAt rseat) blank
    exact result

local notation "originalMarks" => port.originalMarks newH roster age radix
local notation "delivered" => fun (issueBlock:Fin (2^k)) (columnIndex:Fin (P₀*O)) =>
  received roster pitch pitchPos pitchBound space ((finProdFinEquiv.symm columnIndex : Fin P₀ × Fin O).1) issueBlock
    (fetch ((finProdFinEquiv.symm columnIndex : Fin P₀ × Fin O).2))
local notation "launch" => fun (x:Fin (2^k)) (o:Fin O) (u:Fin H) (g:Fin (S.groupCount (i+1))) =>
  orig u ((groups').symm (g,x)) (splitSeat o)


set_option maxHeartbeats 1800000 in
set_option hygiene false in
include ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal hostRoom space in
/-- The actual survivor measurement, both prior endpoints and all original received
cells give the complete signed input on the chronological next (world). -/
def actualModelDrawing : SignedDrawing A₁ (originalId (world).graph.Edge) roster reciprocal
    newHost pitch space delivered launch originalMarks :=by
  let observedHere := Z
  let fieldRoom := fun h p a (u:Source P₀ Q K₀ next.placement.cap) f=>
    Fused.field_room roster (observedHere.venue h) p (observedHere.loc a).1 u f space
  refine {
    «edge» := _
    «finiteEdge» := inferInstance
    «raw» := _
    «finiteRaw» := inferInstance
    «ticket» := _
    «finiteTicket» := inferInstance
    «site» := _
    «blocks» := C₀
    «core» := _
    «emission» := DescentOrdinaryWindowFields.signedEmission W G prior.order pairNo (rr).pick
      (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z
      oldCut chosenCut stageCut B.site A₁ (T).unitPos
    «observed» := observedHere
    «shelf» := shelf
    «order» := original_incidence_orders (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
      dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal
    «coordinate» := fun u=>ticket.parentVenue_ordinal port.enough u.1.2
    «low» := fun u=>ticket.parentVenue_low port.enough u.1.2
    «address» := original_address_both (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
      dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal
    «input» := ?_
    «launch» := ?_
    «mark» := ?_
  }
  ·
    intro x j
    let coords : Fin P₀ × Fin O := finProdFinEquiv.symm j
    exact funext fun h => funext fun g =>
      (original_incoming (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m
        sumSize stored dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal
        hostRoom space fieldRoom x coords.1 coords.2 h g).trans
        (congrArg (fun index : Fin (P₀*O) => Fused.cell C₀ roster observedHere shelf fieldRoom (who x) index h g)
          (finProdFinEquiv.apply_symm_apply j))
  ·
    intro x h g t got e
    have seenAt := (SignedExtent.wholeHost_iff (Equiv.refl (Fin (S.groupCount (i+1)))).toEmbedding newHost x h g t).mp got
    have groupEq : t.1.1=g := seenAt.1
    have blockEq : t.2=x := seenAt.2.2
    let launchAddr : Fin H × Fin O := (Z).loc ((Z).raw t e)
    have pairEq : (g,x)=(t.1.1,t.2) := Prod.ext groupEq.symm blockEq.symm
    have forward := congrArg (fun coordinate : Fin (S.groupCount (i+1)) × Fin (2^k) =>
      orig launchAddr.1 ((groups').symm coordinate) (splitSeat (k:=k) (cap:=(A).cap) launchAddr.2))
      pairEq
    exact forward.trans (original_launch_row (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
      dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal t e)
  ·
    exact fun x j h g t got e selected => original_mark_known (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster
      mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal hostRoom x j h g t got e selected

local notation "diagram" => actualModelDrawing ticket port win hm named fit winner df order profile b m sumSize stored
  dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal hostRoom space

set_option maxHeartbeats 1800000 in
theorem actualModelDrawing_blocks : (diagram).blocks=C₀ := rfl
set_option maxHeartbeats 1800000 in
theorem actualModelDrawing_measured : (diagram).observed=Z := rfl
set_option maxHeartbeats 1800000 in
theorem actualModelDrawing_units : (diagram).emission.units =
    (DescentOrdinaryWindowFields.signedEmission W G prior.order pairNo (rr).pick
      (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z
      oldCut chosenCut stageCut B.site A₁ (T).unitPos).units :=rfl

include ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal hostRoom space in
set_option maxHeartbeats 1800000 in
def namedModelDrawing : SignedDrawing next.placement (next.order.trans Fin.valEmbedding) roster reciprocal
    newHost pitch space delivered launch originalMarks :=
  SignedDrawing.named next.placement (next.order.trans Fin.valEmbedding) roster reciprocal newHost pitch space
    delivered launch originalMarks coh (Function.Embedding.ext fun e=>next.edgeName (Nat.succ_pos i) e) diagram

include ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom space in
set_option maxHeartbeats 1800000 in
theorem namedModelDrawing_heq :
    HEq (namedModelDrawing ticket port win hm named fit winner df order profile b m sumSize stored
      dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal hostRoom space)
      (diagram) :=by
  apply SignedDrawing.named_heq

set_option maxHeartbeats 1800000 in
theorem namedModelDrawing_numbers :
    (namedModelDrawing ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal hostRoom space).numbered S next.valid rfl =
    (diagram).numbered S (model_bounds («next»:=next) B coh) (model_shape («next»:=next) B coh).1 := by
  exact SignedDrawing.named_numbers
    («A»:=next.placement) («native»:=next.order.trans Fin.valEmbedding) («R»:=roster)
    («symm»:=reciprocal) («host»:=newHost) («pitch»:=pitch) («space»:=space)
    («before»:=delivered) («parent»:=launch) («marks»:=originalMarks)
    («S»:=S) («ready»:=next.valid) («capacity»:=rfl) («eqn»:=coh)
    («chronology»:=Function.Embedding.ext fun e=>next.edgeName (Nat.succ_pos i) e)
    («drawing»:=diagram) (model_bounds («next»:=next) B coh) (model_shape («next»:=next) B coh).1


include ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom space in
set_option maxHeartbeats 1800000 in
def originalDrawingData : SignedDrawing next.placement (next.order.trans Fin.valEmbedding) roster reciprocal
    newHost pitch space delivered launch originalMarks :=
  let picked:=parent_model ticket port age radix
  let B:=picked.choose
  let modelWorld:=picked.choose_spec.2.2
  namedModelDrawing ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster
    mounted birth fieldBits age radix B modelWorld.choose modelWorld.choose_spec.1
    pathWidth ticketWidth reciprocal hostRoom space

include pathWidth ticketWidth in
set_option maxHeartbeats 1800000 in
/-- The original stage retains the diagram constructed on the model
selected by the actual ordinary normalization certificate. -/
theorem originalDrawingData_numbers :
    let chosen:=parent_model ticket port age radix
    let coherent:=chosen.choose_spec.2.2
    (originalDrawingData ticket port win hm named fit winner df order profile b m sumSize stored
      dest issued roster mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom space).numbered S next.valid rfl=
      (actualModelDrawing ticket port win hm named fit winner df order profile b m sumSize stored
        dest issued roster mounted birth fieldBits age radix chosen.choose coherent.choose coherent.choose_spec.1
        pathWidth ticketWidth reciprocal hostRoom space).numbered S (model_bounds (next:=next) chosen.choose coherent.choose)
        (model_shape (next:=next) chosen.choose coherent.choose).1 :=
  let picked := parent_model ticket port age radix
  let model := picked.choose
  let coherence := picked.choose_spec.2.2
  namedModelDrawing_numbers (prior := prior) (short := short) (w := w) («a» := a)
    ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster
    mounted birth fieldBits age radix model coherence.choose coherence.choose_spec.1
    pathWidth ticketWidth reciprocal hostRoom space

include pathWidth ticketWidth in
set_option maxHeartbeats 1800000 in
theorem originalDrawingData_heq :
    let chosen:=parent_model ticket port age radix
    let coherent:=chosen.choose_spec.2.2
    HEq (originalDrawingData ticket port win hm named fit winner df order profile b m sumSize stored
      dest issued roster mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom space)
      (actualModelDrawing ticket port win hm named fit winner df order profile b m sumSize stored
        dest issued roster mounted birth fieldBits age radix chosen.choose coherent.choose coherent.choose_spec.1
        pathWidth ticketWidth reciprocal hostRoom space) :=
  let picked := parent_model ticket port age radix
  let model := picked.choose
  let coherence := picked.choose_spec.2.2
  namedModelDrawing_heq (prior := prior) (short := short) (w := w) («a» := a)
    ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster
    mounted birth fieldBits age radix model coherence.choose coherence.choose_spec.1
    pathWidth ticketWidth reciprocal hostRoom space

include ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted
  birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom space in
set_option maxHeartbeats 1800000 in
theorem originalDrawing : Nonempty (SignedDrawing next.placement (next.order.trans Fin.valEmbedding) roster reciprocal
    newHost pitch space delivered launch originalMarks) :=by
  exact ⟨originalDrawingData ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster
    mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom space⟩


include pathWidth ticketWidth in
set_option maxHeartbeats 750000 in
/-- The public dated source numbers its parent tickets with the left-associated
slot count. Its original group digit and original short seat address use the
same scalar retained board as the mathematical grouping. -/
def originalDrawingAtWitness (ids:ℕ) (eqIds:ids=K₀)
    (bands:S.groupCount i=S.groupCount (i+1)*2^k)
    (budget:Fused.capacity (A).degree Q ids next.placement.cap≤2^fieldBits) :
    (bound : ∀h g z,DepotRAM.Material.ParentRoom fmt form (measured h g) (rev h) z Q ids next.placement.cap) →
      let seatAt:=fun o:Fin O=>(DepotRAM.Material.seatIndex fmt).symm
        (Fin.cast (show O=DepotRAM.Material.roles fmt by exact Nat.mul_assoc _ _ _) o)
      let rowAt:=fun o:Fin O=>fun h (g:Fin (S.groupCount (i+1)*2^k))=>
        DepotRAM.Material.parent fmt form (measured h (Fin.cast bands.symm g)) (rev h) (seatAt o) (bound h _ _)
      {D₀ : SignedDrawing next.placement (next.order.trans Fin.valEmbedding) roster reciprocal newHost pitch budget
        (fun x j=>received roster pitch pitchPos pitchBound budget (finProdFinEquiv.symm j).1 x (rowAt (finProdFinEquiv.symm j).2))
        (fun x o h g=>rowAt o h (finProdFinEquiv (g,x))) originalMarks // D₀.numbered S next.valid rfl=(originalDrawingData (prior:=prior) (short:=short) (w:=w) («a»:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster
      mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom (witnessCapacity eqIds budget)).numbered S next.valid rfl ∧ HEq D₀ (originalDrawingData (prior:=prior) (short:=short) (w:=w) («a»:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster
      mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom (witnessCapacity eqIds budget))} :=by
  subst ids
  intro bound
  dsimp only
  have groupDigit (y:Fin (S.groupCount (i+1)*2^k)) :
      Fin.cast bands.symm y=(groups').symm (finProdFinEquiv.symm y) :=by
    apply Fin.ext
    change y.val=(finProdFinEquiv (finProdFinEquiv.symm y)).val
    rw [Equiv.apply_symm_apply]
  have same (o:Fin O) (h:Fin H) (g:Fin (S.groupCount (i+1)*2^k)) :
      DepotRAM.Material.parent fmt form (measured h (Fin.cast bands.symm g)) (rev h)
        ((DepotRAM.Material.seatIndex fmt).symm (Fin.cast (show O=DepotRAM.Material.roles fmt by exact Nat.mul_assoc _ _ _) o))
        (roomAt h _ _)=orig h ((groups').symm (finProdFinEquiv.symm g)) (splitSeat o) :=by
    rw [groupDigit g,←splitSeat_eq (prior:=prior) (short:=short) o]
    rfl
  let old:=originalDrawingData (prior:=prior) (short:=short) (w:=w) («a»:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster
    mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom budget
  refine DescentDatedAddressBook.SignedDrawing.reindexDrawing old S next.valid rfl ?_ ?_
  · funext x j h g
    apply congrArg (fun source => received roster pitch pitchPos pitchBound budget
      (finProdFinEquiv.symm j).1 x source h g)
    funext site₀ group₀
    exact same (finProdFinEquiv.symm j).2 site₀ group₀
  · funext x o h g
    exact (same o h (finProdFinEquiv (g,x))).trans
      (congrArg (fun p₀ => orig h ((groups').symm p₀) (splitSeat o))
        (finProdFinEquiv.symm_apply_apply (g,x)))

include pathWidth ticketWidth in
set_option maxHeartbeats 900000 in
def originalDrawingAtData (ids:ℕ) (eqIds:ids=K₀)
    (bands:S.groupCount i=S.groupCount (i+1)*2^k)
    (budget:Fused.capacity (A).degree Q ids next.placement.cap≤2^fieldBits) :
    (bound : ∀h g z,DepotRAM.Material.ParentRoom fmt form (measured h g) (rev h) z Q ids next.placement.cap) →
      let seatAt:=fun o:Fin O=>(DepotRAM.Material.seatIndex fmt).symm
        (Fin.cast (show O=DepotRAM.Material.roles fmt by exact Nat.mul_assoc _ _ _) o)
      let rowAt:=fun o:Fin O=>fun h (g:Fin (S.groupCount (i+1)*2^k))=>
        DepotRAM.Material.parent fmt form (measured h (Fin.cast bands.symm g)) (rev h) (seatAt o) (bound h _ _)
      SignedDrawing next.placement (next.order.trans Fin.valEmbedding) roster reciprocal newHost pitch budget
        (fun x j=>received roster pitch pitchPos pitchBound budget (finProdFinEquiv.symm j).1 x (rowAt (finProdFinEquiv.symm j).2))
        (fun x o h g=>rowAt o h (finProdFinEquiv (g,x))) originalMarks :=fun bound=>(originalDrawingAtWitness (prior:=prior) (short:=short) (w:=w) («a»:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster
      mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom ids eqIds bands budget bound).val

include pathWidth ticketWidth in
set_option maxHeartbeats 900000 in
theorem originalDrawingAtData_heq (ids:ℕ) (eqIds:ids=K₀)
    (bands:S.groupCount i=S.groupCount (i+1)*2^k)
    (budget:Fused.capacity (A).degree Q ids next.placement.cap≤2^fieldBits)
    (bound:∀h g z,DepotRAM.Material.ParentRoom fmt form (measured h g) (rev h) z Q ids next.placement.cap) :
    HEq (originalDrawingAtData (prior:=prior) (short:=short) (w:=w) («a»:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued
      roster mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom ids eqIds bands budget bound)
      (originalDrawingData (prior:=prior) (short:=short) (w:=w) («a»:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued
        roster mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom (witnessCapacity eqIds budget)) :=
  (originalDrawingAtWitness (prior:=prior) (short:=short) (w:=w) («a»:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster
      mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom ids eqIds bands budget bound).property.2

include pathWidth ticketWidth in
set_option maxHeartbeats 900000 in
theorem originalDrawingAtData_numbers (ids:ℕ) (eqIds:ids=K₀)
    (bands:S.groupCount i=S.groupCount (i+1)*2^k)
    (budget:Fused.capacity (A).degree Q ids next.placement.cap≤2^fieldBits)
    (bound:∀h g z,DepotRAM.Material.ParentRoom fmt form (measured h g) (rev h) z Q ids next.placement.cap) :
    (originalDrawingAtData (prior:=prior) (short:=short) (w:=w) («a»:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued
      roster mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom ids eqIds bands budget bound).numbered S next.valid rfl=
      (originalDrawingData (prior:=prior) (short:=short) (w:=w) («a»:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued
        roster mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom (witnessCapacity eqIds budget)).numbered S next.valid rfl :=
  (originalDrawingAtWitness (prior:=prior) (short:=short) (w:=w) («a»:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster
      mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom ids eqIds bands budget bound).property.1

include ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted
  birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom in
set_option maxHeartbeats 900000 in
theorem originalDrawingAt (ids:ℕ) (eqIds:ids=K₀)
    (bands:S.groupCount i=S.groupCount (i+1)*2^k)
    (budget:Fused.capacity (A).degree Q ids next.placement.cap≤2^fieldBits) :
    ∃bound : ∀h g z,DepotRAM.Material.ParentRoom fmt form (measured h g) (rev h) z Q ids next.placement.cap,
      let seatAt:=fun o:Fin O=>(DepotRAM.Material.seatIndex fmt).symm
        (Fin.cast (show O=DepotRAM.Material.roles fmt by exact Nat.mul_assoc _ _ _) o)
      let rowAt:=fun o:Fin O=>fun h (g:Fin (S.groupCount (i+1)*2^k))=>
        DepotRAM.Material.parent fmt form (measured h (Fin.cast bands.symm g)) (rev h) (seatAt o) (bound h _ _)
      Nonempty (SignedDrawing next.placement (next.order.trans Fin.valEmbedding) roster reciprocal newHost pitch budget
        (fun x j=>received roster pitch pitchPos pitchBound budget (finProdFinEquiv.symm j).1 x (rowAt (finProdFinEquiv.symm j).2))
        (fun x o h g=>rowAt o h (finProdFinEquiv (g,x))) originalMarks) :=by
  subst ids
  exact ⟨roomAt, ⟨originalDrawingAtData (prior:=prior) (short:=short) (w:=w) («a»:=a) ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth fieldBits age radix pathWidth ticketWidth reciprocal hostRoom
    K₀ rfl bands budget roomAt⟩⟩


end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

-- Premise selection traverses the expanded chronological signatures during export.
-- The filter here applies only while exporting this module.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun current =>
    ["original_incoming", "actualModelDrawing_blocks", "actualModelDrawing_measured",
     "actualModelDrawing_units", "namedModelDrawing_heq", "namedModelDrawing_numbers",
     "originalDrawingData_numbers", "originalDrawingData_heq", "originalDrawing",
     "originalDrawingAtData_heq", "originalDrawingAtData_numbers", "originalDrawingAt"] ++ current

end OAI
