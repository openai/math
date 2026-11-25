import OAI.Hierarchy.DescentDatedSignedParentRun
import OAI.Hierarchy.DescentDatedSignedReturnRecords

namespace OAI
/-! The original two launch words measured in the narrow radix of the signed source-return query. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentSharedCableNames DescentHaloWalkRAM DescentHaloPackedRebase DescentParallelBase.ParentFilter
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DepotRAM.Material.Route DescentParallelBase
open scoped Classical Fin.CommRing
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "s" => v.signed
local notation "D" => DepotRAM.Shape.degree (v.ticket.depotShape v.short)
local notation "G" => v.material.groups
local notation "H" => v.material.oldHosts
local notation "M" => v.material.lanes
local notation "B" => v.material.blocks
variable (floor : ℕ) (c : v.SignedChart)
local notation "base" => v.donorEnd floor
local notation "mat" => PriorHeader.endAddress H G M D base
local notation "geo" => PriorHeader.rankBanks H G M D base
variable (hosts : v.material.oldHosts=v.signed.priorHosts)
    (sites : Projection.launchSites v.material.blocks v.materialPitch=v.signed.lowSites)
    (bands : v.material.oldGroups=v.material.groups*v.material.blocks)
    (R : Fin v.material.oldHosts→Fin (v.ticket.depotShape v.short).degree→Option (Fin v.material.oldHosts))
    (state : Fin v.material.oldHosts→Fin v.material.oldGroups→DepotRAM.Parts (v.ticket.depotShape v.short))
local notation "cal" => DepotRAM.Material.reverseEntries (v.ticket.depotShape v.short) R
local notation "reverse₀" => fun h (_:Fin v.material.oldGroups)=>digest (DepotRAM.Material.reverseEntries (v.ticket.depotShape v.short) R h)
def launchNumber (x : Fin (s).blocks) (o : Fin (s).residentSlots) (low : Bool) (h : Fin (s).priorHosts)
    (g : Fin (s).groups) : ℕ :=
  let f:Fin 9:=if low then 2 else 0
  (DepotRAM.Material.Sheets.fields fmt v.materialFormat state reverse₀
    (DepotRAM.Material.Sheets.id fmt f (c.donorSeat o)) (Fin.cast hosts.symm h)
    (Fin.cast bands.symm (finProdFinEquiv (g,Fin.cast c.blocks x)))).val
def originalDigits : (s).RouteDigits :=
  let f (x o h g):Cell (Packed.bits (s).reach):=v.launchNumber c hosts bands R state x o false h g
  let l (x o h g):Cell (Packed.bits (s).lowSites):=v.launchNumber c hosts bands R state x o true h g
  ⟨f,l,fun x o h g=>SourceReturn.Query.packedRoute (rerouted hosts c.degree.symm R) h
    (Packed.readToken _ (f x o h g))⟩

theorem original_back (x o h g) :
    (v.originalDigits c hosts bands R state).back x o h g=
    SourceReturn.Query.packedRoute (rerouted hosts c.degree.symm R) h
      (Packed.readToken _ ((v.originalDigits c hosts bands R state).forward x o h g)):=rfl

private theorem sourceHost {A newHosts a groups lanes w : ℕ} (same : A=newHosts) (q : Expr) (m : Memory w)
    (x : Fin A→Fin groups→Cell a) (known : Source q x lanes m) :
    Source q (fun h g=>x (Fin.cast same.symm h) g) lanes m:=by subst newHosts;exact known

private theorem sourceWidth {hosts groups lanes a b w : ℕ} (same : a=b) (q : Expr) (m : Memory w)
    (values : Fin hosts→Fin groups→ℕ) (seen : Source q (fun h g=>(values h g : Cell a)) lanes m) :
    Source q (fun h g=>(values h g : Cell b)) lanes m := by subst b; exact seen

include sites in
theorem original_earlier {w : ℕ} (parts adj : Bank) (pre : PriorHeader.Room adj H G M D base w)
    (paid : v.MaterialRoom mat parts (geo).reverseRank w) (previous : parts.base+parts.size≤base)
    (pos : 0<(e).oldLanes) (hm : 0<M) (hb : 0<B) (grows : H≤(e).hosts) (m after : Memory w)
    (neighbors : ∀h j,m (adj.base+h.val*D+j.val)=(number (R h j):Word w))
    (board : Reads parts (fun h g=>DepotRAM.combine fmt (state h g)) (e).oldLanes m)
    (keep : ∀a<v.materialEnd floor,after a=(v.beforeSignedMaterial floor parts adj w).image m a) :
    (v.originalDigits c hosts bands R state).Earlier (v.signedInput floor c) after:=by
  let first:=PriorHeader.phase H G M D base adj w
  let run:=first.image m
  have head:=PriorHeader.any H G M D base adj pre m
  have old : Reads parts (fun h g=>DepotRAM.combine fmt (state h g)) (e).oldLanes run:=by
    intro p
    rw [show run=PriorHeader.image H G M D base adj m from PriorHeader.phase_image ..]
    refine (head.2 _ (Or.inl ?_)).trans (board p)
    exact (Nat.add_lt_add_left ((row H (e).oldGroups (e).oldLanes p).isLt.trans_le paid.sourceSize) _).trans_le previous
  have ranks : DescentOrdinaryDonorRankDirectory.Reads R geo run:=by
    rw [show run=PriorHeader.image H G M D base adj m from PriorHeader.phase_image ..]
    exact PriorHeader.directory base adj pre m R neighbors
  have addr : v.materialStart floor=mat:=congrArg (fun degree₀=>PriorHeader.endAddress H G M degree₀ base) c.degree
  have roof:v.materialEnd floor=(e).endAddress mat:=congrArg (e).endAddress addr
  have emit (x : Fin (s).blocks) (o : Fin (s).residentSlots) (low : Bool) :
      Source (v.originSocket (v.materialStart floor) (c.donorSeat o) (Fin.cast c.blocks x) low)
        (fun h g=>(v.launchNumber c hosts bands R state x o low h g:
          Cell (Projection.launchWidth (e).reach B v.materialPitch low))) M after :=by
    let z:=c.donorSeat o
    let b':=Fin.cast c.blocks x
    let f:Fin 9:=if low then 2 else 0
    let j:=DepotRAM.Material.Sheets.id fmt f z
    have bank:=v.received_fit mat ((e).endAddress mat) w le_rfl paid.range hm hb bands grows j
    have n:=v.material_origin_issued paid run R state pos hm hb bands ranks.reverse old z b' low
      ((e).endAddress mat) bank.1 bank.2 le_rfl paid.range
    have safe:=v.origin_socket_fits mat ((e).endAddress mat) w le_rfl paid.range hm hb bands grows z b' low
    rw [addr]
    let vals (h : Fin H) (g : Fin G) : Cell (Projection.launchWidth (e).reach B v.materialPitch low) :=
      (DepotRAM.Material.Sheets.fields fmt v.materialFormat state reverse₀ j h
        (Fin.cast bands.symm (finProdFinEquiv (g,b')))).val
    apply sourceHost hosts (v.originSocket mat z b' low) after vals
    intro p
    refine (ProtocolRAM.eval_below (v.originSocket mat z b' low) _ _ after safe ?_).trans (n p)
    intro a below
    rw [←roof] at below
    rw [keep a below,v.material_to_issued parts adj floor c.degree]
    rfl
  constructor
  · intro x o;exact emit x o false
  · intro x o
    have width : Projection.launchWidth (e).reach B v.materialPitch true = Packed.bits (s).lowSites :=
      congrArg Packed.bits sites
    exact sourceWidth width _ after (v.launchNumber c hosts bands R state x o true) (emit x o true)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
