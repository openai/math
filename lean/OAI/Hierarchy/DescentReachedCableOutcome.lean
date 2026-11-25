import OAI.Hierarchy.DescentReachedPointerCases
import OAI.Hierarchy.DescentDatedPublicGrain
import OAI.Hierarchy.DescentOrdinarySignedMeta
import OAI.Hierarchy.DescentOrdinaryResidentMark
import OAI.Hierarchy.DescentIssuedChartAgreement
import OAI.Hierarchy.DescentIssuedDonors

namespace OAI
/-! The native cable ticket on an incident positive grain, through both quotients. -/
namespace Hierarchy.DescentLocalArchiveOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
    (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣T.z)
attribute [local irreducible] BitDescription.scannedRows
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>T.z
local notation "pos" => fun _ : (r).pairs=>T.unitPos
local notation "room" => fun _ : (r).pairs=>le_refl T.z
local notation "prof" => (r).profile c
local notation "sel" => scanWorld he T c
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "b" => privateChart ticket arch hp one pin sh unit
local notation "addr" => MarkedWorld.address sel ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ)
local notation "group" => GadgetNetwork.newSite W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack
local notation "loc" => addr ∘ group
local notation "M" => rawGraph he T c
local notation "next" => (ticket.advance arch).bit
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni room prof
local notation "source" => operandSource ticket arch
local notation:max "sourceSite" x:arg => (source x).1
local notation:max "equalHome" e:arg => loc ((M).src (e).val)=loc ((M).dst (e).val)
open DescentHaloCompilation DescentSIMDLookup
variable {H degree:ℕ} (name:cap.V↪Fin H) (roster:Fin H→Fin degree→Option (Fin H))
    (listed:∀a t,t∈cap.placement.near a→∃i,roster (name a) i=some (name t))
local notation "A" => cap.placement
local notation "oldName" => (DescentPacking.originalId ((T.result he).state c).graph.Site) ∘ rawInput he T c ((r).state c)

local notation "newName" => rawOwner he T c n ((r).state c) (DescentPacking.originalId _)
local notation:max "mark₀" e:arg => DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role (e).val)
  (decide (DescentCableDonorNames.anchor (r).pick (e).val∈W.core))

/-- The primitive register equation with its literal rack, donor slot, role and parent-wire ordinal. -/
def CableTicket (x:NodeOrder.All next) (e:Incident (M) (sourceSite x)) (piece:ℕ)
    (full:(piece+1)*p≤(M).width e.val) (physical:DescentHostDirectory.Key (Fin (S.groupCount i)×cap.V))
    (key fall:DescentPackedOperand.Key) : Prop :=
  let site:=W.graph.src (DescentCableDonorNames.anchor (r).pick e.val)
  let live:=DescentPrivateRawLabels.parent_positive cap.placement S cap.valid (r).pick uni pos (r).fit prof hp
    (⟨e.val,piece,((Nat.le_div_iff_mul_le hp).mpr full)⟩:WireWord (M) p)
  let old:=DescentSharedCableNames.Stage.outgoing cap.placement (cap.order.trans Fin.valEmbedding) S cap.valid
    ⟨DescentCableDonorNames.anchor (r).pick e.val,live⟩
  ∃mem:site∈DescentOrdinaryDonorHalo.siteSet (DescentHostDirectory.groupedNear (A).near) (A).pos physical,
    let donor:=((shared (A).near name roster listed (A).pos (A).block cap.valid.coordinates).slot physical ⟨site,mem⟩).val
    let label:=11*old.val+(DescentCableDonorNames.role e.val).val
    let first:=decide (oldName ((M).src e.val)=oldName ((M).dst e.val))
    let final_:=decide (newName ((M).src e.val)=newName ((M).dst e.val))
    key=if first then Key.first donor 0 label piece else if !first && final_ then Key.second donor 0 label piece else fall

/-- The public fallback stores the measured peer/serial and the dated grain size. -/
def CableOutcome (x:NodeOrder.All next) (_j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (e:Incident (M) (sourceSite x)) (piece:ℕ) (full:(piece+1)*p≤(M).width e.val)
    (key:DescentPackedOperand.Key) : Prop :=
  ∃(physical:DescentHostDirectory.Key (Fin (S.groupCount i)×cap.V)) (size:ℕ)
    (peer start grain:Cell (size+2)) (fit:piece<2^(size+2)),
    physical.1=(((b).key he T c) (group ((M).src e.val))).1 ∧
    CableTicket ticket arch hp name roster listed x e piece full physical key
      (resolve (Public.fragment (mark₀ e) peer start ⟨piece,fit⟩ grain))

namespace CableOutcome
variable {ticket arch hp one pin sh unit name roster listed}
variable {x:NodeOrder.All (ticket.advance arch).bit}
    {j:Fin ((((afterOrdinary hp one pin ticket arch sh unit).sites x.1).recipe hp).arity x.2)}
    {e:Incident (rawGraph he T c) (operandSource ticket arch x).1} {piece:ℕ}
    {full:(piece+1)*p≤(rawGraph he T c).width e.val} {key:DescentPackedOperand.Key}

theorem of_source (physical:DescentHostDirectory.Key (Fin (S.groupCount i)×cap.V))
    (aligned:physical.1=(((b).key he T c) (group ((M).src e.val))).1)
    {size:ℕ} (peer start grain:Cell (size+2)) (fit:piece<2^(size+2))
    (read:CableTicket ticket arch hp name roster listed x e piece full physical key
      (resolve (Public.fragment (mark₀ e) peer start ⟨piece,fit⟩ grain))) :
    CableOutcome ticket arch hp one pin sh unit name roster listed x j e piece full key :=
  ⟨physical,size,peer,start,grain,fit,aligned,read⟩

theorem captured (out:CableOutcome ticket arch hp one pin sh unit name roster listed x j e piece full key)
    (same:equalHome e) :
    key=DescentOrdinaryNativeNames.captures (receivedRoot ticket arch hp one pin sh unit name roster listed x.1)
      (captureLabel ticket arch hp one pin sh unit (fun _ _=>0) (sourceSite x) e piece full same) :=by
  obtain ⟨physical,size,peer,start,grain,fit,aligned,read⟩:=out
  exact observed_capture_at ticket arch hp one pin sh unit name roster listed x j e piece full same key _
    physical aligned read

theorem survivor (out:CableOutcome ticket arch hp one pin sh unit name roster listed x j e piece full key)
    (different:¬equalHome e) :
    ∃near serial within,key=DescentPackedOperand.Key.cable near serial within :=by
  obtain ⟨physical,size,peer,start,grain,fit,aligned,read⟩:=out
  obtain ⟨mem,issued⟩:=read
  have owners:=source_owners ticket arch hp one pin sh unit ((M).src e.val) ((M).dst e.val)
  have separate:oldName ((M).src e.val)≠oldName ((M).dst e.val):=fun h=>different (congrArg (addr) (owners.1.mp h))
  have survives:newName ((M).src e.val)≠newName ((M).dst e.val):=fun h=>different (owners.2.mp h)
  have publicRead:key=resolve (Public.fragment (mark₀ e) peer start ⟨piece,fit⟩ grain):=by
    simpa only [decide_eq_false separate, decide_eq_false survives, Bool.not_false, Bool.true_and,
      Bool.false_eq_true, ite_false] using issued
  have limbs:=DescentDatedPublicGrain.resolve_public (⟨piece,fit⟩:Cell (size+2)) peer start grain
  cases markEq:mark₀ e with
  | false => rw [markEq] at publicRead; exact ⟨_,_,_,publicRead.trans limbs.2⟩
  | true => rw [markEq] at publicRead; exact ⟨_,_,_,publicRead.trans limbs.1⟩

end CableOutcome

section Dated
local notation "T₀" => cap.placement.stage
variable {choice:(cap.placement.stage.result he).Choice} {norm:Normalize ((cap.placement.stage.result he).state choice)}
    {dest:Reached norm.result G q ε S k (i+1) z' D' wire hist}
    (receipt:OrdinaryLink cap he cap.placement.stage choice norm dest) (alignedGrains:p∣cap.placement.stage.z)
local notation "rr" => BitDescription.scannedRows he T₀
local notation "units" => fun _:(rr).pairs=>(T₀).z
local notation "layout₀" => bestLayout (branchWidth G units ((rr).profile choice))
local notation "M₀" => rawGraph he T₀ choice
local notation "site₀" => GadgetNetwork.newSite W.graph (rr).pick layout₀ (rr).pack
local notation "owner₀" => StarKeys.nativeKey W.graph W.core (scanHomeAt he T₀) (scanColorAt he T₀)
    (T₀).cap (nativeAddress he T₀) receipt.donorChart.same layout₀
local notation "pchart" => privateChart receipt arch hp one pin sh alignedGrains
local notation "fieldShape" => afterOrdinary hp one pin receipt arch sh alignedGrains
local notation "source₀" => operandSource receipt arch

/-- The actual ordinary date uses the native colony address at the selected sender. -/
theorem CableOutcome.dated_rack (v:(M₀).Site) :
    (owner₀ (site₀ v)).1=(((pchart).key he T₀ choice) (site₀ v)).1 :=by
  exact congrArg (fun key => (key (site₀ v)).1)
    (IssuedDonorChart.native_key he T₀ choice pchart receipt.donorChart.same).symm

/-- Feed the measured ticket directly into both quotient branches, at the physical source from
the date's signed roster. Its rack agreement follows from the scanned placement. -/
theorem CableOutcome.of_dated {x:NodeOrder.All (receipt.advance arch).bit}
    {j:Fin ((((fieldShape).sites x.1).recipe hp).arity x.2)} {e:Incident (M₀) (source₀ x).1}
    {piece:ℕ} {full:(piece+1)*p≤(M₀).width e.val} {key:DescentPackedOperand.Key}
    {size:ℕ} (peer start grain:Cell (size+2)) (fit:piece<2^(size+2))
    (read:CableTicket receipt arch hp name roster listed x e piece full (owner₀ (site₀ ((M₀).src e.val))) key
      (resolve (Public.fragment (DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role e.val)
        (decide (DescentCableDonorNames.anchor (rr).pick e.val∈W.core))) peer start ⟨piece,fit⟩ grain))) :
    CableOutcome receipt arch hp one pin sh alignedGrains name roster listed x j e piece full key :=
  CableOutcome.of_source _ (CableOutcome.dated_rack arch hp one pin sh receipt alignedGrains _) peer start grain fit read

end Dated

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
