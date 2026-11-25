import OAI.Hierarchy.DescentRegisteredEntryAddress
import OAI.Hierarchy.DescentDatedRootSourceAddress
import OAI.Hierarchy.DescentDatedMouthRate
import OAI.Hierarchy.DescentDatedMouthBounds

namespace OAI
/-! The genuine registered reference reservation, from ingress to the eight selector results,
has one linear address exponent on ordinary dates with varying original pin types. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentSIMDLookup DescentDatedOperandReadPipeline DescentHaloWalkRAM Filter
noncomputable section
set_option quotPrecheck false
variable {ι : ℕ→Type*} {F : Type} [Field F] {Pin : ∀h,ι h→Type}
    (v : ∀h (i : ι h),PhysicalOrdinary F (Pin h i)) (prior : ∀h,ι h→DatePorts) (floor : ∀h,ι h→ℕ)
local notation "ex_" => fun h i=>(v h i).argumentUnitFrom (prior h i) (floor h i)
local notation "W_" => fun h i=>(v h i).registeredFrom (prior h i) (floor h i)
local notation "L_" => fun h i=>((W_) h i).resolver
local notation "R_" => fun h i=>((W_) h i).reference
local notation "B_" => fun h i=>((W_) h i).bornBook
local notation "working_" => fun h i=>((v h i).fundedClip ((ex_) h i)).working

structure ReferenceAddressInputs : Prop where
  entry : EntryAddressInputs v prior floor
  material : MaterialExtent.ScalarRoom (fun h i=>((W_) h i).material)
  resolver : DescentDatedPriorOperand.Layout.ScalarRoom L_
  degree : Bounded (fun h i=>(v h i).area.D)
  radix : Bounded (fun h i=>2^(v h i).area.k)
  cap : Bounded (fun h i=>(v h i).reference.capacity)
  oldNodes : Bounded (fun h i=>(v h i).reference.oldNodes)
  host : Bounded (fun h i=>(v h i).vector.hosts)
  birthHost : Bounded (fun h i=>(v h i).bornBook.hosts)
  grouping : ∀h i,((B_) h i).groups=(v h i).vector.groups*2^(v h i).area.k
  payload : ∀ᶠ h in atTop,∀i,(v h i).payload≤h
  signed : ∀h i,((W_) h i).signed=((W_) h i).signedLayout.format ((W_) h i).payload
  /-- The broadcast has one sentinel row even at zero lanes. -/
  digits : Linear (fun h i=>((W_) h i).operandShortBits)

theorem registered_reference_rate (inputs : ReferenceAddressInputs v prior floor) :
    Bounded (fun h i=>((W_) h i).referenceWords) :=by
  let cst:=fun n=>Bounded.const (ι:=ι) n
  have shape (h) (i : ι h):=(v h i).registered_width (prior h i) (floor h i)
  have key {x : ∀h,ι h→ℕ} (bought : ∀h i,x h i≤(v h i).payload) : Linear x :=by
    refine ⟨1,inputs.payload.mono ?_⟩
    intro h high i
    simpa only [Nat.one_mul] using (bought h i).trans (high i)
  have refKey : Linear (fun h i=>((R_) h i).width):=key (fun h i=>((shape h i).1 4).trans (Nat.div_le_self ..))
  have oldKey : Linear (fun h i=>((R_) h i).digitBits):=key (fun h i=>((shape h i).1 5).trans (Nat.div_le_self ..))
  have bornKey : Linear (fun h i=>(((B_) h i).chipBits*1+((B_) h i).chipBits)*((B_) h i).lanes):=
    key (fun h i=>((shape h i).1 6).trans (Nat.div_le_self ..))
  have acquired (h) (i : ι h) := (v h i).mouth_purchase ((ex_) h i) ((v h i).datedEntry (prior h i) (floor h i))
  have rootKey : Linear (fun h i=>(((B_) h i).bits*((L_) h i).nodes)*((L_) h i).lanes):=by
    apply key
    intro h i
    have small : ((B_) h i).bits*((L_) h i).nodes ≤ (ex_) h i :=
      ((Nat.le_max_right ..).trans (acquired h i)).trans (Nat.le_max_left _ _)
    exact ((v h i).funded_extra_fit ((ex_) h i) (((B_) h i).bits*((L_) h i).nodes) small).2.2.trans (Nat.div_le_self ..)
  have source:=(root_source_rate W_ inputs.material inputs.resolver inputs.degree
    (key (fun _ _=>le_rfl)) inputs.signed rootKey
    (key (fun h i=>(shape h i).2.trans (Nat.div_le_self ..))) inputs.digits)
  have origin:=origin_mouth_rate v ex_ (by
    apply Eventually.of_forall
    intro h i
    let x:=v h i
    let e:=(ex_) h i
    let ent:=x.datedEntry (prior h i) (floor h i)
    exact ⟨inputs.grouping h i,(acquired h i).trans (Nat.le_max_left ..),
      (x.argumentWidth_le ent e 11).trans (Nat.le_max_left ..)⟩)
    inputs.host inputs.birthHost inputs.resolver.groups inputs.entry.sites inputs.resolver.nodes
    inputs.resolver.arities inputs.cap inputs.radix inputs.resolver.lanes inputs.payload
  have donors:=((inputs.degree.add (cst 1)).pow 4).mul inputs.radix
  have count:=(cst 3).add (donors.mul (inputs.oldNodes.add (inputs.cap.mul (cst 6))))
  have refs : Bounded (fun h i=>((R_) h i).extent):=
    (inputs.oldNodes.mul oldKey.table).add ((count.mul (cst 2)).mul refKey.table)
  have cols:=((((inputs.radix.mul inputs.cap).mul (cst 6)).mul inputs.resolver.arities).mul (cst 7))
  have birthGroups : Bounded (fun h i=>((B_) h i).groups):=(inputs.resolver.groups.mul inputs.radix).of_le
    (fun h i=>(inputs.grouping h i).le)
  have birthRows:=inputs.birthHost.mul (birthGroups.chunks inputs.entry.clip.receiving)
  have born : Bounded (fun h i=>((B_) h i).endAddress 0):=
    ((cst 0).add (((cst 1).add cols).mul ((cst 2).mul bornKey.table))).add (cols.mul birthRows.padded)
  have span:=(inputs.resolver.hosts.mul (inputs.resolver.groups.chunks inputs.resolver.lanes)).padded
  have jobs:=inputs.resolver.blocks.mul (inputs.resolver.nodes.mul inputs.resolver.arities)
  have route:=(((origin.add source).add span).add ((jobs.mul (cst 8)).mul span))
  exact ((((registered_entry_address v prior floor inputs.entry).add refs).add born).add route)
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
