import OAI.Hierarchy.DescentDatedTicketSocketCore
import OAI.Hierarchy.DescentDatedSelectedPublicOperand
import OAI.Hierarchy.DescentDatedPostedParentNumbers

namespace OAI
/-! Fields 7 and 6 of the actual returned job are the peer and first serial
at the donated physical slot of its surviving normalized operand. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
attribute [local irreducible] BitDescription.scannedRows
set_option maxRecDepth 12000
set_option maxHeartbeats 900000
set_option cleanup.letToHave false
open scoped Fin.CommRing
open DescentDatedAddressBook DescentPackedOperand DescentOperandStateBanks

private theorem four_number_equality (input : ℕ×ℕ) (numbers : ℕ→ℕ→ℕ→ℕ→ℕ×ℕ)
    (x₁ s₁ h₁ g₁ x₂ s₂ h₂ g₂ : ℕ) (first : input=numbers x₁ s₁ h₁ g₁)
    (x : x₂=x₁) (s : s₂=s₁) (h : h₂=h₁) (g : g₂=g₁) : input=numbers x₂ s₂ h₂ g₂ := by
  cases x
  cases s
  cases h
  cases g
  exact first

private theorem donated_role_flatten {paths blocks slots : ℕ} (path : Fin paths)
    (block : Fin blocks) (slot : Fin slots) (tag : Fin 11) :
    (finProdFinEquiv (path,DescentDatedOperandCoordinates.Ticket.seatNo (block,slot,tag))).val =
      (finProdFinEquiv (path,finProdFinEquiv (finProdFinEquiv (block,slot),tag))).val := by
  simp only [DescentDatedOperandCoordinates.Ticket.seatNo,finProdFinEquiv_apply_val]
  ring


/-- The result at a fixed occupied node and argument, for any dependent family of reached incident
edges with their chunk and fit certificate. The registered first-cable reader, receiver, and
donor rows all observe the same signed slot. -/
private theorem returned_pointer_on_named_use {N U Raw Path : Type*} {A E : N → Type*}
    (nodeOf : U → N) (argOf : ∀ u, A (nodeOf u)) (chunk : U → ℕ)
    (read : ∀ x, A x → E x → Prop) (side : ∀ x, E x → Bool)
    (target : ∀ x, E x → Pointer) (wire : U → Raw → Prop) (visits : Raw → Path → Prop)
    (locator : U → Bool → Option SignedDrawing.Slot) (arrived : N → SignedDrawing.Slot → Prop)
    (mark : Raw → Bool) (peer first : Raw → Path → ℕ) (numbers : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ)
    {w : ℕ} (grain : ℕ) (x : N) (j : A x) (edge : E x) (hit : read x j edge)
    (registered : ∃ u, nodeOf u=x ∧ HEq (argOf u) j ∧
      ∀ bits cut : Cell (w+2), bits.val=chunk u → cut.val=grain →
        ∃ entry : SignedDrawing.Slot, locator u (side x edge)=some entry ∧
        let pair:=numbers entry.block entry.role entry.host entry.group
        Pointer.ofKey 0 (resolve (Public.fragment entry.marked pair.1 pair.2 bits cut))=target x edge)
    (receiverAt : ∀ u (e:E (nodeOf u)), read (nodeOf u) (argOf u) e →
      ∀ entry, locator u (side (nodeOf u) e)=some entry → arrived (nodeOf u) entry)
    (donorAt : ∀ u s raw path, wire u raw → visits raw path →
      ∀ entry, locator u s=some entry → arrived x entry →
      entry.marked=mark raw ∧ (peer raw path,first raw path)=numbers entry.block entry.role entry.host entry.group) :
    ∃ u, nodeOf u=x ∧ HEq (argOf u) j ∧
      ∀ raw, wire u raw → ∀ path, visits raw path → ∀ bits cut : Cell (w+2),
        bits.val=chunk u → cut.val=grain →
        Pointer.ofKey 0 (resolve (Public.fragment (mark raw) (peer raw path) (first raw path) bits cut))=target x edge := by
  obtain ⟨u,hx,hi,found⟩:=registered
  cases hx
  cases eq_of_heq hi
  refine ⟨u,rfl,HEq.rfl,?_⟩
  intro raw atWire path atPath bits cut hb hc
  obtain ⟨entry,located,ptr⟩:=found bits cut hb hc
  have atReceiver:=receiverAt u edge hit entry located
  obtain ⟨marked,numerals⟩:=donorAt u _ raw path atWire atPath entry located atReceiver
  exact (congrArg₂ (fun (b : Bool) (q : ℕ × ℕ) =>
    Pointer.ofKey 0 (resolve (Public.fragment b (q.1 : Cell (w+2)) (q.2 : Cell (w+2)) bits cut)))
    marked.symm numerals).trans ptr

variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
set_option hygiene false in
local notation "phys" => v.withIssuedSigned
set_option hygiene false in
local notation "S" => v.schedule
set_option hygiene false in
local notation "G" => v.gadget
set_option hygiene false in
local notation "A" => v.prior.placement
set_option hygiene false in
local notation "T" => (A).stage
set_option hygiene false in
local notation "D" => (A).degree
set_option hygiene false in
local notation "r" => 2^v.k
set_option hygiene false in
local notation "J" => (S).groupCount v.age
set_option hygiene false in
local notation "M" => (phys).material.oldLanes
set_option hygiene false in
local notation "H" => v.area.H
set_option hygiene false in
local notation "ss" => (phys).signed
set_option hygiene false in
local notation "native" => v.prior.order.trans Fin.valEmbedding
set_option hygiene false in
local notation "rank" => groupRank Fin.valEmbedding (v.prior.vertex.trans Fin.valEmbedding)
set_option hygiene false in
local notation "grp" => Equiv.refl (Fin J)
set_option hygiene false in
local notation "peers" => rotor A rank
set_option hygiene false in
local notation "home" => scanHomeAt v.nonnegative T
set_option hygiene false in
local notation "color" => scanColorAt v.nonnegative T
set_option hygiene false in
local notation "addr" => nativeAddress v.nonnegative T
set_option hygiene false in
local notation "rr" => BitDescription.scannedRows v.nonnegative T
set_option hygiene false in
local notation "K" => 2^(v.k+1)
set_option hygiene false in
local notation "s" => shape r D (2*(A).cap) v.profile
set_option hygiene false in
local notation "traffic" => nativeTraffic v.world.graph v.world.core home
set_option hygiene false in
local notation "fmt" => v.ticket.depotShape v.short
variable (oldFit:Fintype.card v.prior.V≤H) (R:Fin H→Fin D→Option (Fin H))
set_option hygiene false in
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
variable (selected:((T).result v.nonnegative).Choice)
set_option hygiene false in
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)

open DescentHaloPackedRebase DescentSharedCableNames
variable (B:v.SelectedBoard oldFit R selected m parts)
variable (choiceEq:HEq selected v.choice) (wide:Fintype.card v.target.V≤ (ss).hosts)
variable (age:v.age<(S).length) (radix:(S).radix=r) (bands:J=(ss).groups*r)
variable (reciprocal:∀v u j,R v j=some u→∃l,R u l=some v)
set_option hygiene false in
local notation "chart" => v.issuedSignedChart
set_option hygiene false in
local notation "pitch" => (phys).materialPitch
set_option hygiene false in
local notation "paths" => (ss).reach
set_option hygiene false in
local notation "space" => v.signedLayout.field_room.1
set_option hygiene false in
local notation "oldStates" => B.material
set_option hygiene false in
local notation "markedBits" => (phys).markBits chart oldFit bands.symm R
open DescentBundleHistory DescentPackedOperand DescentOperandStateBanks Computability.BorderVNP.Crossing
attribute [local irreducible] WorldShape.follow WorldShape.selected WorldShape.transport OrdinaryModel.publicBooks
attribute [local irreducible] selectedModelPresentation selectedLocator
set_option hygiene false in
local notation "info" => v.selectedModelPresentation oldFit R selected m parts B choiceEq wide age radix reciprocal
set_option hygiene false in
local notation "mod₀" => (info).model
set_option hygiene false in
local notation "world₁" => ((mod₀).named v.nonnegative T selected v.prior.order).result
variable {p kinds : ℕ} (arch : Archive v.world) (hp : 0<p) (one : 1≤kinds) (pin : ∀x,p∣v.bits x)
    (sh : WorldShape p kinds arch.bit) (unit : p∣(T).z)
set_option hygiene false in
local notation "Use" => OrdinaryModel.PublicUse v.nonnegative T selected v.prior.order mod₀ arch hp one pin sh unit
set_option hygiene false in
local notation "node" => OrdinaryModel.PublicNode v.nonnegative T selected v.prior.order mod₀ arch
set_option hygiene false in
local notation "slotIndex" => OrdinaryModel.PublicArg v.nonnegative T selected v.prior.order mod₀ arch hp one pin sh unit
set_option hygiene false in
local notation "observed" => OrdinaryModel.publicOperand v.nonnegative T selected v.prior.order mod₀ arch hp one pin sh unit


set_option hygiene false in
local notation "sheet" => v.selectedLocator oldFit R selected m parts B choiceEq wide age radix reciprocal arch hp one pin sh unit

open DescentDatedOperandCoordinates DescentDatedOperandReadPipeline DescentOperandPriorIncidence
set_option hygiene false in
local notation "ℒ" => (phys).resolver
set_option hygiene false in
local notation "E" => (phys).material
set_option hygiene false in
local notation "Γ" => (phys).ticketReadGeometry
set_option hygiene false in
local notation "pos₀" => DescentSharedCableNames.Stage.Positive A
set_option hygiene false in
local notation "cells" => breadth D*DepotRAM.Material.roles fmt
variable (bl : (ℒ).blocks=(E).blocks) (hb : (ℒ).hosts≤(E).hosts) (gs : (ℒ).groups=(E).groups)
variable (orig : Fin (ℒ).jobs→Fin 6→Values Γ (phys).operandShortBits)
    (priorHead : Fin (ℒ).jobs→Fin 4→Values Γ ((ℒ).size+2)) (born : Fin (ℒ).jobs→Fin 3→Values Γ (phys).bornBook.bits)
set_option hygiene false in
local notation "serial" => v.retainedSerial oldFit R selected m parts B choiceEq wide age radix bands reciprocal
set_option hygiene false in
local notation "peer" => v.retainedPeer oldFit R selected m parts B choiceEq wide age radix bands reciprocal
set_option hygiene false in
local notation "grid₀" => (phys).sampleHeads bl hb gs orig priorHead born
  ((phys).wideMaterialValues R B.material bands serial peer) ((phys).narrowValue R)
set_option hygiene false in
local notation "data" => (phys).originalValues grid₀
variable (j : Fin (ℒ).jobs) (h : Fin (ℒ).hosts) (y : Fin (ℒ).groups)
set_option hygiene false in
local notation "x₀" => (phys).receiverBlock bl j
set_option hygiene false in
local notation "h₀" => h.castLE hb
set_option hygiene false in
local notation "y₀" => y.cast gs

theorem returned_W_digits (row : Fin cells) :
    (((data).raw j 7 row h y).val,((data).raw j 6 row h y).val)=
      (info).numbers (x₀).val ((phys).parentSlot chart row).val (h₀).val (y₀).val :=by
  refine (congrArg₂ Prod.mk ((phys).original_raw_number grid₀ j 7 row h y) ((phys).original_raw_number grid₀ j 6 row h y)).trans ?_
  change ((peer x₀ row h₀ y₀).val,(serial x₀ row h₀ y₀).val)=_
  exact v.retained_numbers oldFit R selected m parts B choiceEq wide age radix bands reciprocal x₀ row h₀ y₀


set_option hygiene false in
local notation "rawType" => DescentRawCablePanel.Live A (rr).pick
set_option hygiene false in
local notation "anchor₀" raw:arg => (⟨anchor (rr).pick (raw).val,(raw).property⟩ : pos₀)
set_option hygiene false in
local notation "src₀" raw:arg => v.world.graph.src (anchor₀ raw).val
set_option hygiene false in
local notation "seat" raw:arg => ((A).block (src₀ raw),DescentSharedCableNames.Stage.outgoing A native S v.prior.valid
    (anchor₀ raw),DescentCableDonorNames.role (raw).val)
set_option hygiene false in
local notation "row" path:arg raw:arg => finProdFinEquiv (path,Ticket.seatNo (seat raw))
set_option hygiene false in
local notation "cutCore" raw:arg => DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role (raw).val)
  (decide ((anchor₀ raw).val∈v.world.core))

set_option hygiene false in
local notation "rawWire" => DescentRawCablePanel.Live A (rr).pick
set_option hygiene false in
local notation "fromDonor" e:arg => v.world.graph.src (anchor (rr).pick (e).val)
set_option hygiene false in
local notation "zAt" e:arg => DescentRawCablePanel.shortSlot A S v.prior.valid native hosts (rr).pick e



/-- The two literal input fields and the recorded mark at this actual
donor socket all agree with the selected input's normalized signed read. -/
theorem donated_W_digits (use : Use) (side : Bool) (raw : rawType) (source : raw.val=use.cable.val)
    (entry : SignedDrawing.Slot) (located : sheet use side=some entry)
    (receiver : Fin H) (route : DepotRAM.Material.Route.receiver H pitch h₀=some receiver)
    (path : Fin (breadth D)) (visits : Gather.select (Gather.reaching R) receiver path=some (hosts ((A).pos (src₀ raw)).2))
    (block : entry.block=(x₀).val) (host : entry.host=(h₀).val) (group : entry.group=(y₀).val) :
    entry.marked=cutCore raw ∧
    (((data).raw j 7 (row path raw) h y).val,((data).raw j 6 (row path raw) h y).val)=
      (info).numbers entry.block entry.role entry.host entry.group :=by
  constructor
  · have marked := v.selected_donated_mark oldFit R selected m parts B choiceEq wide age radix reciprocal
      arch hp one pin sh unit use side entry located
    simpa only [source] using marked
  · have registered := v.selected_donated_role oldFit R selected m parts B choiceEq wide age radix reciprocal
      arch hp one pin sh unit use side raw source entry located h₀ host receiver route path visits
    have physical : ((phys).parentSlot chart (row path raw)).val = (finProdFinEquiv (path,(zAt raw).2)).val :=
      @donated_role_flatten (breadth D) (2^v.k) (A).cap path ((A).block (src₀ raw))
        (DescentSharedCableNames.Stage.outgoing A native S v.prior.valid (anchor₀ raw)) (DescentCableDonorNames.role raw.val)
    exact four_number_equality (((data).raw j 7 (row path raw) h y).val,((data).raw j 6 (row path raw) h y).val)
      (info).numbers (x₀).val ((phys).parentSlot chart (row path raw)).val (h₀).val (y₀).val
      entry.block entry.role entry.host entry.group
      (v.returned_W_digits (B:=B) (choiceEq:=choiceEq) (wide:=wide) (age:=age) (radix:=radix)
        (bands:=bands) (reciprocal:=reciprocal) (bl:=bl) (hb:=hb) (gs:=gs) (orig:=orig) (priorHead:=priorHead)
        (born:=born) (j:=j) (h:=h) (y:=y) («row»:=row path raw)) block (registered.trans physical.symm) host group

/-- At every surviving external cable of the normalized archive, resolving
the actual four-field physical job yields the precise reached pointer. -/
theorem returned_public_pointer (x : node) (arg : slotIndex x) (edge : Incident (world₁).graph x.1)
    (lo : ℕ) (fit : (lo+1)*p≤(world₁).graph.width edge.val) (hit : observed x arg=.inl ⟨.inl edge,lo,fit⟩)
    (wireFit : v.target.placement.cap≤2^(ss).fieldBits) (peerFit : v.target.placement.degree≤2^(ss).fieldBits)
    (wireWide : v.target.placement.cap≤2^((ℒ).size+2)) (peerWide : v.target.placement.degree≤2^((ℒ).size+2))
    (recv : Fin H) (atHost : DepotRAM.Material.Route.receiver H pitch h₀=some recv)
    (vHost : (v.target.vertex (v.target.placement.pos (Reached.originalSite (info).same x.1)).2).val=(h₀).val)
    (vBand : (v.target.placement.pos (Reached.originalSite (info).same x.1)).1.val=(y₀).val)
    (vBlock : (v.target.placement.block (Reached.originalSite (info).same x.1)).val=(x₀).val) :
    ∃use : Use,use.node=x ∧ HEq use.arg arg ∧
      ∀(raw : rawType),raw.val=use.cable.val→∀(path : Fin (breadth D)),
        Gather.select (Gather.reaching R) recv path=some (hosts ((A).pos (src₀ raw)).2)→
        ∀bitsIn cut : Cell ((ℒ).size+2),bitsIn.val=use.chunk→cut.val=(T).z/p→
        Pointer.ofKey 0 (resolve (Public.fragment (cutCore raw)
          (((data).raw j 7 (row path raw) h y).val:Cell ((ℒ).size+2))
          (((data).raw j 6 (row path raw) h y).val:Cell ((ℒ).size+2)) bitsIn cut))=
          v.target.firstCable hp (Reached.originalSite (info).same x.1) (Reached.originalIncident (info).same x.1 edge)
            lo (Reached.original_fit (info).same x.1 edge lo fit) :=by
  let Ed (xn : node) := Σ en : Incident (world₁).graph xn.1, { ln : ℕ // (ln+1)*p≤(world₁).graph.width en.val }
  let occupied (xn : node) (jn : slotIndex xn) (en : Ed xn) : Prop :=
    observed xn jn=.inl ⟨.inl en.1,en.2.val,en.2.property⟩
  let face (xn : node) (en : Ed xn) := decide ((world₁).graph.src en.1.val≠xn.1)
  let pointer (xn : node) (en : Ed xn) := v.target.firstCable hp (Reached.originalSite (info).same xn.1)
    (Reached.originalIncident (info).same xn.1 en.1) en.2.val (Reached.original_fit (info).same xn.1 en.1 en.2.val en.2.property)
  let reached (xn : node) (sl : SignedDrawing.Slot) : Prop :=
    let site:=Reached.originalSite (info).same xn.1
    sl.host=(v.target.vertex (v.target.placement.pos site).2).val ∧ sl.group=(v.target.placement.pos site).1.val ∧
      sl.block=(v.target.placement.block site).val
  let en : Ed x := ⟨edge,⟨lo,fit⟩⟩
  refine returned_pointer_on_named_use (N:=node) (U:=Use) (Raw:=rawType) (Path:=Fin (breadth D))
    («A»:=fun xn => slotIndex xn) («E»:=Ed) (fun u => u.node) (fun u => u.arg) (fun u => u.chunk)
    occupied face pointer (fun u raw => raw.val=u.cable.val)
    (fun raw path => Gather.select (Gather.reaching R) recv path=some (hosts ((A).pos (src₀ raw)).2))
    sheet reached (fun raw => cutCore raw)
    (fun raw path => ((data).raw j 7 (row path raw) h y).val)
    (fun raw path => ((data).raw j 6 (row path raw) h y).val)
    (info).numbers (w:=(ℒ).size) ((T).z/p) x arg en hit ?_ ?_ ?_
  · exact v.selected_firstCable oldFit R selected m parts B choiceEq wide age radix reciprocal
      arch hp one pin sh unit x arg edge lo fit hit wireFit peerFit wireWide peerWide
  · intro u e readHere sl seen
    exact v.selected_donated_receiver oldFit R selected m parts B choiceEq wide age radix reciprocal
      arch hp one pin sh unit u e.1 e.2.val e.2.property readHere sl seen
  · intro u side raw path atWire atPath sl seen coords
    exact v.donated_W_digits oldFit R selected m parts B choiceEq wide age radix bands reciprocal
      arch hp one pin sh unit bl hb gs orig priorHead born j h y u side raw atWire sl seen recv atHost path atPath
      (coords.2.2.trans vBlock) (coords.1.trans vHost) (coords.2.1.trans vBand)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

-- The expanded signatures below exceed the premise-search indexing budget during export.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun current =>
    ["donated_W_digits", "returned_public_pointer"] ++ current

end OAI
