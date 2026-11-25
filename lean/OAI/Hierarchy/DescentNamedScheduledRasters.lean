import OAI.Hierarchy.DescentDatedHeldVenue
import OAI.Hierarchy.DescentNamedScheduledOriginalPreflight
import OAI.Hierarchy.DescentNamedPhysicalRaster
import OAI.Hierarchy.DescentTerminalReturnedRasters

namespace OAI
/-! # Reading the Book's physically scheduled old venue inputs on the final branch -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentMixedRouter Catalyst DescentInitialHost DescentExteriorReplay
open DescentTerminalPreflightSpace DescentTerminalFixedSlices DescentTerminalPrimitiveArena
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Routing CallPool
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable {F:Type} [Field F] {cp ar:ℕ} (X:Approximation F cp ar) (G:PoweredGadget F) (S:AtomSchedule)
  {k tail:ℕ} (baseGroups:S.baseGroups=2^tail) (radix:S.radix=2^k)
  (g p q drift:ℕ) (op:RotorSpec) (headerRows paidRows:ℕ)
local notation "spec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
local notation "ports" => Fintype.card (Port ar X.width)

open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentResetInvoice CorrectionBatch
variable {n deg : ℕ} (board : NonlinearExpanders.Graph n deg) (age f degree payload : ℕ)
  (ordinary : ℕ→Dated.Ordinary) (operandLanes primitiveLanes : ℕ)
  (previous : StageVenueTail.Date) (addr : ℕ→ℕ→Bank) (oldRoster : Bank) (floor : ℕ)
  (j r t base compact : ℕ) (tag : ℕ→Bool) (rotation : ℕ→ℕ) (A : Snapshots k) (roleBase : ℕ)
local notation "phase" => Phase.scheduled G S board k tail age p f g drift degree payload ordinary op
  operandLanes primitiveLanes previous addr oldRoster floor
local notation "output" => (phase).output
local notation "origin" => (phase).dateBase
local notation "s₀" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "dated" => PhysicalReset.scheduled G S board k tail age p f g drift degree payload ordinary op
  s₀ Z operandLanes primitiveLanes previous addr oldRoster floor
local notation "cal" => replayCalendar X S k tail j r A
local notation "early" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t ports
local notation "image₀" => DescentExteriorMatrixUpdate.Calendar.earlyImage S k tail base tag rotation j r t ports compact
local notation "slices" => (phase).stop early
local notation "packet" => (cal).packetEnd slices
local notation "shelf" => (spec).scanPages packet q
local notation "census" => (shelf).stop
local notation "D" => (output).venue.next
local notation "hw" => (output).receiver
local notation "H" => (spec).scalar.shops
local notation "bs" => (spec).scalar.blocks
local notation "blocks" => (rfl : bs=(hw).blocks)
local notation "paid" => fun x:Fin bs=>(output).terminalPaid origin x.val
local notation "actor" => fun x:Fin bs=>(output).terminalActor origin x.val
local notation "wing" => fun (x:Fin bs) (a:Fin (2*(spec).cap))=>(output).terminalWing origin x.val a.val
local notation "peer" => (output).terminalPeer origin
variable {w : ℕ} (room : scheduledPreflightStop X G S (tail:=tail) g p q drift op headerRows paidRows
  board age f degree payload ordinary operandLanes primitiveLanes previous addr oldRoster floor j r t base A < 2^w)
local notation "code" => originalPreflight X G S baseGroups radix g p q drift op headerRows paidRows
  j r t base compact tag rotation (phase) A blocks roleBase peer paid actor wing room
local notation "dst" => originalPreflightMemory X G S baseGroups radix g p q drift op headerRows paidRows
  j r t base compact tag rotation (phase) A blocks roleBase peer paid actor wing room
local notation "ticks" => originalPreflightClocks X G S (k:=k) (tail:=tail) g p q drift op headerRows paidRows j r t
  base (phase) A blocks peer paid actor wing room
local notation "colors" => DescentPrimitivePalette.colors G s₀ Z op
local notation "args" => NativeBranch.privateSlotCapacity G S drift
local notation "roleBits" => fun f:Fin 6=>DescentTerminalCombinedRole.width colors (max 8 (2^S.capGain))
  args p drift f*(S.epochPower^S.localTokenExponent)*(spec).groups

variable (last : age+1=S.length) (oldK : previous.k=k)
  (word : (preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)).maskBase (((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)).scanPages
    ((replayCalendar X S k tail j r A).packetEnd ((Phase.scheduled G S board k tail age p f g drift degree payload ordinary op
      operandLanes primitiveLanes previous addr oldRoster floor).stop
      (DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t (Fintype.card (Port ar X.width))))) q).stop)<2^w) (positive : 0<w) (alive : 0<(preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)).scalar.shops)
  (prev : ∀i<S.length,rotation i<base) (seed : compact+32*DescentExteriorShelf.span j r t (Fintype.card (Port ar X.width))≤base)
  (earlier : (PhysicalReset.scheduled G S board k tail age p f g drift degree payload ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) operandLanes primitiveLanes previous addr oldRoster floor).fullEnd floor≤(DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t (Fintype.card (Port ar X.width))))
  (signedPitch : (Phase.scheduled G S board k tail age p f g drift degree payload ordinary op
      operandLanes primitiveLanes previous addr oldRoster floor).output.venue.next.signedLanes=S.groupCount S.length)
  (rank : ∀t<S.length,∀b,A.compact t=some b→b.Fits w base)
  (roleEnd : roleBase+DescentTerminalRoleTables.count (fun f:Fin 6 => DescentTerminalCombinedRole.width (DescentPrimitivePalette.colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op) (max 8 (2^S.capGain))
    (NativeBranch.privateSlotCapacity G S drift) p drift f*(S.epochPower^S.localTokenExponent)*(preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)).groups)≤base)

section Selected
local notation "wireWidth" => S.epochPower^S.priceExponent
local notation "rate" => (1/((s₀:ℝ)*(wireWidth:ℝ)):ℝ)
local notation "err" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
variable {h C₀ R : ℕ} {he : 0≤(((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {hu : 0≤(1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)*((S.epochPower^S.priceExponent):ℝ)}
  {epoch : Epochs G hu he (h:=h) (C:=C₀) (Ht:=GroupStage.depthBound (atRound S.rounds) n f g)
    (t:=S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
  {c : (Epochs.finish G hu he epoch).Choice} (b : Branch X G S radix R epoch c) (hp : 0<p)
  (width : S.groupWidth k tail 0+k=j+(j+r))

open DescentSIMDLookup DescentPackedColony DescentColonies DescentTerminalLocalPortBook DescentTerminalGraphPositions
open DescentTerminalSiteShelves DescentTerminalVertexFields DescentTerminalPointerIssue
open DescentTerminalRoleTables DescentTerminalCombinedRole DescentSortedRoster DescentActorRaster
open DescentColonies.SplitRAM
open scoped Fin.CommRing
local notation "oldLimit" => (output).fullEnd origin
local notation "nodes_" => S.epochPower^S.localTokenExponent
local notation "nodeBits" => Nat.clog 2 (nodes_+1)
local notation "config_" => (⟨nodeBits,Nat.clog 2 (args+1),fun _=>DescentOperandWidth.recordBits G S k tail drift 3 p,some nodes_⟩:Widths)
local notation "pin_" => DescentExterior.terminalPin (S.groupWidth k tail 0+k) (S.groupWidth k tail S.length+k) (k*S.length)
local notation "public_" => DescentTerminalPointerDigits.publicCell (cap:=(spec).cap) (N:=nodes_) (A:=args)
  (d:=(spec).scalar.pointerBits) 3 q G.b (poolBatchCount (s₀*1) p) (k*S.length) (spec).groups config_
local notation "private_" => DescentTerminalPointerDigits.output (spec).cap nodes_ args 3 (spec).groups
  (spec).scalar.pointerBits (Nat.clog 2 (q+args+1)) q G.b (poolBatchCount (s₀*1) p) config_ pin_
local notation "roles" => DescentTerminalRoleTables.role roleBits ((phase).banks early) roleBase
local notation "arity_" => DescentTerminalRoleTables.arity roleBits ((phase).banks early) roleBase
local notation "matrix" => DescentExteriorMatrixUpdate.Calendar.stop S k tail base+S.length
local notation "ptr" => fun (f:Fin 4) (j:Fin (output).argumentSlots) (x:Fin bs) =>
  (output).terminalPointers origin f j (x.cast blocks)
local notation "old_" => DescentTerminalOperandRepack.padded (K:=args) ptr paid
local notation "chart_" => ((spec).pointerPages census matrix old_ wing).address (N:=nodes_)
variable (u:ResetVenue.Earlier) (m:Memory w)
local notation "entry" => (cal).memory slices census room ((phase).memory early (image₀ m))
local notation "prim_" => (spec).primitiveSnapshot (base:=census) (w:=w) (q:=q) (p:=p) (nd:=nodeBits)
  (nodes:=nodes_) (hidden:=args) («args»:=args) (oldPaid:=paid) («actor»:=actor) (first:=roles) (second:=arity_)
  (chart:=chart_) (f0:=public_) (f7:=private_) ((shelf).image entry)
local notation "grid" => b.target.placement
local notation "hosts_" => b.target.vertex.trans (Fin.castLEEmb b.target.valid.host)
local notation "capEq" => preflight_caps (tail:=tail) X G S b (geometryFormat G S k g p tail q drift op headerRows paidRows)
local notation "rasters_" => presented (capEq).1 (capEq).2.1 ((spec).rasters census peer wing)
local notation "masks" => Venue.actual grid (Function.Embedding.refl _) hosts_
local notation "slots_" => (output).venue.sources u ((output).fundedEnd origin)
local notation "at_" => (output).venue.venueStart ((output).fundedEnd origin)
local notation "io_" => (D).operands slots_ at_

private theorem roster_address {d d' c c' blockCount:ℕ} (hd:d=d') (hc:c=c') (v:Rasters d' blockCount c'):
    (presented hd hc v).roster=v.roster:=by subst d';subst c';rfl

private theorem wing_address {d d' c c' blockCount:ℕ} (hd:d=d') (hc:c=c') (peerBank:Bank)
    (ch:MaskAllocation.Channels blockCount) (get:ℕ→ℕ→Bank) (v:Fin blockCount) (t:Fin (2*c)):
    (presented hd hc (⟨peerBank,ch,fun x j=>get x.val j.val⟩:Rasters d' blockCount c')).wing v t=get v.val t.val:=by
  subst d';subst c';rfl

include last oldK in
/-- The hosted registers are precisely those returned by the original final
chronological reset. Its stage starts after native ingress. -/
theorem scheduled_held_venue {limit:ℕ} (input:(dated).DateInputs ((dated).stageStart floor) w)
    (endMemory:Memory w)
    (kept:(Chronology.DatePorts.reset (dated) ((dated).stageStart floor) input).held b.target limit endMemory) :
    stageVenue b.target b.target.valid.host
      ((D).operands ((output).venue.sources (PhysicalReset.FinalInputs.predecessor input) ((output).fundedEnd origin)) at_)
      (S.groupCount S.length) (D).paidBits limit (b.target.venueRoster b.target.valid.host) endMemory := by
  have shape:=PhysicalReset.scheduled_terminal_shape G S board k tail age p f g drift degree payload ordinary op
    s₀ Z operandLanes primitiveLanes previous addr oldRoster floor last oldK
  exact Chronology.DatePorts.held_venue_at _ b.target b.target.valid.host shape.2.1 shape.2.2.2.2 kept

include last oldK in
/-- The independently emitted live plane for each block survives the rest of the
last native event. The venue and the event use the same original RAM execution. -/
theorem scheduled_actor_words (input:(dated).DateInputs ((dated).stageStart floor) w)
    (final_:input.FinalInputs) (fit:final_.Room) {firstMemory fundedMemory endMemory:Memory w}
    (entered:input.throughOperandDate.Runs firstMemory fundedMemory)
    (stepped:(PhysicalReset.date final_).Runs firstMemory endMemory)
    (panels:∀x:DescentColonies.Block k,Reads (((D).transported
      ((output).venue.sources (PhysicalReset.FinalInputs.predecessor input) ((output).fundedEnd origin)) at_).alive x.val)
      (masks x) (S.groupCount S.length) (final_.venueImage fundedMemory)):
    ∀x:DescentColonies.Block k,Reads (actor x) (masks x) (S.groupCount S.length) endMemory:=by
  have preserve:=PhysicalReset.date_venue_below final_ fit entered stepped
  have shape:=PhysicalReset.scheduled_terminal_shape G S board k tail age p f g drift degree payload ordinary op
    s₀ Z operandLanes primitiveLanes previous addr oldRoster floor last oldK
  obtain ⟨kind,hostCount,groupCount,_,lanes⟩:=shape
  intro x pos
  have span:=(output).terminal_actor_room origin fit.successor.return_.roof
    (x.cast (congrArg (2^·) kind).symm)
  have dim:H*chunks (S.groupCount S.length) (S.groupCount S.length)≤(actor x).size:=by
    have bound := span.2
    change (dated).successor.venue.next.hosts *
      chunks (dated).successor.venue.next.groups (dated).successor.venue.next.lanes ≤ (actor x).size at bound
    rw [hostCount,groupCount,lanes] at bound
    exact bound
  have small: (row H (S.groupCount S.length) (S.groupCount S.length) pos).val<(actor x).size:=
    (row _ _ _ pos).isLt.trans_le dim
  exact (preserve _ ((Nat.add_lt_add_left small _).trans_le span.1)).trans (panels x pos)

include baseGroups last oldK word signedPitch roleEnd in
/-- The charged scheduled prefix emits the exact dictionary entry on the
attained primitive receiver. The argument digit is taken at the original row. -/
theorem scheduled_reference_digit {tags:ℕ} (afterDate:(dated).fullEnd floor≤base)
    (x:DescentColonies.Block k) (h:Fin H) (gg:Fin (spec).groups) (u:Fin nodes_) (j₀:Fin args)
    (hostWord:H≤2^w) (outputRoom:(Nat.clog 2 (q+args+1)*(nodes_*args))*(spec).groups≤w)
    (value:ℕ) (small:value<2^Nat.clog 2 (q+args+1))
    (actual:(decode 3 config_ pin_ (((spec).pointerPages census matrix old_ wing).source
      (N:=nodes_) (d:=(spec).scalar.pointerBits) prim_ x h) gg.val).argument q G.b
      (poolBatchCount (s₀*1) p) (finProdFinEquiv (u,j₀))=value) :
    venueField (cellAt (measured (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p)
      (groups:=(spec).groups) (MaskAllocation.shelf (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (p:=p) (groups:=(spec).groups) ((spec).channels census) 0) prim_ h) (finProdFinEquiv (gg,x)))
      (DescentTerminalVertexFields.nodeArg u j₀)=value := by
  have first := scheduled_base_le_early S k tail base j r t ports
  have next:early≤ slices:=by
    unfold Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop DescentTerminalSliceShelf.fence
      DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom DescentOperandStateBanks.guard
    simp only [Nat.add_assoc, Nat.le_add_right]
  obtain ⟨c₀,c₁,c₂,c₃,_⟩:=(cal).addresses slices census
  have below:slices≤packet:=c₀.trans (c₁.trans c₂)
  have lit:packet≤census:=Nat.le_add_right ..
  have horizon:census≤(spec).cohortEnd census:=(spec).cohort_le census
  have chart:=Phase.scheduled_layout G S board k tail age p f g drift degree payload ordinary op
    operandLanes primitiveLanes previous addr oldRoster floor last
  have datedEnd:oldLimit≤base:= ((output).terminal_order origin).2.1.trans
    (((output).terminal_order origin).2.2.trans (chart.2.2.2.2.2.le.trans afterDate))
  have reelRoom:base<2^w:=(first.trans (next.trans (below.trans (lit.trans c₃)))).trans_lt room
  have booked:=scheduled_scan_before X G S k g p tail q drift op headerRows paidRows j r A slices
    board age f degree payload ordinary s₀ Z operandLanes primitiveLanes previous addr oldRoster floor
    baseGroups last oldK (afterDate.trans (first.trans next)) room
  have toCohort:early≤(spec).cohortEnd census:=next.trans (below.trans (lit.trans horizon))
  have fitsMatrix:matrix+1≤(spec).cohortEnd census:=(show matrix+1≤early from Nat.le_add_right ..).trans toCohort
  have dateEnd_:(output).finalEnd origin≤(spec).cohortEnd census:=
    ((output).terminal_order origin).1.trans (datedEnd.trans (first.trans toCohort))
  have fieldBounds (f:Fin 4) (i:Fin (output).argumentSlots) (x:Fin bs):=
    (output).terminal_field_room origin (show (output).metadataEnd origin<2^w by
      rw [chart.2.2.2.2.2];exact afterDate.trans_lt reelRoom)
    (f.castLE (by decide : 4≤7)) i (x.cast blocks)
  have one:=Phase.scheduled_one G S board k tail age p f g drift degree payload ordinary op
    operandLanes primitiveLanes previous addr oldRoster floor last baseGroups signedPitch
  apply fixed_operand_digit (X:=X) (G:=G) (S:=S) (q:=q) (drift:=drift) (op:=op)
    (headerRows:=headerRows) (paidRows:=paidRows) («origin»:=census) (romBase:=packet) (w:=w)
    («peer»:=peer) («paid»:=paid) («actor»:=actor) (signed:=wing) («matrix»:=matrix) (roleBase:=roleBase)
    (rolePages:=(phase).banks early) («ptr»:=ptr) (m:=entry) (homes:=(cal).homes slices)
    booked.1 word fitsMatrix (fun j=>((phase).banks_before early j).trans (below.trans (lit.trans horizon)))
    (roleEnd.trans (first.trans toCohort)) (fun f j x=>(fieldBounds f j x).1.2.2.trans dateEnd_)
    ?_ booked.2.1 booked.2.2.1 x h gg u j₀ hostWord outputRoom value small actual
  intro f j x
  change S.hostSize S.length ≤ ((output).terminalField origin (f.castLE (by decide : 4 ≤ 7)) j (x.cast blocks)).size
  simpa only [chart.2.1,one,Nat.mul_one] using (fieldBounds f j x).2

open DescentBundleHistory DescentKernelHistory DescentEpochTagKeys
local notation "colors_" => DescentPrimitivePalette.colors G s₀ (S.grainAt G.b p 0) op
local notation "bound_" => max 8 (2^S.capGain)

include baseGroups last oldK word signedPitch roleEnd in
theorem scheduled_role_scan_fields (afterDate:(dated).fullEnd floor≤base)
    {Tag V : Type} {widthAt : V→ℕ} {r₀:BitRecipe Tag V widthAt} (dictionary:Codec Tag colors_)
    (shape:DescentBundleHistory.Shape p r₀) (u₀:r₀.Node) (maskBase:ℕ)
    (x:DescentColonies.Block k) (h₀:Fin H) (gg:Fin (spec).groups) (slot:Fin nodes_)
    (roleRoom:DescentTerminalCombinedRole.output colors_ bound_ args p drift*nodes_*(spec).groups≤w)
    (arityRoom:Nat.clog 2 (args+1)*nodes_*(spec).groups≤w)
    (marked:dictionary.fits (r₀.tag u₀)) (bounded:(shape.recipe hp).arity u₀≤args)
    (ready:Static (A:=bound_) (G:=args) (p:=p) (R:=drift) (N:=nodes_) (M:=(spec).groups)
      dictionary roles prim_ ∧ CountStatic (n:=colors_) (A:=bound_) (G:=args) (p:=p) (R:=drift)
      (N:=nodes_) (M:=(spec).groups) args arity_ prim_)
    («given»:Printed dictionary (DescentTerminalCombinedRole.fields (DescentTerminalCombinedRole.node (DescentTerminalCombinedRole.observed (n:=colors_) (A:=bound_) (G:=args)
      (p:=p) (R:=drift) (N:=nodes_) (M:=(spec).groups) roles prim_ ((finProdFinEquiv (x,h₀)).val:Computability.VPVNP.BurstRAM.Word w))
      gg slot)) (r₀.tag u₀) (shape.sliceFields u₀)) :
    let machine:=MaskAllocation.shelf (q:=q) (t:=DescentBundleTagKeys.capacity colors_ bound_ args p drift)
      («H»:=args) (N:=nodes_) (A:=args) (p:=p) (groups:=(spec).groups) ((spec).channels census) maskBase
    let cell:=cellAt (measured (q:=q) (t:=DescentBundleTagKeys.capacity colors_ bound_ args p drift)
      («H»:=args) (N:=nodes_) (A:=args) (w:=p) (groups:=(spec).groups) machine prim_ h₀) (finProdFinEquiv (gg,x))
    venueField cell (nodeRole slot)=((DescentBundleTagKeys.codec dictionary bound_ args p drift).store
      ((shape.recipe hp).tag u₀)).val+1 ∧ venueField cell (nodeArity slot)=(shape.recipe hp).arity u₀ :=by
  have first := scheduled_base_le_early S k tail base j r t ports
  have next:early≤ slices:=by
    unfold Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop DescentTerminalSliceShelf.fence
      DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom DescentOperandStateBanks.guard
    simp only [Nat.add_assoc, Nat.le_add_right]
  obtain ⟨c₀,c₁,c₂,c₃,_⟩:=(cal).addresses slices census
  have below:slices≤packet:=c₀.trans (c₁.trans c₂)
  have lit:packet≤census:=Nat.le_add_right ..
  have horizon:census≤(spec).cohortEnd census:=(spec).cohort_le census
  have chart:=Phase.scheduled_layout G S board k tail age p f g drift degree payload ordinary op
    operandLanes primitiveLanes previous addr oldRoster floor last
  have datedEnd:oldLimit≤base:= ((output).terminal_order origin).2.1.trans
    (((output).terminal_order origin).2.2.trans (chart.2.2.2.2.2.le.trans afterDate))
  have reelRoom:base<2^w:=(first.trans (next.trans (below.trans (lit.trans c₃)))).trans_lt room
  have booked:=scheduled_scan_before X G S k g p tail q drift op headerRows paidRows j r A slices
    board age f degree payload ordinary s₀ Z operandLanes primitiveLanes previous addr oldRoster floor
    baseGroups last oldK (afterDate.trans (first.trans next)) room
  have toCohort:early≤(spec).cohortEnd census:=next.trans (below.trans (lit.trans horizon))
  have fitsMatrix:matrix+1≤(spec).cohortEnd census:=(show matrix+1≤early from Nat.le_add_right ..).trans toCohort
  have dateEnd_:(output).finalEnd origin≤(spec).cohortEnd census:=
    ((output).terminal_order origin).1.trans (datedEnd.trans (first.trans toCohort))
  have fieldBounds (f:Fin 4) (i:Fin (output).argumentSlots) (x:Fin bs):=
    (output).terminal_field_room origin (show (output).metadataEnd origin<2^w by
      rw [chart.2.2.2.2.2];exact afterDate.trans_lt reelRoom)
    (f.castLE (by decide : 4≤7)) i (x.cast blocks)
  have one:=Phase.scheduled_one G S board k tail age p f g drift degree payload ordinary op
    operandLanes primitiveLanes previous addr oldRoster floor last baseGroups signedPitch
  apply fixed_role_scan_fields (X:=X) (G:=G) (S:=S) (q:=q) (drift:=drift) (op:=op) (hp:=hp)
    (headerRows:=headerRows) (paidRows:=paidRows) («origin»:=census) (romBase:=packet) (w:=w)
    («peer»:=peer) («paid»:=paid) («actor»:=actor) (signed:=wing) («matrix»:=matrix) (roleBase:=roleBase)
    (rolePages:=(phase).banks early) («ptr»:=ptr) (m:=entry) (homes:=(cal).homes slices)
    booked.1 word fitsMatrix (fun f=>(phase).banks_before early f |>.trans (below.trans (lit.trans horizon)))
    (roleEnd.trans (first.trans toCohort)) (fun f j x=>(fieldBounds f j x).1.2.2.trans dateEnd_)
    ?_ booked.2.1 booked.2.2.1 dictionary shape u₀ maskBase x h₀ gg slot roleRoom arityRoom marked bounded ready «given»
  intro f j x
  change S.hostSize S.length ≤ ((output).terminalField origin (f.castLE (by decide : 4 ≤ 7)) j (x.cast blocks)).size
  simpa only [chart.2.1,one,Nat.mul_one] using (fieldBounds f j x).2

open private venue_reads from OAI.Hierarchy.DescentNamedPhysicalRaster

include baseGroups last oldK word positive alive prev seed signedPitch rank roleEnd in
/-- In addition to the earlier packed actor pages this uses precisely the venue certified
by the final native date. All input addresses, their bounds, and the transfers across
the early rotation, scalar roles, snapshot replay, and fixed lookup installation
are derived from the scheduled program. -/
private theorem scheduledVenueReads {tags:ℕ} (afterDate:(dated).fullEnd floor≤base)
    {venueLimit:ℕ} (original:stageVenue b.target b.target.valid.host io_ (S.groupCount S.length) (D).paidBits venueLimit
      (b.target.venueRoster b.target.valid.host) m)
    (actorWords:∀x,Reads (actor x) (masks x) (S.groupCount S.length) m)
    (printed:2^(spec).printBits<2^w) :
    ((∀i:Fin (S.hostSize S.length),∀x:DescentColonies.Block k,prim_ (((rasters_).geometry.occupied x).base+i.val)=
      ((encode 1 (S.groupCount S.length) (masks x i)).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    ((∀v,venueField (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p) (cellAt (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p) (groups:=S.groupCount S.length) («blocks»:=2^k) (measured (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p)
      (groups:=S.groupCount S.length) (MaskAllocation.shelf (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (p:=p) (groups:=S.groupCount S.length) (rasters_).geometry 0) prim_ (hosts_ ((grid).pos v).2))
      (finProdFinEquiv (((grid).pos v).1,(grid).block v))) publicArity=DescentTerminalGraphRows.arity ((Epochs.finish G hu he epoch).state c).graph p v) →
      Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=Nat.clog 2 (q+1)) grid hosts_ S b.target.valid
      b.target.order (b.target.terminalRoster b.target.valid.host) rasters_ prim_)) ∧
    (∀ piecePositive : 0 < p, NativeBranch.localLimit G S≤q → (∀i:Fin H,(prim_ (((spec).frozenRoster census).base+i.val)).val=
      frozenRosterCode X G S b piecePositive baseGroups i) → (∀v,venueField (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p) (cellAt (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p) (groups:=S.groupCount S.length) («blocks»:=2^k) (measured (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p)
      (groups:=S.groupCount S.length) (MaskAllocation.shelf (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (p:=p) (groups:=S.groupCount S.length) (rasters_).geometry 0) prim_ (hosts_ ((grid).pos v).2))
      (finProdFinEquiv (((grid).pos v).1,(grid).block v))) publicArity=DescentTerminalGraphRows.arity ((Epochs.finish G hu he epoch).state c).graph p v)) := by
  have first := scheduled_base_le_early S k tail base j r t ports
  have next:early≤ slices:=by
    unfold Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop DescentTerminalSliceShelf.fence
      DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom DescentOperandStateBanks.guard
    simp only [Nat.add_assoc, Nat.le_add_right]
  obtain ⟨c₀,c₁,c₂,c₃,_⟩:=(cal).addresses slices census
  have below:slices≤packet:=c₀.trans (c₁.trans c₂)
  have lit:packet≤census:=Nat.le_add_right ..
  have horizon:census≤(spec).cohortEnd census:=(spec).cohort_le census
  have chart:=Phase.scheduled_layout G S board k tail age p f g drift degree payload ordinary op
    operandLanes primitiveLanes previous addr oldRoster floor last
  have datedEnd:oldLimit≤base:= ((output).terminal_order origin).2.1.trans
    (((output).terminal_order origin).2.2.trans (chart.2.2.2.2.2.le.trans afterDate))
  have reelRoom:base<2^w:=(first.trans (next.trans (below.trans (lit.trans c₃)))).trans_lt room
  have oldWord:oldLimit<2^w:=datedEnd.trans_lt reelRoom
  have booked:=scheduled_scan_before X G S k g p tail q drift op headerRows paidRows j r A slices
    board age f degree payload ordinary s₀ Z operandLanes primitiveLanes previous addr oldRoster floor
    baseGroups last oldK (afterDate.trans (first.trans next)) room
  have replay:=scheduled_original_preflight X G S baseGroups radix g p q drift op headerRows paidRows
    board age f degree payload ordinary operandLanes primitiveLanes previous addr oldRoster floor j r t base compact
    tag rotation A roleBase room last oldK word positive alive prev seed (afterDate.trans first) signedPitch rank roleEnd m
  have earlierRead (x:ℕ) (small:x<oldLimit):entry x=m x:=
    (replay.2.1 x (small.trans_le (datedEnd.trans (first.trans (next.trans below))))).symm.trans
      (replay.1.2.2.1 x (.inl (small.trans_le datedEnd)))
  have fitsMatrix:matrix+1≤(spec).cohortEnd census:=
    (show matrix+1≤early from Nat.le_add_right ..).trans (next.trans (below.trans (lit.trans horizon)))
  have dateEnd_:(output).finalEnd origin≤(spec).cohortEnd census:=
    ((output).terminal_order origin).1.trans (datedEnd.trans (first.trans (next.trans (below.trans (lit.trans horizon)))))
  have fieldBounds (f:Fin 4) (i:Fin (output).argumentSlots) (x:Fin bs):=
    (output).terminal_field_room origin (show (output).metadataEnd origin<2^w by
      rw [chart.2.2.2.2.2];exact afterDate.trans_lt reelRoom)
    (f.castLE (by decide : 4≤7)) i (x.cast blocks)
  have one:=Phase.scheduled_one G S board k tail age p f g drift degree payload ordinary op
    operandLanes primitiveLanes previous addr oldRoster floor last baseGroups signedPitch
  have shape:=PhysicalReset.scheduled_terminal_shape G S board k tail age p f g drift degree payload ordinary op
    s₀ Z operandLanes primitiveLanes previous addr oldRoster floor last oldK
  obtain ⟨kind,shops_,groups_,cap_,lanes_⟩:=shape
  have capMatch:(D).cap=(grid).cap:=cap_.trans (capEq).2.1.symm
  have widthBounds (x:DescentColonies.Block k) (t:Fin (2*(grid).cap)) :=
    (output).terminal_wing_room origin oldWord (x.cast (congrArg (2^·) kind).symm)
      (t.cast (congrArg (2*·) capMatch).symm)
  have sourceBounds (x:DescentColonies.Block k):=(output).terminal_actor_room origin oldWord (x.cast (congrArg (2^·) kind).symm)
  have gp:0<S.groupCount S.length:=by
    change 0<S.baseGroups*S.radix^_
    rw [baseGroups,radix]
    positivity
  have chunksOne:=covered_chunks gp le_rfl
  have hroom:H≤2^w:=by
    let zero:DescentColonies.Block k:=⟨0,Nat.two_pow_pos _⟩
    have size:H≤(actor zero).size:=booked.2.2.2 zero
    exact size.trans ((Nat.le_add_left ..).trans ((sourceBounds zero).1.trans oldWord.le))
  have two:2<2^w:=by
    have log_:1≤(spec).printBits:=by change 1≤2+_;omega
    have below_:2^1≤2^(spec).printBits:=Nat.pow_le_pow_right (by decide) log_
    omega
  refine venue_reads (tags:=tags) (X:=X) (G:=G) (S:=S) (b:=b) (base:=baseGroups) (q:=q)
      (drift:=drift) (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) («origin»:=census)
      (romBase:=packet) (w:=w) («peer»:=peer) («paid»:=paid) («actor»:=actor) (signed:=wing)
      («matrix»:=matrix) (roleBase:=roleBase) (rolePages:=(phase).banks early) («ptr»:=ptr) (m:=entry)
      (homes:=(cal).homes slices) le_rfl booked.1 word fitsMatrix ?_ ?_ ?_ ?_ booked.2.1 booked.2.2.1
      io_ m oldLimit (D).paidBits original earlierRead (datedEnd.trans (first.trans (next.trans below)))
      (fun i=>(sourceBounds i).1) actorWords ?_ ?_ (fun i t=>(widthBounds i t).1) ?_ ((output).terminal_peer_room origin).1 printed two hroom
  · exact fun j=>((phase).banks_before early j).trans (below.trans (lit.trans horizon))
  · exact roleEnd.trans (first.trans (next.trans (below.trans (lit.trans horizon))))
  · exact fun f j x=>(fieldBounds f j x).1.2.2.trans dateEnd_
  · intro f j x
    change S.hostSize S.length ≤ ((output).terminalField origin (f.castLE (by decide : 4 ≤ 7)) j (x.cast blocks)).size
    simpa only [chart.2.1,one,Nat.mul_one] using (fieldBounds f j x).2
  · exact roster_address (capEq).1 (capEq).2.1 _
  · intro x t
    exact wing_address (capEq).1 (capEq).2.1 peer ((spec).channels census) ((output).terminalWing origin) x t
  · intro i t
    have same : (D).hosts * chunks (D).groups (D).lanes =
        S.hostSize S.length * chunks (S.groupCount S.length) (S.groupCount S.length) :=
      congrArg₂ Nat.mul shops_ (congrArg₂ chunks groups_ lanes_)
    exact same.symm.le.trans (widthBounds i t).2




include baseGroups last oldK word positive alive prev seed signedPitch rank roleEnd in
/-- In addition to the earlier packed actor pages this uses precisely the venue certified
by the final native date. All input addresses, their bounds, and the transfers across
the early rotation, scalar roles, snapshot replay, and fixed lookup installation
are derived from the scheduled program. -/
theorem scheduled_venue_public {tags:ℕ} (afterDate:(dated).fullEnd floor≤base)
    {venueLimit:ℕ} (original:stageVenue b.target b.target.valid.host io_ (S.groupCount S.length) (D).paidBits venueLimit
      (b.target.venueRoster b.target.valid.host) m)
    (actorWords:∀x,Reads (actor x) (masks x) (S.groupCount S.length) m)
    (printed:2^(spec).printBits<2^w) :
    ((∀i:Fin (S.hostSize S.length),∀x:DescentColonies.Block k,prim_ (((rasters_).geometry.occupied x).base+i.val)=
      ((encode 1 (S.groupCount S.length) (masks x i)).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    ((∀v,venueField (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p) (cellAt (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p) (groups:=S.groupCount S.length) («blocks»:=2^k) (measured (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p)
      (groups:=S.groupCount S.length) (MaskAllocation.shelf (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (p:=p) (groups:=S.groupCount S.length) (rasters_).geometry 0) prim_ (hosts_ ((grid).pos v).2))
      (finProdFinEquiv (((grid).pos v).1,(grid).block v))) publicArity=DescentTerminalGraphRows.arity ((Epochs.finish G hu he epoch).state c).graph p v) →
      Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=Nat.clog 2 (q+1)) grid hosts_ S b.target.valid
      b.target.order (b.target.terminalRoster b.target.valid.host) rasters_ prim_)) ∧
    (NativeBranch.localLimit G S≤q → (∀i:Fin H,(prim_ (((spec).frozenRoster census).base+i.val)).val=
      frozenRosterCode X G S b hp baseGroups i) → (∀v,venueField (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p) (cellAt (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p) (groups:=S.groupCount S.length) («blocks»:=2^k) (measured (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p)
      (groups:=S.groupCount S.length) (MaskAllocation.shelf (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (p:=p) (groups:=S.groupCount S.length) (rasters_).geometry 0) prim_ (hosts_ ((grid).pos v).2))
      (finProdFinEquiv (((grid).pos v).1,(grid).block v))) publicArity=DescentTerminalGraphRows.arity ((Epochs.finish G hu he epoch).state c).graph p v)) := by
  have reads := scheduledVenueReads (tags:=tags) (X:=X) (G:=G) (S:=S) (baseGroups:=baseGroups) (radix:=radix)
    (q:=q) (p:=p) (g:=g) (drift:=drift) (op:=op) (headerRows:=headerRows) (paidRows:=paidRows)
    (board:=board) (age:=age) (f:=f) (degree:=degree) (payload:=payload) (ordinary:=ordinary)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previous) (addr:=addr)
    (oldRoster:=oldRoster) (floor:=floor) (j:=j) (r:=r) (t:=t) (base:=base)
    (compact:=compact) (tag:=tag) (rotation:=rotation) (A:=A) (roleBase:=roleBase)
    (room:=room) (b:=b) (u:=u) (m:=m) (last:=last) (oldK:=oldK) (word:=word)
    (positive:=positive) (alive:=alive) (prev:=prev) (seed:=seed) (signedPitch:=signedPitch) (rank:=rank)
    (roleEnd:=roleEnd) afterDate original actorWords printed
  exact ⟨reads.1, reads.2 hp⟩

include baseGroups last oldK word positive alive prev seed signedPitch rank roleEnd in
theorem scheduled_occupation_words {tags:ℕ} (afterDate:(dated).fullEnd floor≤base)
    {venueLimit:ℕ} (original:stageVenue b.target b.target.valid.host io_ (S.groupCount S.length) (D).paidBits venueLimit
      (b.target.venueRoster b.target.valid.host) m)
    (actorWords:∀x,Reads (actor x) (masks x) (S.groupCount S.length) m)
    (printed:2^(spec).printBits<2^w) :
    (∀i:Fin (S.hostSize S.length),∀x:DescentColonies.Block k,prim_ (((rasters_).geometry.occupied x).base+i.val)=
      ((encode 1 (S.groupCount S.length) (masks x i)).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    ((∀v,venueField (cellAt (measured (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p)
      (groups:=S.groupCount S.length) (MaskAllocation.shelf (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (p:=p) (groups:=S.groupCount S.length) (rasters_).geometry 0) prim_ (hosts_ ((grid).pos v).2))
      (finProdFinEquiv (((grid).pos v).1,(grid).block v))) publicArity=DescentTerminalGraphRows.arity ((Epochs.finish G hu he epoch).state c).graph p v) →
      Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=Nat.clog 2 (q+1)) grid hosts_ S b.target.valid
      b.target.order (b.target.terminalRoster b.target.valid.host) rasters_ prim_) := by
  exact (scheduledVenueReads (tags:=tags) (X:=X) (G:=G) (S:=S) (baseGroups:=baseGroups) (radix:=radix)
    (q:=q) (p:=p) (g:=g) (drift:=drift) (op:=op) (headerRows:=headerRows) (paidRows:=paidRows)
    (board:=board) (age:=age) (f:=f) (degree:=degree) (payload:=payload) (ordinary:=ordinary)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previous) (addr:=addr)
    (oldRoster:=oldRoster) (floor:=floor) (j:=j) (r:=r) (t:=t) (base:=base)
    (compact:=compact) (tag:=tag) (rotation:=rotation) (A:=A) (roleBase:=roleBase)
    (room:=room) (b:=b) (u:=u) (m:=m) (last:=last) (oldK:=oldK) (word:=word)
    (positive:=positive) (alive:=alive) (prev:=prev) (seed:=seed) (signedPitch:=signedPitch) (rank:=rank)
    (roleEnd:=roleEnd) afterDate original actorWords printed).1

include baseGroups last oldK word positive alive prev seed signedPitch rank roleEnd in
/-- Decode the true paid stage and exterior census at the attained primitive output. -/
theorem scheduled_population_word (afterDate:(dated).fullEnd floor≤base)
    {venueLimit:ℕ} (original:stageVenue b.target b.target.valid.host io_ (S.groupCount S.length) (D).paidBits venueLimit
      (b.target.venueRoster b.target.valid.host) m)
    (actorWords:∀x,Reads (actor x) (masks x) (S.groupCount S.length) m)
    (sourcePrecision:(D).paidBits=S.censusBits p) (height:0<S.height) (geometry:G.b≤2^S.capGain)
    (outer:∀h:Fin H,prim_ (((spec).census census).base+h.val)=
      (Computability.BorderVNP.FragmentBucket.count (cohortHome X G S b hp baseGroups) h:Computability.VPVNP.BurstRAM.Word w)) :
    ∀v:((Epochs.finish G hu he epoch).state c).graph.Site,digit nodeBits ((grid).pos v).1.val
      (prim_ ((((spec).channels census).primitive ((grid).block v) 3).base+(b.target.home v).val)).val=
      Fintype.card ((archive X G S b hp).bit.recipe v).Node := by
  have first := scheduled_base_le_early S k tail base j r t ports
  have next:early≤ slices:=by
    unfold Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop DescentTerminalSliceShelf.fence
      DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom DescentOperandStateBanks.guard
    simp only [Nat.add_assoc, Nat.le_add_right]
  obtain ⟨c₀,c₁,c₂,c₃,_⟩:=(cal).addresses slices census
  have below:slices≤packet:=c₀.trans (c₁.trans c₂)
  have lit:packet≤census:=Nat.le_add_right ..
  have horizon:census≤(spec).cohortEnd census:=(spec).cohort_le census
  have chart:=Phase.scheduled_layout G S board k tail age p f g drift degree payload ordinary op
    operandLanes primitiveLanes previous addr oldRoster floor last
  have datedEnd:oldLimit≤base:= ((output).terminal_order origin).2.1.trans
    (((output).terminal_order origin).2.2.trans (chart.2.2.2.2.2.le.trans afterDate))
  have reelRoom:base<2^w:=(first.trans (next.trans (below.trans (lit.trans c₃)))).trans_lt room
  have oldWord:oldLimit<2^w:=datedEnd.trans_lt reelRoom
  have booked:=scheduled_scan_before X G S k g p tail q drift op headerRows paidRows j r A slices
    board age f degree payload ordinary s₀ Z operandLanes primitiveLanes previous addr oldRoster floor
    baseGroups last oldK (afterDate.trans (first.trans next)) room
  have replay:=scheduled_original_preflight X G S baseGroups radix g p q drift op headerRows paidRows
    board age f degree payload ordinary operandLanes primitiveLanes previous addr oldRoster floor j r t base compact
    tag rotation A roleBase room last oldK word positive alive prev seed (afterDate.trans first) signedPitch rank roleEnd m
  have earlierRead (x:ℕ) (small:x<oldLimit):entry x=m x:=
    (replay.2.1 x (small.trans_le (datedEnd.trans (first.trans (next.trans below))))).symm.trans
      (replay.1.2.2.1 x (.inl (small.trans_le datedEnd)))
  have fitsMatrix:matrix+1≤(spec).cohortEnd census:=
    (show matrix+1≤early from Nat.le_add_right ..).trans (next.trans (below.trans (lit.trans horizon)))
  have dateEnd_:(output).finalEnd origin≤(spec).cohortEnd census:=
    ((output).terminal_order origin).1.trans (datedEnd.trans (first.trans (next.trans (below.trans (lit.trans horizon)))))
  have fieldBounds (f:Fin 4) (i:Fin (output).argumentSlots) (x:Fin bs):=
    (output).terminal_field_room origin (show (output).metadataEnd origin<2^w by
      rw [chart.2.2.2.2.2];exact afterDate.trans_lt reelRoom)
    (f.castLE (by decide : 4≤7)) i (x.cast blocks)
  have one:=Phase.scheduled_one G S board k tail age p f g drift degree payload ordinary op
    operandLanes primitiveLanes previous addr oldRoster floor last baseGroups signedPitch
  have shape:=PhysicalReset.scheduled_terminal_shape G S board k tail age p f g drift degree payload ordinary op
    s₀ Z operandLanes primitiveLanes previous addr oldRoster floor last oldK
  obtain ⟨kind,shops_,groups_,cap_,lanes_⟩:=shape
  have actorRange (x:DescentColonies.Block k):=(output).terminal_actor_room origin oldWord
    (x.cast (congrArg (2^·) kind).symm)
  have paidRange (x:DescentColonies.Block k):=(output).terminal_paid_room origin oldWord
    (x.cast (congrArg (2^·) kind).symm)
  have oldBefore:oldLimit≤packet:=datedEnd.trans (first.trans (next.trans below))
  have actorRead (x:DescentColonies.Block k):Reads (actor x) (masks x) (S.groupCount S.length) entry:=by
    intro zz
    have dim:H*chunks (S.groupCount S.length) (S.groupCount S.length)≤(actor x).size:=by
      have bound := (actorRange x).2
      change (dated).successor.venue.next.hosts *
        chunks (dated).successor.venue.next.groups (dated).successor.venue.next.lanes ≤ (actor x).size at bound
      rw [shops_,groups_,lanes_] at bound
      exact bound
    have small:=(row _ _ _ zz).isLt.trans_le dim
    exact (earlierRead _ ((Nat.add_lt_add_left small _).trans_le (actorRange x).1)).trans (actorWords x zz)
  have paidRead (x:DescentColonies.Block k):Reads (paid x)
      (fun h g=>DescentPacking.PackedMatch.Local.Stage.Census.count grid (Equiv.refl _) hosts_ (S.censusBits p) h g x)
      (S.groupCount S.length) entry:=by
    intro zz
    have dim:H*chunks (S.groupCount S.length) (S.groupCount S.length)≤(paid x).size:=by
      have bound := (paidRange x).2
      change (dated).successor.venue.next.hosts *
        chunks (dated).successor.venue.next.groups (dated).successor.venue.next.lanes ≤ (paid x).size at bound
      rw [shops_,groups_,lanes_] at bound
      exact bound
    have small:=(row _ _ _ zz).isLt.trans_le dim
    have roof:=(paidRange x).1
    have fits:(paid x).Fits w oldLimit:=
      ⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (roof.trans_lt oldWord),roof⟩
    have originalRead:=original.2.2.2.2.2.2.2.2 x zz
    change (paid x).read m ((row _ _ _ zz).val:Computability.VPVNP.BurstRAM.Word w)=_ at originalRead
    rw [DescentPackedZip.bank_read (paid x) m small fits,sourcePrecision] at originalRead
    exact (earlierRead _ ((Nat.add_lt_add_left small _).trans_le roof)).trans originalRead
  refine fixed_population_word (hp:=hp) (X:=X) (G:=G) (S:=S) (b:=b) (base:=baseGroups) (q:=q)
      (drift:=drift) (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) («origin»:=census)
      (romBase:=packet) (w:=w) («peer»:=peer) («paid»:=paid) («actor»:=actor) (signed:=wing)
      («matrix»:=matrix) (roleBase:=roleBase) (rolePages:=(phase).banks early) («ptr»:=ptr) (m:=entry)
      (homes:=(cal).homes slices) le_rfl booked.1 word fitsMatrix ?_ ?_ ?_ ?_ booked.2.1 booked.2.2.1
      height geometry (fun x=>(actorRange x).1.trans oldBefore) actorRead
      (fun x=>(paidRange x).1.trans oldBefore) paidRead outer
  · exact fun j=>((phase).banks_before early j).trans (below.trans (lit.trans horizon))
  · exact roleEnd.trans (first.trans (next.trans (below.trans (lit.trans horizon))))
  · exact fun f j x=>(fieldBounds f j x).1.2.2.trans dateEnd_
  · intro f j x
    change S.hostSize S.length ≤ ((output).terminalField origin (f.castLE (by decide : 4 ≤ 7)) j (x.cast blocks)).size
    simpa only [chart.2.1,one,Nat.mul_one] using (fieldBounds f j x).2


include baseGroups last oldK word positive alive prev seed signedPitch rank roleEnd in
/-- Read the remaining Book fields after measuring the native public arity. -/
theorem scheduled_raster_fields {tags:ℕ} (afterDate:(dated).fullEnd floor≤base)
    {venueLimit:ℕ} (original:stageVenue b.target b.target.valid.host io_ (S.groupCount S.length) (D).paidBits venueLimit
      (b.target.venueRoster b.target.valid.host) m)
    (actorWords:∀x,Reads (actor x) (masks x) (S.groupCount S.length) m)
    (printed:2^(spec).printBits<2^w)
    (scalar:∀v,venueField (cellAt (measured (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (w:=p)
      (groups:=S.groupCount S.length) (MaskAllocation.shelf (q:=q) (t:=tags) («H»:=args) (N:=nodes_) (A:=args) (p:=p) (groups:=S.groupCount S.length) (rasters_).geometry 0) prim_ (hosts_ ((grid).pos v).2))
      (finProdFinEquiv (((grid).pos v).1,(grid).block v))) publicArity=DescentTerminalGraphRows.arity ((Epochs.finish G hu he epoch).state c).graph p v):
    Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=Nat.clog 2 (q+1)) grid hosts_ S b.target.valid
      b.target.order (b.target.terminalRoster b.target.valid.host) rasters_ prim_ := by
  exact (scheduled_occupation_words (tags:=tags) (X:=X) (G:=G) (S:=S) (baseGroups:=baseGroups) (radix:=radix)
    (q:=q) (p:=p) (g:=g) (drift:=drift) (op:=op) (headerRows:=headerRows) (paidRows:=paidRows)
    (board:=board) (age:=age) (f:=f) (degree:=degree) (payload:=payload) (ordinary:=ordinary)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previous) (addr:=addr)
    (oldRoster:=oldRoster) (floor:=floor) (j:=j) (r:=r) (t:=t) (base:=base)
    (compact:=compact) (tag:=tag) (rotation:=rotation) (A:=A) (roleBase:=roleBase)
    (room:=room) (b:=b) (u:=u) (m:=m) (last:=last) (oldK:=oldK) (word:=word)
    (positive:=positive) (alive:=alive) (prev:=prev) (seed:=seed) (signedPitch:=signedPitch) (rank:=rank)
    (roleEnd:=roleEnd) afterDate original actorWords printed).2 scalar

end Selected
end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
