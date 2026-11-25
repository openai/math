import OAI.Hierarchy.DescentTerminalRoleTableFrame
import OAI.Hierarchy.DescentTerminalRolePairFields
import OAI.Hierarchy.DescentTerminalFixedPointerCast
import OAI.Hierarchy.DescentTerminalPointerPair
import OAI.Hierarchy.DescentTerminalFrozenPointerWords
import OAI.Hierarchy.DescentTerminalPrimitivePublicFrame
import OAI.Hierarchy.DescentNamedTerminalPopulation
import OAI.Hierarchy.DescentPackedCensusInvoice
import OAI.Hierarchy.DescentPaidResidentCensus
import OAI.Hierarchy.DescentNamedPreflightFrames
import OAI.Hierarchy.DescentTerminalPriorActorWords
import OAI.Hierarchy.DescentTerminalObservedRoster

namespace OAI
/-! # The six-Book roster on the attained physical primitive memory -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 12288
set_option maxHeartbeats 900000
set_option cleanup.letToHave false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)


local notation "s" => S.firstWidth G.b p
local notation "net" => ((Epochs.finish G hu he r).state c).graph
local notation "E" => Fintype.card (Port P X.width)
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
variable (width : S.groupWidth k tail 0+k=j+(j+rest))



open DescentTerminalGraphPositions DescentTerminalCableOrder DescentTerminalLocalPortBook DescentSharedCableNames DescentColonies
open ThreeFlat.Routing CallPool
local notation "retained" => S.groupWidth k tail S.length+k
local notation "O" => leafOrder X G S b hp base width
local notation "placement" => b.target.placement
local notation "native" => b.target.order.trans Fin.valEmbedding
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount S.length)) (b.target.vertex.trans Fin.valEmbedding))
local notation "pinRank" v:arg => (densePinEquiv X G S b hp base v).toEmbedding.trans Fin.valEmbedding
local notation "calendar" => fun g row => ((S.resetInputDigits base radix S.length).symm (g,row)).val
local notation "scale" => ((placement).z*G.b)/p


open DescentTerminalPaidHeaderEvents DescentTerminalGrainProfiles DescentTerminalPeerChronology DescentTerminalGraphRows
open DescentSortedRoster DescentPhysicalOrder DescentPacking
local notation "H0" => S.hostSize S.length
local notation "hosts" => b.target.vertex.trans (Fin.castLEEmb b.target.valid.host)
local notation "nodeRank" => ((placement).site b.target.vertex b.target.valid.coordinates).trans Fin.valEmbedding
local notation "outs" => leafExternal X G S b hp base width
local notation "ins" => leafOperands X G S b hp base

open DescentSIMDLookup DescentTerminalRecipeRows DescentTerminalPointerDigits ProtocolRAM Calendar Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
local notation "V0" => S.groupCount S.length*2^k
local notation "A0" => NativeBranch.localLimit G S
local notation "M0" => V0*A0


open DescentTerminalPreflightSpace

open DescentTerminalVertexFields DescentTerminalPointerIssue DescentTerminalSiteShelves
open DescentTerminalSignedGrainWord DescentChosenRouter DescentPackedColony DescentColonies.SplitRAM
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentStaticWordColumn DescentTerminalPrimitiveArena
open Computability.BorderVNP.Crossing
variable (q drift:ℕ) (op:RotorSpec) (headerRows paidRows:ℕ)
local notation "fmt" => geometryFormat G S k g p tail q drift op headerRows paidRows
local notation "spec" => preflightSpec X G S k g p tail fmt
local notation "nodes" => S.epochPower^S.localTokenExponent
local notation "maxArgs" => NativeBranch.privateSlotCapacity G S drift
local notation "s₀" => S.firstWidth G.b p
local notation "colors" => DescentPrimitivePalette.colors G s₀ (S.grainAt G.b p 0) op
local notation "groupLimit" => max 8 (2^S.capGain)
local notation "tagBits" => fun f:Fin 6=>DescentTerminalCombinedRole.width colors groupLimit maxArgs p drift f*nodes*(spec).groups
local notation "nodeBits" => Nat.clog 2 (nodes+1)
local notation "config" => (⟨nodeBits,Nat.clog 2 (maxArgs+1),fun _=>DescentOperandWidth.recordBits G S k tail drift 3 p,some nodes⟩:Widths)
local notation "index" => DescentExterior.terminalPin (S.groupWidth k tail 0+k) (S.groupWidth k tail S.length+k) (k*S.length)
local notation "psize" => poolBatchCount (s₀*1) p
local notation "f0" => publicCell (cap:=(spec).cap) (N:=nodes) (A:=maxArgs) (d:=(spec).scalar.pointerBits)
  3 q G.b psize (k*S.length) (spec).groups config
local notation "f7" => DescentTerminalPointerDigits.output (spec).cap nodes maxArgs 3 (spec).groups (spec).scalar.pointerBits
  (Nat.clog 2 (q+maxArgs+1)) q G.b psize config index
local notation "readBook" => decodeBook S G base radix p q 3 (spec).cap (spec).printBits (by decide)
local notation "fixedControl" => portTable (G:=4) (V:=(spec).vertices) (M:=(spec).vertices*(spec).arguments) (A:=(spec).arguments)
  (a:=Book.tokenBits ((spec).vertices*(spec).arguments)) q

local notation "blocks" => (spec).scalar.blocks
local notation "shops" => (spec).scalar.shops
variable (origin romBase:ℕ) (w:ℕ) (peer:Bank) (paid actor:Fin (((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).scalar.blocks)→Bank) (signed:Fin (((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).scalar.blocks)→Fin (2*((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).cap)→Bank)
    (matrix roleBase:ℕ) (rolePages:Fin 6→Bank) {Aphys:ℕ} (ptr:Fin 4→Fin Aphys→Fin (((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).scalar.blocks)→Bank)
local notation "first" => DescentTerminalRoleTables.role tagBits rolePages roleBase
local notation "second" => DescentTerminalRoleTables.arity tagBits rolePages roleBase
local notation "previous" => DescentTerminalOperandRepack.padded (K:=maxArgs) ptr paid
local notation "pointerPages_" => (spec).pointerPages origin matrix previous signed
local notation "chart" => (pointerPages_).address (N:=nodes)
variable (m:Memory w)
local notation "shelf" => (spec).scanPages romBase q
local notation "rack" => (spec).rasters origin peer signed
local notation "eqs" => preflight_caps (tail:=tail) X G S b fmt
local notation "measuredRack" => presented (eqs).1 (eqs).2.1 rack
local notation "literalized" => (shelf).image m
local notation "primitive" => (spec).primitiveSnapshot (base:=origin) (w:=w) (q:=q) (p:=p)
  (nd:=nodeBits) («nodes»:=nodes) (hidden:=maxArgs) (args:=maxArgs) (oldPaid:=paid) (actor:=actor)
  («first»:=first) («second»:=second) («chart»:=chart) («f0»:=f0) («f7»:=f7) literalized
private theorem raster_geometry {d k c d' c':ℕ} (left:d=d') (right:c=c') (r:Rasters d' k c') :
    (presented left right r).geometry=r.geometry := by subst d';subst c';rfl

/-- Read the original four physical families after generating f0, f7 and the two
primitive masks. This date includes the actual initial literal ROM write. -/
theorem fixed_primitive_raster {tags:ℕ} (raw:Fin H0 → Fin (placement).degree → Option (Fin H0))
    (near:∀v,present raw (hosts v)=((placement).near v).map hosts)
    (peers:∀h j z,(DescentSortedRoster.indexed raw) h j=some z→(measuredRack).roster.read primitive ((h.val*(placement).degree+j.val:ℕ):Computability.VPVNP.BurstRAM.Word w)=(z.val:Computability.VPVNP.BurstRAM.Word w))
    (word:2<2^w) (room:2^(spec).printBits<2^w) (hostFit:H0≤2^w)
    (actors:∀h:Fin H0,∀b:Block k,primitive (((measuredRack).geometry.occupied b).base+h.val)=
      ((encode 1 (S.groupCount S.length) (fun g=>(if ∃v:(net).Site,hosts ((placement).pos v).2=h ∧ ((placement).pos v).1=g ∧ (placement).block v=b then 1 else 0):Fin (S.groupCount S.length) → Cell 1)).val:Computability.VPVNP.BurstRAM.Word w))
    (scalar:∀v:(net).Site,venueField (cellAt
      (measured (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (w:=p) (groups:=S.groupCount S.length)
        (MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=S.groupCount S.length) (measuredRack).geometry 0) primitive (hosts ((placement).pos v).2)) (finProdFinEquiv (((placement).pos v).1,(placement).block v))) publicArity=
      DescentTerminalGraphRows.arity net p v)
    (pitch:ℕ) (covered:(S.groupCount S.length) ≤ pitch) (wide:DescentSignedCableCodec.width (placement).degree (placement).cap*pitch ≤ w)
    (wings:∀block t,Reads ((measuredRack).wing block t) (fun h g=>DescentSignedCableCodec.encode ((DescentPacking.PackedMatch.Local.Stage.Prepare.signed placement native S b.target.valid (Function.Embedding.refl _) hosts block t h g))) pitch primitive)
    (wingCap:∀b t,H0≤((measuredRack).wing b t).size) :
    Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=(Nat.clog 2 (q+1))) placement hosts S b.target.valid b.target.order raw measuredRack primitive := by
  let B:=S.groupCount S.length
  let side:=DescentSignedCableCodec.width (placement).degree (placement).cap
  let tier:=max (max 1 (Nat.clog 2 (q+1))) side
  have wordShape:(spec).printBits=2+B*tier:=by
    dsimp only [tier,side,B]
    rw [(eqs).1,(eqs).2.1]
    rfl
  have shelfBits:B≤(spec).printBits:=by
    have one:1≤tier:= (Nat.le_max_left 1 _).trans (Nat.le_max_left _ _)
    have bound:=Nat.mul_le_mul_left B one
    simp only [Nat.mul_one] at bound
    omega
  have argBits:Nat.clog 2 (q+1)*B≤(spec).printBits:=by
    have rate:Nat.clog 2 (q+1)≤tier:=(Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_left B rate).trans (by omega)
  have wingBits:side*B≤(spec).printBits:=by
    rw [Nat.mul_comm];exact (Nat.mul_le_mul_left B (show side≤tier from Nat.le_max_right ..)).trans (by omega)
  have bitsRoom:(spec).printBits≤w:=by
    by_contra! bad
    exact (not_le_of_gt room) (Nat.pow_le_pow_right (by decide) bad.le)
  have tiny : 2<2^(spec).printBits:= (by decide : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have maskCap (i:Block k) : H0≤((measuredRack).geometry.occupied i).size:=by
    rw [raster_geometry]
    change H0≤2^Nat.clog 2 H0
    exact Nat.le_pow_clog (by decide) _
  have portCap (i:Block k) : H0≤((measuredRack).geometry.primitive i 0).size:=by
    rw [raster_geometry]
    change H0≤2^Nat.clog 2 H0
    exact Nat.le_pow_clog (by decide) _
  exact Rasters.from_pages (p:=p) (bw:=(spec).printBits) (q:=q) (tags:=tags) (hid:=maxArgs) (N:=nodes) (M:=maxArgs)
    placement hosts S b.target.valid b.target.order raw measuredRack primitive near peers word tiny hostFit
    maskCap portCap actors scalar shelfBits bitsRoom argBits wingBits pitch covered wide wings wingCap

section NativeActors
variable (homes:Bank)
  (low:((((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).scanPages romBase q)).stop≤origin)
  (boot:((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).Before origin paid actor signed peer ((((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).scanPages romBase q)).total ((((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).scanPages romBase q)).modulo homes ((((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).scanPages romBase q)).boundaries)
  (space:((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).maskBase origin<2^w)
  (matrixEnd:matrix+1≤((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).cohortEnd origin)
  (roleBefore:∀f,(rolePages f).base+(rolePages f).size≤((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).cohortEnd origin)
  (roleEnd:roleBase+DescentTerminalRoleTables.count (fun f:Fin 6=>DescentTerminalCombinedRole.width (DescentPrimitivePalette.colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op) (max 8 (2^S.capGain)) (NativeBranch.privateSlotCapacity G S drift) p drift f*(S.epochPower^S.localTokenExponent)*((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).groups)≤((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).cohortEnd origin)
  (ptrEnd:∀f j b,(ptr f j b).base+(ptr f j b).size≤((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).cohortEnd origin)
  (ptrRows:∀f j b,(((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).scalar.shops)≤(ptr f j b).size) (paidFit:∀b,(((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).scalar.shops)≤(paid b).size)
  (signedRows:∀b j,(((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows))).scalar.shops)≤(signed b j).size)
local notation "liveBits" => (fun (block:Block k) (h:Fin H0) (g:Fin (S.groupCount S.length)) =>
  (if ∃v:(net).Site,hosts ((placement).pos v).2=h ∧ ((placement).pos v).1=g ∧ (placement).block v=block
    then 1 else 0 : Cell 1))
local notation "paidMem" => (spec).paidSnapshot (base:=origin) (w:=w) (nd:=nodeBits) (oldPaid:=paid)
  (actor:=actor) literalized

local notation "warmed" => DescentTerminalCombinedRole.memory first second ((spec).primitive origin) ((spec).scalar.rows) paidMem

open DescentEpochTagKeys DescentBundleHistory DescentKernelHistory

include boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
/-- The primitive image retains the exact two acquired role/arity rows after the pointer and width passes. -/
theorem fixed_role_scan_fields {Tag V:Type} {widthAt:V→ℕ} {r:BitRecipe Tag V widthAt}
    (dictionary : Codec Tag colors) (shape : DescentBundleHistory.Shape p r) (u : r.Node)
    (maskBase : ℕ) (x:Block k) (h:Fin H0) (gg:Fin (spec).groups) (slot:Fin nodes)
    (roleRoom : DescentTerminalCombinedRole.output colors groupLimit maxArgs p drift*nodes*(spec).groups≤w)
    (arityRoom : Nat.clog 2 (maxArgs+1)*nodes*(spec).groups≤w)
    (marked : dictionary.fits (r.tag u)) (bounded : (shape.recipe hp).arity u≤ maxArgs)
    (ready : Static (A:=groupLimit) (G:=maxArgs) (p:=p) (R:=drift) (N:=nodes) (M:=(spec).groups) dictionary first primitive ∧
      CountStatic (n:=colors) (A:=groupLimit) (G:=maxArgs) (p:=p) (R:=drift) (N:=nodes) (M:=(spec).groups)
        maxArgs second primitive)
    («given» : Printed dictionary (DescentTerminalCombinedRole.fields (n:=colors) (A:=groupLimit) (G:=maxArgs) (p:=p) (R:=drift) (DescentTerminalCombinedRole.node (n:=colors) (A:=groupLimit) (G:=maxArgs) (p:=p) (R:=drift) (N:=nodes) (M:=(spec).groups) (observed (n:=colors) (A:=groupLimit) (G:=maxArgs)
      (p:=p) (R:=drift) (N:=nodes) (M:=(spec).groups) first primitive ((finProdFinEquiv (x,h)).val:Computability.VPVNP.BurstRAM.Word w))
       gg slot)) (r.tag u) (shape.sliceFields u)) :
    let machine:=MaskAllocation.shelf (q:=q) (t:=DescentBundleTagKeys.capacity colors groupLimit maxArgs p drift)
      (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=(spec).groups) ((spec).channels origin) maskBase
    let cell:=cellAt (measured (q:=q) (t:=DescentBundleTagKeys.capacity colors groupLimit maxArgs p drift)
      (H:=maxArgs) (N:=nodes) (A:=maxArgs) (w:=p) (groups:=(spec).groups) machine primitive h) (finProdFinEquiv (gg,x))
    venueField cell (nodeRole slot)=((DescentBundleTagKeys.codec dictionary groupLimit maxArgs p drift).store ((shape.recipe hp).tag u)).val+1 ∧
    venueField cell (nodeArity slot)=(shape.recipe hp).arity u :=by
  intro machine cell
  have roles:=(spec).role_fits origin space tagBits rolePages roleBase roleBefore roleEnd
  have ptrE:∀f j b,(previous f j b).base+(previous f j b).size≤(spec).cohortEnd origin:=by
    intro f j b
    unfold DescentTerminalOperandRepack.padded
    split
    · exact ptrEnd _ _ _
    · exact boot.oldPaid _
  have ptrH:∀f j b,shops≤(previous f j b).size:=by
    intro f j b
    unfold DescentTerminalOperandRepack.padded
    split
    · exact ptrRows _ _ _
    · exact paidFit _
  have cols:0<(spec).scalar.columns:=by
    change 0<3+nodes+4*(nodes*maxArgs)+2*(spec).cap
    omega
  have ptrFit:=(spec).pointer_fits origin matrix previous signed space matrixEnd ptrE ptrH boot.oldCables signedRows nodes
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=(spec).layers origin
  have room:(spec).primitive origin<2^w:=by omega
  have lim:(spec).scalar.finish ((spec).primitive origin)<2^w:=by
    change (spec).weights origin<2^w
    omega
  have kit:=(spec).scalar.realized ((spec).primitive origin) ((spec).population origin) _ ((spec).prior origin) lim cols
  have frames:=(spec).scalar.primitive_frames ((spec).primitive origin) ((spec).population origin)
    first second chart f0 f7 q maxArgs nodes maxArgs (spec).groups p paidMem kit roles.1
    (ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) roles.2) ptrFit
  have early:=(spec).cohort_le origin
  have beforeStart : (spec).cohortEnd origin≤(spec).primitive origin:=by omega
  have transferred:=DescentTerminalRoleTables.preserve_tables dictionary maxArgs rolePages roleBase
    primitive paidMem ready.1 ready.2 (fun a _ bound=>(frames.2.2.1 a (.inl (bound.trans_le (roleEnd.trans beforeStart)))).symm)
  let src:=DescentTerminalCombinedRole.observed (wb:=w) (n:=colors) (A:=groupLimit) (G:=maxArgs) (p:=p)
    (R:=drift) (N:=nodes) (M:=(spec).groups) first
  have seen : src paidMem ((finProdFinEquiv (x,h)).val:Computability.VPVNP.BurstRAM.Word w)=src primitive ((finProdFinEquiv (x,h)).val:Computability.VPVNP.BurstRAM.Word w) :=by
    funext f
    have eqn:=DescentTerminalPrimitiveFrames.bank_below paidMem primitive (rolePages f) ((spec).primitive origin)
      ((roleBefore f).trans beforeStart) (fun a h=>frames.2.2.1 a (.inl h)) ((finProdFinEquiv (x,h)).val:Computability.VPVNP.BurstRAM.Word w)
    exact congrArg (fun z : Computability.VPVNP.BurstRAM.Word w => (z.val : Computability.VPVNP.BurstRAM.Word (tagBits f))) eqn.symm
  have chan (f : Fin 8) : machine.channel (finProdFinEquiv (x,f.succ)) = ((spec).channels origin).primitive x f :=
    MaskAllocation.Channels.primitive_at ((spec).channels origin) x f
  have transported := (congrArg (fun z => Printed dictionary (DescentTerminalCombinedRole.fields (n:=colors) (A:=groupLimit) (G:=maxArgs) (p:=p) (R:=drift) (DescentTerminalCombinedRole.node (n:=colors) (A:=groupLimit) (G:=maxArgs) (p:=p) (R:=drift) (N:=nodes) (M:=(spec).groups) z gg slot)) (r.tag u) (shape.sliceFields u)) seen).mpr «given»
  have pair:=DescentTerminalRolePairFields.paired_fields (q:=q) (hid:=maxArgs) dictionary hp shape u first second
    ((spec).primitive origin) machine paidMem roles.1 roles.2 kit.role_first transferred.1 transferred.2 rfl
    roleRoom arityRoom h x gg slot (by rw [chan];rfl)
    (by rw [chan];exact kit.keep_family x 5) (by rw [chan];rfl)
    (by rw [chan];exact kit.keep_family x 6) marked bounded transported
  have fieldEq (key : Key maxArgs nodes maxArgs) (code : group key=5 ∨ group key=6) :=
    DescentTerminalPrimitiveFrames.field_below (q:=q) (t:=DescentBundleTagKeys.capacity colors groupLimit maxArgs p drift)
      (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=(spec).groups) machine warmed primitive x h gg
      ((spec).scalar.gather ((spec).primitive origin)) key
      ((congrArg (fun bank : Bank => bank.base+bank.size) (chan (group key))).trans_le (kit.pointer_prior x (group key) (Or.inr (Or.inr code)))) frames.2.2.2
  exact ⟨(fieldEq (nodeRole slot) (.inl rfl)).trans pair.2.2.1,
    (fieldEq (nodeArity slot) (.inr rfl)).trans pair.2.2.2.1⟩

include boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
/-- The actual public output comes from the gather on the preceding role-scan
state. Its signed panels and original frozen roster still have their values
from the end of the entire primitive run. -/
theorem fixed_pointer_output_rows (x:Block k) (h:Fin H0) :
    primitive ((((spec).channels origin).primitive x 0).base+h.val)=
      ((f0 ((pointerPages_).source warmed x h)).val:Computability.VPVNP.BurstRAM.Word w) ∧
    primitive ((((spec).channels origin).primitive x 7).base+h.val)=
      ((f7 ((pointerPages_).source warmed x h)).val:Computability.VPVNP.BurstRAM.Word w) ∧
    (∀a,a<(spec).primitive origin→warmed a=primitive a) ∧
    ((pointerPages_).source (N:=nodes) (d:=(spec).scalar.pointerBits) warmed x h)=
       (pointerPages_).source primitive x h := by
  have roles:=(spec).role_fits origin space tagBits rolePages roleBase roleBefore roleEnd
  have ptrE:∀f j b,(previous f j b).base+(previous f j b).size≤(spec).cohortEnd origin:=by
    intro f j b
    unfold DescentTerminalOperandRepack.padded
    split
    · exact ptrEnd _ _ _
    · exact boot.oldPaid _
  have ptrH:∀f j b,shops≤(previous f j b).size:=by
    intro f j b
    unfold DescentTerminalOperandRepack.padded
    split
    · exact ptrRows _ _ _
    · exact paidFit _
  have cols:0<(spec).scalar.columns:=by
    change 0<3+nodes+4*(nodes*maxArgs)+2*(spec).cap
    omega
  have ptrFit:=(spec).pointer_fits origin matrix previous signed space matrixEnd ptrE ptrH boot.oldCables signedRows nodes
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=(spec).layers origin
  have room:(spec).primitive origin<2^w:=by omega
  have lim:(spec).scalar.finish ((spec).primitive origin)<2^w:=by
    change (spec).weights origin<2^w
    omega
  have kit:=(spec).scalar.realized ((spec).primitive origin) ((spec).population origin) _ ((spec).prior origin) lim cols
  have write:=(spec).scalar.primitive_any ((spec).primitive origin) ((spec).population origin)
    first second chart f0 f7 q maxArgs nodes maxArgs (spec).groups p paidMem kit roles.1
    (ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) roles.2) ptrFit
  let i:Fin (spec).scalar.rows:=finProdFinEquiv (x,h)
  have frame:=(spec).scalar.public_frame ((spec).primitive origin) ((spec).population origin)
    first second chart f0 f7 q maxArgs nodes maxArgs (spec).groups p paidMem kit ptrFit i
  have refs:=(spec).scalar.reference_frame ((spec).primitive origin) ((spec).population origin)
    first second chart f0 f7 q maxArgs nodes maxArgs (spec).groups p paidMem kit i
  have pair:=(pointerPages_).pair warmed ((spec).scalar.gather ((spec).primitive origin)) shops
    f0 f7 ptrFit kit.pointer_radix kit.pointer_limit
  have address:(((spec).channels origin).primitive x 0).base+h.val=
      (spec).scalar.public ((spec).primitive origin)+i.val:=by
    change (_+x.val*shops)+h.val=_+(finProdFinEquiv (x,h)).val
    change _ + x.val * H0 + h.val = _ + (h.val + H0 * x.val)
    ac_rfl
  have operand:(((spec).channels origin).primitive x 7).base+h.val=
      (spec).scalar.pointers ((spec).primitive origin)+i.val:=by
    change (_+x.val*shops)+h.val=_+(finProdFinEquiv (x,h)).val
    change _ + x.val * H0 + h.val = _ + (h.val + H0 * x.val)
    ac_rfl
  refine ⟨?_,?_,?_,?_⟩
  · exact ((congrArg primitive address).trans frame).trans (pair.2.2.1 x h).1
  · exact ((congrArg primitive operand).trans refs).trans (pair.2.2.1 x h).2
  · intro a earlier
    have low₁:=ProtocolRAMGeneratedWrite.frame_image ((spec).primitive origin) ((spec).scalar.rows)
      (emit first) paidMem a (.inl earlier)
    have low₂:=ProtocolRAMGeneratedWrite.frame_image (((spec).primitive origin)+(spec).scalar.rows)
      ((spec).scalar.rows) (emit second) (ProtocolRAM.image ((spec).primitive origin) ((spec).scalar.rows) (emit first) paidMem) a
      (.inl (earlier.trans_le (Nat.le_add_right ..)))
    exact (low₂.trans low₁).trans (write.2.2 a (.inl earlier)).symm

  · funext j
    let addr:=(chart j x).atHost h
    have all:=(spec).scalar.source_frame ((spec).primitive origin) ((spec).population origin)
      first second chart f0 f7 q maxArgs nodes maxArgs (spec).groups p paidMem kit ptrFit addr
      ((chart j x).below (ptrFit j x) h)
    exact congrArg (fun z:Computability.VPVNP.BurstRAM.Word w=>(z.val:Cell (spec).scalar.pointerBits)) all.symm

include boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
theorem fixed_public_row (x:Block k) (h:Fin H0) :
    primitive ((((spec).channels origin).primitive x 0).base+h.val)=
      ((f0 ((pointerPages_).source warmed x h)).val:Computability.VPVNP.BurstRAM.Word w) ∧
    ∀a,a<(spec).primitive origin→warmed a=primitive a := by
  have both:=fixed_pointer_output_rows (X:=X) (G:=G) (S:=S) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase) (w:=w)
    (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
    (rolePages:=rolePages) (ptr:=ptr) (m:=m) (homes:=homes) boot space matrixEnd roleBefore roleEnd
    ptrEnd ptrRows paidFit signedRows x h
  exact ⟨both.1,both.2.2.1⟩

include boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
/-- The f7 cell is the actual dictionary output on the four original pointer
pages, preserved through the native distinct-word and width scans. -/
theorem fixed_operand_word (x:Block k) (h:Fin H0) :
    primitive ((((spec).channels origin).primitive x 7).base+h.val)=
      ((f7 ((pointerPages_).source primitive x h)).val:Computability.VPVNP.BurstRAM.Word w) := by
  have both:=fixed_pointer_output_rows (X:=X) (G:=G) (S:=S) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase) (w:=w)
    (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
    (rolePages:=rolePages) (ptr:=ptr) (m:=m) (homes:=homes) boot space matrixEnd roleBefore roleEnd
    ptrEnd ptrRows paidFit signedRows x h
  exact both.2.1.trans (congrArg (fun raw=>((f7 raw).val:Computability.VPVNP.BurstRAM.Word w)) both.2.2.2)

/-- Numerically authenticate the exact cells of a reached site read by the f7
dictionary. Only the four raw fields of active original operands enter the proof. -/
theorem fixed_pointer_live (x:Block k) (h:Fin H0) (gg:Fin (spec).groups)
    (t:CellInputs 3 (spec).cap nodes maxArgs)
    (population:digit nodeBits gg.val (primitive ((((spec).channels origin).primitive x 3).base+h.val)).val=t.n)
    (arity:∀u:Fin nodes,u.val<t.n→(config).nodeDigit (Nat.clog 2 (maxArgs+1)) u.val gg.val
      (primitive ((((spec).channels origin).primitive x 6).base+h.val)).val=t.arity u)
    («fields»:∀i:Fin (nodes*maxArgs),t.active i→∀f:Fin 4,let j:=((finProdFinEquiv (m:=nodes) (n:=maxArgs)).symm i).2
      (config).nodeDigit (DescentOperandWidth.recordBits G S k tail drift 3 p) (nodeOf i).val gg.val
        (primitive ((previous f j x).base+h.val)).val=(t.pointer i).header f)
    (side:∀j,DescentTerminalSignedGrainWord.wing 3 (spec).cap (signed x j) primitive h gg
      (M:=(spec).groups) (Nat.zero_lt_of_lt gg.isLt)=t.chips j) :
    SourceRead config ((pointerPages_).source (N:=nodes) (d:=(spec).scalar.pointerBits) primitive x h) gg.val t := by
  have sizes:=DescentTerminalPointerDigits.input_bounds ((spec).groups) nodes
    (S.groupWidth k tail 0+k) (k*S.length) (2^(8+S.capGain*S.length)) nodeBits (Nat.clog 2 (maxArgs+1))
    (DescentOperandWidth.recordBits G S k tail drift 3 p) (DescentSignedCableCodec.width 3 (spec).cap)
  exact (pointerPages_).live primitive x h gg config rfl t sizes.2.2.1 sizes.2.2.2.1
    (fun _=>sizes.2.2.2.2.1) sizes.2.2.2.2.2 population arity «fields» side

include boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
/-- The observed scalar socket reads the native lookup value at the original
rectangular node/operand position. -/
theorem fixed_operand_digit {tags:ℕ} (x:Block k) (h:Fin H0) (gg:Fin (spec).groups) (u:Fin nodes) (j:Fin maxArgs)
    (hostWord:H0≤2^w) (outputRoom:(Nat.clog 2 (q+maxArgs+1)*(nodes*maxArgs))*(spec).groups≤w)
    (v:ℕ) (small:v<2^Nat.clog 2 (q+maxArgs+1))
    (denotes:(decode 3 config index ((pointerPages_).source (N:=nodes) (d:=(spec).scalar.pointerBits) primitive x h) gg.val).argument
      q G.b psize (finProdFinEquiv (u,j))=v) :
    venueField (cellAt (measured (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (w:=p) (groups:=(spec).groups)
        (MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=(spec).groups) ((spec).channels origin) 0) primitive h) (finProdFinEquiv (gg,x)))
      (nodeArg u j)=v := by
  let channel:=((spec).channels origin).primitive x 7
  have read:=fixed_operand_word (X:=X) (G:=G) (S:=S) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase) (w:=w)
    (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
    (rolePages:=rolePages) (ptr:=ptr) (m:=m) (homes:=homes) boot space matrixEnd roleBefore roleEnd
    ptrEnd ptrRows paidFit signedRows x h
  have enough:H0≤channel.size:=Nat.le_pow_clog (by decide) _
  have channelAt : (MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p)
      (groups:=(spec).groups) ((spec).channels origin) 0).channel (finProdFinEquiv (x,(7:Fin 8).succ)) = channel :=
    MaskAllocation.Channels.primitive_at ((spec).channels origin) x 7
  rw [DescentTerminalPointerIssue.family_digit (q:=q) (tags:=tags) (hid:=maxArgs) (p:=p) (MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=(spec).groups) ((spec).channels origin) 0)
    primitive channel.base x (congrArg Bank.base channelAt) (enough.trans_eq (congrArg Bank.size channelAt.symm)) hostWord h gg u j,read,
    Fin.val_cast_of_lt ((f7 _).isLt.trans_le (Nat.pow_le_pow_right (by decide) outputRoom))]
  simp only [DescentTerminalPointerDigits.output,digit_encode,denotes,Fin.val_cast_of_lt small]

local notation "cellsAt" v:arg => (pointerPages_).source (N:=nodes) (d:=(spec).scalar.pointerBits)
  primitive ((placement).block v) (b.target.home v)
local notation "physicalShape" t:arg => inputsAtShape (eqs).1 (eqs).2.1 t
open DescentBundleHistory DescentLocalPrivateNames DescentTerminalPortChart DescentTerminalBoundaryBasis

/-- The physically decoded prior is built from the real node, operand and wing
names. It suffices to read the fields of the actual occupied recipe slots. -/
theorem fixed_issued_rows {Tag B:Type} (v:(net).Site) (r:Recipe Tag B) (birth:r.Node↪ℕ)
    (fitsN:Fintype.card r.Node≤nodes) (fitsA:∀u,r.arity u≤ maxArgs) (operand:Slot r→DescentOperandStateBanks.Pointer)
    (panel:Fin (2*(placement).cap)→Option (DescentSharedCableNames.Stage.Live (placement).degree (placement).cap))
    (population:digit nodeBits ((placement).pos v).1.val
      (primitive ((((spec).channels origin).primitive ((placement).block v) 3).base+(b.target.home v).val)).val=Fintype.card r.Node)
    (widths:∀u:r.Node,(config).nodeDigit (Nat.clog 2 (maxArgs+1)) (DescentTerminalPointerIssue.row r birth fitsN u).val
      ((placement).pos v).1.val (primitive ((((spec).channels origin).primitive ((placement).block v) 6).base+(b.target.home v).val)).val=r.arity u)
    («fields»:∀(a:Slot r) (f:Fin 4),(config).nodeDigit (DescentOperandWidth.recordBits G S k tail drift 3 p)
      (DescentTerminalPointerIssue.row r birth fitsN a.1).val ((placement).pos v).1.val
      (primitive ((previous f (a.2.castLE (fitsA a.1)) ((placement).block v)).base+(b.target.home v).val)).val=(operand a).header f)
    (side:∀j,DescentTerminalSignedGrainWord.wing 3 (spec).cap (signed ((placement).block v) j) primitive (b.target.home v)
      ((placement).pos v).1 (M:=(spec).groups) (Nat.zero_lt_of_lt ((placement).pos v).1.isLt)=wingsAtShape (eqs).1 (eqs).2.1 panel j) :
    SourceRead config (cellsAt v) ((placement).pos v).1.val
      (physicalShape (issuedInputs r birth fitsN fitsA operand panel)) := by
  rw [issued_at_shape]
  let fixed:=wingsAtShape (eqs).1 (eqs).2.1 panel
  let inputs:=issuedInputs r birth fitsN fitsA operand fixed
  apply fixed_pointer_live (X:=X) (G:=G) (S:=S) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase) (w:=w)
    (paid:=paid) (actor:=actor) (roleBase:=roleBase) (signed:=signed)
    (rolePages:=rolePages) (matrix:=matrix) (ptr:=ptr) (m:=m) ((placement).block v) (b.target.home v)
    ((placement).pos v).1 inputs population
  · intro i hi
    let index_:Fin (Fintype.card r.Node):=⟨i.val,hi⟩
    let u:=(DescentTerminalChronologicalBooks.ordinal birth).symm index_
    have value:(DescentTerminalChronologicalBooks.ordinal birth u).val=index_.val:=
      congrArg (fun j:Fin (Fintype.card r.Node)=>j.val) ((DescentTerminalChronologicalBooks.ordinal birth).apply_symm_apply index_)
    have atRow:DescentTerminalPointerIssue.row r birth fitsN u=i:=Fin.ext value
    rw [←atRow]
    exact (widths u).trans (issued_arity r birth fitsN fitsA operand fixed u).symm
  · intro i «on» f
    obtain ⟨a,rfl⟩ : ∃a:Slot r,DescentTerminalPointerIssue.slot r birth fitsN fitsA a=i := by
      apply Classical.byContradiction
      intro miss
      exact inactive r birth fitsN fitsA inputs rfl (issued_arity r birth fitsN fitsA operand fixed) i
        (fun a same=>miss ⟨a,same⟩) «on»
    rw [show inputs.pointer (DescentTerminalPointerIssue.slot r birth fitsN fitsA a)=operand a from
      issued_pointer r birth fitsN fitsA operand fixed a]
    have pos : finProdFinEquiv.symm (DescentTerminalPointerIssue.slot r birth fitsN fitsA a) =
        (DescentTerminalPointerIssue.row r birth fitsN a.1,a.2.castLE (fitsA a.1)) := finProdFinEquiv.symm_apply_apply _
    simp only [nodeOf,pos]
    exact «fields» a f
  · exact side


include base boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
/-- At a reached site, actual archived input words, the signed roster and the
original phase's pointer classification determine the f7 value of every named
operand at the post-primitive socket. -/
theorem fixed_operand_from_origin {Tag:Type} {tags K:ℕ} (v:(net).Site)
    (recipe:Recipe Tag (BlockRef p (boundaryWidth net v))) (code:Tag→Fin tags)
    (birth:recipe.Node↪ℕ) (fitsN:Fintype.card recipe.Node≤nodes) (fitsA:∀u,recipe.arity u≤ maxArgs)
    (aliases:Slot recipe↪Fin K) (t:CellInputs (placement).degree (placement).cap nodes maxArgs)
    (qFit:NativeBranch.localLimit G S≤q) (hiddenFit:Fintype.card recipe.UsedWord≤ maxArgs)
    (hostWord:H0≤2^w)
    (outputRoom:(Nat.clog 2 (q+maxArgs+1)*(nodes*maxArgs))*(spec).groups≤w)
    (read:SourceRead config (cellsAt v) ((placement).pos v).1.val (physicalShape t))
    (prior:DescentTerminalPointerIssue.Origin net v recipe birth fitsN fitsA aliases (rank placement native S b.target.valid names v (pinRank v)) (pinRank v)
      (reindexed t (index ((cellsAt v) mcol).val ((cellsAt v) fcol).val)))
    (panels:t.chips=DescentSharedCableNames.Stage.signedPanel placement native S b.target.valid names
      (DescentSharedCableNames.Stage.home placement v))
    (u:recipe.Node) (j:Fin (recipe.arity u)) :
    venueField (cellAt (measured (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (w:=p) (groups:=(spec).groups)
        (MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=(spec).groups) ((spec).channels origin) 0) primitive (b.target.home v))
      (finProdFinEquiv (((placement).pos v).1,(placement).block v)))
      (nodeArg (row recipe birth fitsN u) (j.castLE (fitsA u)))=
      DescentTerminalBoundaryPointer.num (q:=q) net hp v (rank placement native S b.target.valid names v (pinRank v)) recipe code
        ((firstAlias recipe aliases).trans Fin.valEmbedding) u j := by
  have genuine:=reached_fixed_argument (q:=q) placement native S b.target.valid names v b.target.valid.coordinates (pinRank v)
    hp G.b psize (by rw [b.target.grain,Nat.mul_comm]) (fun _=>rfl) recipe code birth fitsN fitsA aliases t
    (eqs).1 (eqs).2.1 config (cellsAt v) ((placement).pos v).1.val index read prior panels u j
  have narrow:=reference_fits (q:=q) placement native S b.target.valid names v (pinRank v) hp recipe code aliases
    ((final_slots X G S b hp v).trans qFit) hiddenFit u j
  exact fixed_operand_digit (X:=X) (G:=G) (S:=S) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase) (w:=w)
    (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
    (rolePages:=rolePages) (ptr:=ptr) (m:=m) (homes:=homes) boot space matrixEnd roleBefore roleEnd
    ptrEnd ptrRows paidFit signedRows _ _ _ _ _ hostWord outputRoom _ narrow genuine

private theorem cast_panel_count {d d' c c' blockCount groups H:ℕ} (hd:d=d') (hc:c=c') (r:Rasters d' blockCount c')
    (mem:Memory w) (x:Fin blockCount) (h:Fin H) (g:Fin groups) :
    (grains (fun j=>DescentTerminalSignedGrainWord.wing d' c' (r.wing x j) mem h g (M:=groups)
      (Nat.zero_lt_of_lt g.isLt))).card=
    (grains (fun j=>DescentTerminalSignedGrainWord.wing d c ((presented hd hc r).wing x j) mem h g
      (M:=groups) (Nat.zero_lt_of_lt g.isLt))).card := by
  subst d';subst c';rfl

private theorem wing_shape {d c d' c' groups H blockCount w:ℕ} (hd:d=d') (hc:c=c') (r:Rasters d' blockCount c')
    (mem:Memory w) (x:Fin blockCount) (h:Fin H) (g:Fin groups) :
    wingsAtShape hd hc (fun j=>DescentTerminalSignedGrainWord.wing d c ((presented hd hc r).wing x j) mem h g (M:=groups)
      (Nat.zero_lt_of_lt g.isLt)) =
    (fun j=>DescentTerminalSignedGrainWord.wing d' c' (r.wing x j) mem h g (M:=groups)
      (Nat.zero_lt_of_lt g.isLt)) := by
  subst d';subst c';rfl

local notation "reachedPanel" v:arg => DescentSharedCableNames.Stage.signedPanel placement native S b.target.valid names
  (DescentSharedCableNames.Stage.home placement v)

/-- Read the actual selected signed panel as well as the four prior fields in
the scalar pointer dictionary's own fixed dimensions. -/
theorem fixed_pointer_issued_read {Tag B:Type} (v:(net).Site) (r:Recipe Tag B) (birth:r.Node↪ℕ)
    (fitsN:Fintype.card r.Node≤nodes) (fitsA:∀u,r.arity u≤ maxArgs) (operand:Slot r→DescentOperandStateBanks.Pointer)
    (population:digit nodeBits ((placement).pos v).1.val
      (primitive ((((spec).channels origin).primitive ((placement).block v) 3).base+(b.target.home v).val)).val=Fintype.card r.Node)
    (widths:∀u:r.Node,(config).nodeDigit (Nat.clog 2 (maxArgs+1)) (DescentTerminalPointerIssue.row r birth fitsN u).val
      ((placement).pos v).1.val (primitive ((((spec).channels origin).primitive ((placement).block v) 6).base+(b.target.home v).val)).val=r.arity u)
    («fields»:∀(a:Slot r) (f:Fin 4),(config).nodeDigit (DescentOperandWidth.recordBits G S k tail drift 3 p)
      (DescentTerminalPointerIssue.row r birth fitsN a.1).val ((placement).pos v).1.val
      (primitive ((previous f (a.2.castLE (fitsA a.1)) ((placement).block v)).base+(b.target.home v).val)).val=(operand a).header f)
    (wireBits:DescentSignedCableCodec.width (placement).degree (placement).cap*(S.groupCount S.length)≤w)
    (wings:∀block t,Reads ((measuredRack).wing block t) (fun h g=>DescentSignedCableCodec.encode
      (DescentPacking.PackedMatch.Local.Stage.Prepare.signed placement native S b.target.valid
        (Function.Embedding.refl _) hosts block t h g)) (S.groupCount S.length) primitive) :
    SourceRead config (cellsAt v) ((placement).pos v).1.val
      (physicalShape (issuedInputs r birth fitsN fitsA operand (reachedPanel v))) := by
  let x:Block k:=(placement).block v
  let h:Fin H0:=b.target.home v
  let g':Fin (S.groupCount S.length):=((placement).pos v).1
  have actual:(fun j=>DescentTerminalSignedGrainWord.wing (placement).degree (placement).cap
      ((measuredRack).wing x j) primitive h g' (M:=S.groupCount S.length) (Nat.zero_lt_of_lt g'.isLt))=reachedPanel v := by
    funext j
    exact DescentTerminalSignedGrainWord.stage_wing placement native S b.target.valid (Function.Embedding.refl _)
      hosts (measuredRack).wing primitive wings (Nat.zero_lt_of_lt g'.isLt) wireBits x j ((placement).pos v)
  apply fixed_issued_rows (X:=X) (G:=G) (S:=S) (q:=q) (drift:=drift) (op:=op) (headerRows:=headerRows)
    (paidRows:=paidRows) (origin:=origin) (romBase:=romBase) (w:=w) (paid:=paid) (actor:=actor) (roleBase:=roleBase)
    (b:=b) (signed:=signed) (rolePages:=rolePages) (matrix:=matrix) (ptr:=ptr) (m:=m)
    v r birth fitsN fitsA operand (reachedPanel v) population widths «fields»
  intro j
  exact (congrFun (wing_shape (eqs).1 (eqs).2.1 rack primitive x h g') j).symm.trans
    (congrFun (congrArg (wingsAtShape (eqs).1 (eqs).2.1) actual) j)

include base radix boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
/-- At the reached vertex the original f0 scan counts both the signed cable grains
and the immutable exterior copies. Both inputs are read on the primitive history. -/
theorem fixed_public_digit (qFit:NativeBranch.localLimit G S≤q)
    (outputBits:Nat.clog 2 (q+1)*(S.groupCount S.length)≤w)
    (wireBits:DescentSignedCableCodec.width (placement).degree (placement).cap*(S.groupCount S.length)≤w)
    (roster:∀i:Fin H0,(primitive (((spec).frozenRoster origin).base+i.val)).val=
      frozenRosterCode X G S b hp base i)
    (wings:∀block t,Reads ((measuredRack).wing block t) (fun h g=>DescentSignedCableCodec.encode
      (DescentPacking.PackedMatch.Local.Stage.Prepare.signed placement native S b.target.valid
        (Function.Embedding.refl _) hosts block t h g)) (S.groupCount S.length) primitive)
    (v:(net).Site) :
    digit (Nat.clog 2 (q+1)) ((placement).pos v).1.val
      (primitive ((((spec).channels origin).primitive ((placement).block v) 0).base+(b.target.home v).val)).val=
      DescentTerminalGraphRows.arity net p v := by
  let x:Block k:=(placement).block v
  let h:Fin H0:=b.target.home v
  let gg:Fin (S.groupCount S.length):=((placement).pos v).1
  let shape:=(spec).scalar
  have original:=fixed_public_row (X:=X) (G:=G) (S:=S) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (romBase:=romBase)
    (paid:=paid) (actor:=actor) (roleBase:=roleBase) (peer:=peer) (homes:=homes) (signed:=signed)
    (rolePages:=rolePages) (matrix:=matrix) (ptr:=ptr) (origin:=origin) (w:=w) (m:=m)
    (boot:=boot) (space:=space) (matrixEnd:=matrixEnd) (roleBefore:=roleBefore) (roleEnd:=roleEnd)
    (ptrEnd:=ptrEnd) (ptrRows:=ptrRows) (paidFit:=paidFit) (signedRows:=signedRows) (x:=x) (h:=h)
  have recode:=DescentTerminalPointerDigits.input_bounds ((spec).groups) nodes
    (S.groupWidth k tail 0+k) (k*S.length) (2^(8+S.capGain*S.length)) nodeBits (Nat.clog 2 (maxArgs+1))
    (DescentOperandWidth.recordBits G S k tail drift 3 p) (DescentSignedCableCodec.width 3 (spec).cap)
  have frozen:(primitive (((spec).frozenRoster origin).base+h.val)).val<2^shape.pointerBits:=by
    rw [roster]
    have a:=frozenRosterCode_lt X G S b hp base h
    rw [b.path.frozen_age] at a
    exact a.trans_le (Nat.pow_le_pow_right (by decide) recode.2.1)
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=(spec).layers origin
  have held:warmed (((spec).frozenRoster origin).base+h.val)=primitive (((spec).frozenRoster origin).base+h.val):=by
    apply original.2
    have early:((spec).frozenRoster origin).base+h.val<(spec).cohortEnd origin:=by
      change _+4*(spec).cohorts+h.val<_+4*(spec).cohorts+H0+1
      omega
    omega
  have kept:∀j,warmed ((signed x j).base+h.val)=primitive ((signed x j).base+h.val):=by
    intro j
    apply original.2
    have en:=boot.oldCables x j
    have size : H0 ≤ (signed x j).size := signedRows x j
    have span := (Nat.add_lt_add_left (h.isLt.trans_le size) (signed x j).base).trans_le en
    exact span.trans_le (by omega)
  have measuredCount:=(cast_panel_count (w:=w) (eqs).1 (eqs).2.1 rack primitive x h gg)
  have signedValues: (fun j=>DescentTerminalSignedGrainWord.wing (placement).degree (placement).cap
      ((measuredRack).wing x j) primitive h gg (M:=S.groupCount S.length) (Nat.zero_lt_of_lt gg.isLt))=
      DescentSharedCableNames.Stage.signedPanel placement native S b.target.valid names
        (DescentSharedCableNames.Stage.home placement v):=by
    funext j
    exact DescentTerminalSignedGrainWord.stage_wing placement native S b.target.valid (Function.Embedding.refl _)
      hosts (measuredRack).wing primitive wings (Nat.zero_lt_of_lt gg.isLt) wireBits x j ((placement).pos v)
  have total:=boundary_count placement native S b.target.valid names v b.target.valid.coordinates hp
    G.b psize (by rw [b.target.grain,Nat.mul_comm]) (fun _=>by rfl)
  have pinCount:DescentTerminalFrozenRoster.length (k*S.length)
      (primitive (((spec).frozenRoster origin).base+h.val)).val=Fintype.card (Attached net v):=by
    rw [roster,←b.path.frozen_age]
    exact actual_pin_count X G S b hp base v
  have physical:=public_from_rows (D:=3) (N:=nodes) (d:=shape.pointerBits) pointerPages_ warmed primitive x h gg config
    q G.b psize (k*S.length) recode.2.2.2.2.2 frozen held kept _ ((final_slots X G S b hp v).trans qFit) (by
      change _*G.b+DescentTerminalFrozenRoster.length (k*S.length)
        (primitive (((spec).frozenRoster origin).base+h.val)).val*psize=_
      exact (congrArg₂ (fun a b => a*G.b+b*psize)
        (measuredCount.trans (congrArg (fun panel => (grains panel).card) signedValues)) pinCount).trans total)
  rw [original.1,Fin.val_cast_of_lt ((f0 _).isLt.trans_le (Nat.pow_le_pow_right (by decide) outputBits))]
  exact physical

include base radix low boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
/-- The prior actor raster is read on the incoming execution. The actual bitmap
printed for the Book is produced by repacking it, then retained through the
primitive writers. The original sorted neighbors and signed wings are retained
at every address below the first new literal. -/
theorem fixed_primitive_mask_and_count_words
    (actorLow:∀b,(actor b).base+(actor b).size≤romBase)
    (source:∀b,Reads (actor b) (liveBits b) (spec).actorLanes m) :
    (∀h:Fin H0,∀b:Block k,primitive (((measuredRack).geometry.occupied b).base+h.val)=
      ((encode 1 (S.groupCount S.length) (liveBits b h)).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    (∀j,j<romBase→primitive j=m j) ∧
    ∀(charges:Block k→Fin H0→Fin (S.groupCount S.length)→Cell (spec).paidBits)
      (hist:Fin H0→Cell (spec).externalBits),
      (∀b,(paid b).base+(paid b).size≤romBase) →
      (∀b,Reads (paid b) (charges b) (spec).paidLanes m) →
      (∀h:Fin H0,primitive (((spec).census origin).base+h.val)=((hist h).val:Computability.VPVNP.BurstRAM.Word w)) →
      ∀(x:Block k)(h:Fin H0),primitive ((((spec).channels origin).primitive x 3).base+h.val)=
        (DescentTerminalPopulation.words (M:=(spec).paidLanes) nodeBits (charges x) (fun i=>(hist i).val) h:Computability.VPVNP.BurstRAM.Word w) := by
  have roles:=(spec).role_fits origin space tagBits rolePages roleBase roleBefore roleEnd
  have ptrE:∀f j b,(previous f j b).base+(previous f j b).size≤(spec).cohortEnd origin:=by
    intro f j b
    unfold DescentTerminalOperandRepack.padded
    split
    · exact ptrEnd _ _ _
    · exact boot.oldPaid _
  have ptrH:∀f j b,shops≤(previous f j b).size:=by
    intro f j b
    unfold DescentTerminalOperandRepack.padded
    split
    · exact ptrRows _ _ _
    · exact paidFit _
  have cols:0<(spec).scalar.columns:=by
    change 0<3+nodes+4*(nodes*maxArgs)+2*(spec).cap
    omega
  have ptrFit:=(spec).pointer_fits origin matrix previous signed space matrixEnd ptrE ptrH boot.oldCables signedRows nodes
  have early:=(spec).earlier_population origin paid actor signed peer (shelf).total (shelf).modulo homes (shelf).boundaries boot
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=(spec).layers origin
  have room:(spec).primitive origin<2^w:=by omega
  have lim:(spec).scalar.finish ((spec).primitive origin)<2^w:=by
    change (spec).weights origin<2^w
    omega
  have kit:=(spec).scalar.realized ((spec).primitive origin) ((spec).population origin) _ ((spec).prior origin) lim cols
  have write:=(spec).scalar.primitive_any ((spec).primitive origin) ((spec).population origin)
    first second chart f0 f7 q maxArgs nodes maxArgs (spec).groups p paidMem kit roles.1
    (ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) roles.2) ptrFit
  have old:=(spec).purchased_prior origin nodeBits paid actor signed peer (shelf).total (shelf).modulo homes
    (shelf).boundaries literalized boot space
  have start:romBase≤(shelf).stop:=by change romBase≤romBase+_;exact Nat.le_add_right ..
  have co:origin≤(spec).cohortEnd origin:=(spec).cohort_le origin
  have inserted:=(shelf).install m (show (shelf).stop<2^w by omega)
  have pos:0<(spec).actorLanes:=by
    change 0<S.baseGroups*S.radix^_
    rw [base,radix]
    positivity
  have slots (b) (j:Row shops (spec).groups (spec).actorLanes):
      literalized ((actor b).base+(row shops (spec).groups (spec).actorLanes j).val)=
        ((data (liveBits b) j).val:Computability.VPVNP.BurstRAM.Word w):=by
    have hit:((actor b).base+(row shops (spec).groups (spec).actorLanes j).val)<romBase:=
      (Nat.add_lt_add_left ((row shops (spec).groups (spec).actorLanes j).isLt.trans_le (boot.actorRows b)) _).trans_le (actorLow b)
    exact (inserted.2.2.2 _ (.inl hit)).trans (source b j)
  have actual:=DescentTerminalPriorArena.repacked_actor (spec).scalar (spec).groups (spec).paidLanes
    (spec).actorLanes (spec).paidBits (spec).externalBits ((spec).cohortEnd origin) paid actor ((spec).census origin)
    nodeBits literalized early room pos liveBits slots
  refine ⟨?_,?_,?_⟩
  · intro h block
    rw [raster_geometry]
    have valid:=kit.keep_actor block
    have earlier:=kit.old_actor block
    have frame:=write.2.2 (((rack).geometry.occupied block).base+h.val)
      (.inl ((Nat.add_lt_add_left (h.isLt.trans_le valid) _).trans_le earlier))
    exact frame.trans (actual block h)
  · intro j hit
    exact (write.2.2 _ (.inl (by omega))).trans
      ((old.2.2 _ (.inl (by omega))).trans (inserted.2.2.2 _ (.inl hit)))
  · intro inputCounts hist paidLow paidReads history x h
    have counts (b) (j:Row shops (spec).groups (spec).paidLanes):
        literalized ((paid b).base+(row shops (spec).groups (spec).paidLanes j).val)=
          ((data (inputCounts b) j).val:Computability.VPVNP.BurstRAM.Word w):=by
      have hit := (Nat.add_lt_add_left ((row shops (spec).groups (spec).paidLanes j).isLt.trans_le (boot.paidRows b)) _).trans_le (paidLow b)
      exact (inserted.2.2.2 _ (.inl hit)).trans (paidReads b j)
    have census (i:Fin H0) : literalized (((spec).census origin).base+i.val)=((hist i).val:Computability.VPVNP.BurstRAM.Word w) := by
      have left:((spec).census origin).base+i.val<(spec).cohortEnd origin :=
        (Nat.add_lt_add_left (i.isLt.trans_le early.extSize) _).trans_le early.extEnd
      exact ((write.2.2 _ (.inl (by omega))).trans (old.2.2 _ (.inl left))).symm.trans (history i)
    have result:=DescentTerminalPriorArena.issued (spec).scalar (spec).groups (spec).paidLanes (spec).actorLanes
      (spec).paidBits (spec).externalBits 1 ((spec).cohortEnd origin) paid actor ((spec).census origin) early room
      nodeBits (fun (_:Fin (spec).scalar.blocks)(value:Cell 1)=>value) literalized pos (fun _=>rfl)
      inputCounts hist liveBits counts census slots
    have before:=kit.old_population x
    have idx:(((spec).channels origin).primitive x 3).base+h.val<(spec).primitive origin :=
      (Nat.add_lt_add_left (h.isLt.trans_le (kit.keep_family x 3)) _).trans_le before
    exact (write.2.2 _ (.inl idx)).trans (result.2.2.1 x h)


include base radix low boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
theorem fixed_primitive_actor_words
    (actorLow:∀b,(actor b).base+(actor b).size≤romBase)
    (source:∀b,Reads (actor b) (liveBits b) (spec).actorLanes m) :
    (∀h:Fin H0,∀b:Block k,primitive (((measuredRack).geometry.occupied b).base+h.val)=
      ((encode 1 (S.groupCount S.length) (liveBits b h)).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    ∀j,j<romBase→primitive j=m j := by
  have result:=fixed_primitive_mask_and_count_words (X:=X) (G:=G) (S:=S) (b:=b) (base:=base) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase) (w:=w)
    (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
    (rolePages:=rolePages) (ptr:=ptr) (m:=m) (homes:=homes) low boot space matrixEnd roleBefore
    roleEnd ptrEnd ptrRows paidFit signedRows actorLow source
  exact ⟨result.1,result.2.1⟩




include base radix low boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
/-- The old paid census and the attained exterior cohorts add to the genuine primitive node count. -/
theorem fixed_population_word (height:0<S.height) (geometry:G.b≤2^S.capGain)
    (actorLow:∀b,(actor b).base+(actor b).size≤romBase)
    (actorRead:∀b,Reads (actor b) (liveBits b) (spec).actorLanes m)
    (paidLow:∀b,(paid b).base+(paid b).size≤romBase)
    (paidRead:∀x:Block k,Reads (paid x)
      (fun h g=>DescentPacking.PackedMatch.Local.Stage.Census.count placement (Equiv.refl _) hosts (S.censusBits p) h g x)
      (spec).paidLanes m)
    (extRead:∀h:Fin H0,primitive (((spec).census origin).base+h.val)=
      (Computability.BorderVNP.FragmentBucket.count (cohortHome X G S b hp base) h:Computability.VPVNP.BurstRAM.Word w)) :
    ∀v:(net).Site,digit nodeBits ((placement).pos v).1.val
      (primitive ((((spec).channels origin).primitive ((placement).block v) 3).base+(b.target.home v).val)).val=
      Fintype.card ((archive X G S b hp).bit.recipe v).Node := by
  have result:=fixed_primitive_mask_and_count_words (X:=X) (G:=G) (S:=S) (b:=b) (base:=base) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase) (w:=w)
    (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
    (rolePages:=rolePages) (ptr:=ptr) (m:=m) (homes:=homes) low boot space matrixEnd roleBefore
    roleEnd ptrEnd ptrRows paidFit signedRows actorLow actorRead
  let counts:=Computability.BorderVNP.FragmentBucket.count (cohortHome X G S b hp base)
  have extFit (h:Fin H0):counts h<2^((spec).externalBits):=by
    change counts h<2^(8+S.capGain*S.length+1)
    exact (cohort_cap X G S b hp base h).trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
  let hist:=fun h:Fin H0=>(⟨counts h,extFit h⟩:Cell (spec).externalBits)
  let charges:=fun (x:Block k) h g=>
    DescentPacking.PackedMatch.Local.Stage.Census.count placement (Equiv.refl _) hosts (S.censusBits p) h g x
  have installed:=result.2.2 charges hist paidLow paidRead extRead
  have bound:=((placement).census_caps_at S b.target.valid height le_rfl
    (b.target.grain.trans (S.grain_terminal G.b p).symm) b.target.edges geometry).2
  have recordFit (v:(net).Site):((placement).records v).length<2^(S.censusBits p):=
    (DescentPaidResidentCount.record_bound placement S b.target.valid v).trans_lt bound
  have nodeFit (v:(net).Site):Fintype.card ((archive X G S b hp).bit.recipe v).Node<2^nodeBits:=
    (site_nodes X G S b hp height v).trans_lt ((Nat.lt_succ_self _).trans_le (Nat.le_pow_clog (by decide) _))
  have lanes:0<(spec).paidLanes:=by
    change 0<S.baseGroups*S.radix^_
    rw [base,radix]
    positivity
  have roleDigit:1≤DescentTerminalCombinedRole.width colors groupLimit maxArgs p drift (1:Fin 6):=by
    change 0<Nat.clog 2 (groupLimit+1)
    apply Nat.clog_pos (by decide)
    have := Nat.le_max_left 8 (2^S.capGain)
    omega
  have laneBound:nodeBits≤nodes:=(Nat.clog_le_iff_le_pow (by decide)).2
    (show nodes+1≤2^nodes from Nat.lt_two_pow_self)
  have packBound:nodeBits*(S.groupCount S.length)≤tagBits (1:Fin 6):=by
    apply Nat.mul_le_mul_right
    exact laneBound.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right nodes roleDigit)
  have term:2^(tagBits (1:Fin 6))≤DescentTerminalRoleTables.marks tagBits:=
    Finset.single_le_sum (f:=fun f:Fin 6=>2^(tagBits f)) (fun _ _=>Nat.zero_le _) (Finset.mem_univ _)
  have sizes:DescentTerminalRoleTables.marks tagBits≤DescentTerminalRoleTables.count tagBits:=by
    unfold DescentTerminalRoleTables.count
    omega
  obtain ⟨z₁,z₂,z₃,z₄,z₅,z₆,z₇,z₈,z₉⟩:=(spec).layers origin
  have short:2^(tagBits (1:Fin 6))<2^w:=by omega
  have wide:nodeBits*(S.groupCount S.length)≤w:=by
    by_contra! bad
    exact (not_le_of_gt short) (Nat.pow_le_pow_right (by decide) (bad.le.trans packBound))
  intro v
  rw [installed ((placement).block v) (b.target.home v)]
  exact true_population_word X G S b hp base lanes wide recordFit nodeFit v

include base radix low boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
private theorem venue_reads {tags venueLimit:ℕ} (io:DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (prior:Memory w) (floor precision:ℕ)
    (dateLog:stageVenue b.target b.target.valid.host io (S.groupCount S.length) precision venueLimit
      (b.target.venueRoster b.target.valid.host) prior)
    (frame:∀a<floor,m a=prior a) (resident:floor≤romBase)
    (actorEnd:∀i,(actor i).base+(actor i).size≤floor)
    (source:∀i,Reads (actor i) (liveBits i) (spec).actorLanes prior)
    (physicalPeer:(measuredRack).roster=io.roster)
    (physicalWings:∀i t,(measuredRack).wing i t=io.wire i.val t.val)
    (stored:∀(i:Block k)(t:Fin (2*(placement).cap)),(io.wire i.val t.val).base+(io.wire i.val t.val).size≤floor)
    (cableRoom:∀i:Block k,∀t:Fin (2*(placement).cap),
      H0*chunks (S.groupCount S.length) (S.groupCount S.length)≤(io.wire i.val t.val).size)
    (peerEnd:io.roster.base+io.roster.size≤floor)
    (price:2^(spec).printBits<2^w) (word:2<2^w) (hostFit:H0≤2^w) :
    ((∀h:Fin H0,∀b:Block k,primitive (((measuredRack).geometry.occupied b).base+h.val)=
      ((encode 1 (S.groupCount S.length) (liveBits b h)).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    ((∀v:(net).Site,venueField (cellAt
      (measured (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (w:=p) (groups:=S.groupCount S.length)
        (MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=S.groupCount S.length) (measuredRack).geometry 0) primitive (hosts ((placement).pos v).2)) (finProdFinEquiv (((placement).pos v).1,(placement).block v))) publicArity=
      DescentTerminalGraphRows.arity net p v) →
      Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=Nat.clog 2 (q+1)) placement hosts S b.target.valid
      b.target.order (b.target.terminalRoster b.target.valid.host) measuredRack primitive)) ∧
    (∀ hp : 0 < p, NativeBranch.localLimit G S≤q → (∀i:Fin H0,(primitive (((spec).frozenRoster origin).base+i.val)).val=
      frozenRosterCode X G S b hp base i) → (∀v:(net).Site,venueField (cellAt
      (measured (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (w:=p) (groups:=S.groupCount S.length)
        (MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=S.groupCount S.length) (measuredRack).geometry 0) primitive (hosts ((placement).pos v).2)) (finProdFinEquiv (((placement).pos v).1,(placement).block v))) publicArity=
      DescentTerminalGraphRows.arity net p v)) := by
  have old (i):Reads (actor i) (liveBits i) (spec).actorLanes m:=by
    intro r
    have x:=(row shops (spec).groups (spec).actorLanes r).isLt.trans_le (boot.actorRows i)
    exact (frame _ ((Nat.add_lt_add_left x _).trans_le (actorEnd i))).trans (source i r)
  have set_:=fixed_primitive_actor_words (X:=X) (G:=G) (S:=S) (b:=b) (base:=base) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase) (w:=w)
    (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
    (rolePages:=rolePages) (ptr:=ptr) (m:=m) (homes:=homes) low boot space matrixEnd roleBefore
    roleEnd ptrEnd ptrRows paidFit signedRows (fun i=>(actorEnd i).trans resident) old
  have same (i:ℕ) (hi:i<floor):primitive i=prior i:=
    (set_.2 i (hi.trans_le resident)).trans (frame i hi)
  let groups:=S.groupCount S.length
  let side:=DescentSignedCableCodec.width (placement).degree (placement).cap
  have dims:(spec).printBits=2+groups*max (max 1 (Nat.clog 2 (q+1))) side:=by
    dsimp only [groups,side]
    rw [(eqs).1,(eqs).2.1]
    rfl
  have cost:side*groups≤(spec).printBits:=by
    rw [Nat.mul_comm,dims]
    exact (Nat.mul_le_mul_left groups (Nat.le_max_right _ side)).trans (Nat.le_add_left ..)
  have wordBits:(spec).printBits≤w:=by
    by_contra! bad
    exact (not_le_of_gt price) (Nat.pow_le_pow_right (by decide) bad.le)
  have gPos:0<groups:=by change 0<S.baseGroups*S.radix^_;rw [base,radix];positivity
  have chunksOne:chunks groups groups=1:=covered_chunks gPos le_rfl
  have wingReads : ∀block t,Reads ((measuredRack).wing block t) (fun h g=>DescentSignedCableCodec.encode
      (DescentPacking.PackedMatch.Local.Stage.Prepare.signed placement native S b.target.valid (Function.Embedding.refl _) hosts block t h g)) groups primitive := by
    intro i t r
    rw [physicalWings]
    have n:=(row H0 groups groups r).isLt.trans_le (cableRoom i t)
    exact (same _ ((Nat.add_lt_add_left n _).trans_le (stored i t))).trans (dateLog.2.2.2.1 i t r)
  refine ⟨⟨set_.1,?_⟩,?_⟩
  · intro scalar
    refine fixed_primitive_raster (X:=X) (G:=G) (S:=S) (b:=b) (tags:=tags) (q:=q) (drift:=drift)
      (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase)
      (w:=w) (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
      (rolePages:=rolePages) (ptr:=ptr) (m:=m) (b.target.terminalRoster b.target.valid.host)
      (b.target.terminal_roster_near b.target.valid.host) ?_ word price hostFit set_.1 scalar
      groups le_rfl (cost.trans wordBits) wingReads ?_
    · intro h j z actual
      rw [physicalPeer]
      have hold:=DescentTerminalCountWidthPair.bank_before prior primitive floor same
        io.roster peerEnd ((h.val*(placement).degree+j.val:ℕ):Computability.VPVNP.BurstRAM.Word w)
      exact hold.trans (b.target.terminal_roster_reads b.target.valid.host io dateLog h j z actual)
    · intro i t
      rw [physicalWings]
      simpa only [show S.groupCount S.length=groups from rfl,chunksOne,Nat.mul_one] using cableRoom i t
  · intro hp qFit roster v
    have enumBits:Nat.clog 2 (q+1)*groups≤w:=by
      have width:Nat.clog 2 (q+1)≤ max (max 1 (Nat.clog 2 (q+1))) side:=(Nat.le_max_right ..).trans (Nat.le_max_left ..)
      have bound:=Nat.mul_le_mul_left groups width
      rw [dims] at wordBits
      rw [Nat.mul_comm];omega
    have read:=fixed_public_digit (hp:=hp) (X:=X) (G:=G) (S:=S) (b:=b) (base:=base) (q:=q) (drift:=drift)
      (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase) (w:=w)
      (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
      (rolePages:=rolePages) (ptr:=ptr) (m:=m) (homes:=homes) boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows
      paidFit signedRows qFit enumBits (cost.trans wordBits) roster wingReads v
    have rowsize:H0≤(((spec).channels origin).primitive ((placement).block v) 0).size:= by
      change H0≤2^Nat.clog 2 H0
      exact Nat.le_pow_clog (by decide) _
    rw [raster_geometry]
    let sourceShelf := MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p)
      (groups:=S.groupCount S.length) (rack).geometry 0
    have placed : sourceShelf.channel (finProdFinEquiv ((placement).block v,(0:Fin 8).succ)) =
        ((spec).channels origin).primitive ((placement).block v) 0 := MaskAllocation.Channels.primitive_at _ _ _
    exact (DescentTerminalPointerIssue.public_field (q:=q) (tags:=tags) (N:=nodes) (hid:=maxArgs)
      (M:=maxArgs) (p:=p) sourceShelf primitive ((placement).block v)
      ((((spec).channels origin).primitive ((placement).block v) 0).base) (congrArg Bank.base placed) (rowsize.trans_eq (congrArg Bank.size placed.symm)) hostFit
      (b.target.home v) (((placement).pos v).1)).trans read

include base radix low boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
/-- Bind all three geographic fields to the attained original date, using the
same actor, peer, and cable pages as the deposited earlier venue. -/
theorem fixed_venue_inputs {tags venueLimit:ℕ} (io:DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (prior:Memory w) (floor precision:ℕ)
    (dateLog:stageVenue b.target b.target.valid.host io (S.groupCount S.length) precision venueLimit
      (b.target.venueRoster b.target.valid.host) prior)
    (frame:∀a<floor,m a=prior a) (resident:floor≤romBase)
    (actorEnd:∀i,(actor i).base+(actor i).size≤floor)
    (source:∀i,Reads (actor i) (liveBits i) (spec).actorLanes prior)
    (physicalPeer:(measuredRack).roster=io.roster)
    (physicalWings:∀i t,(measuredRack).wing i t=io.wire i.val t.val)
    (stored:∀(i:Block k)(t:Fin (2*(placement).cap)),(io.wire i.val t.val).base+(io.wire i.val t.val).size≤floor)
    (cableRoom:∀i:Block k,∀t:Fin (2*(placement).cap),
      H0*chunks (S.groupCount S.length) (S.groupCount S.length)≤(io.wire i.val t.val).size)
    (peerEnd:io.roster.base+io.roster.size≤floor)
    (price:2^(spec).printBits<2^w) (word:2<2^w) (hostFit:H0≤2^w) :
    ((∀h:Fin H0,∀b:Block k,primitive (((measuredRack).geometry.occupied b).base+h.val)=
      ((encode 1 (S.groupCount S.length) (liveBits b h)).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    ((∀v:(net).Site,venueField (cellAt
      (measured (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (w:=p) (groups:=S.groupCount S.length)
        (MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=S.groupCount S.length) (measuredRack).geometry 0) primitive (hosts ((placement).pos v).2)) (finProdFinEquiv (((placement).pos v).1,(placement).block v))) publicArity=
      DescentTerminalGraphRows.arity net p v) →
      Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=Nat.clog 2 (q+1)) placement hosts S b.target.valid
      b.target.order (b.target.terminalRoster b.target.valid.host) measuredRack primitive)) ∧
    (NativeBranch.localLimit G S≤q → (∀i:Fin H0,(primitive (((spec).frozenRoster origin).base+i.val)).val=
      frozenRosterCode X G S b hp base i) → (∀v:(net).Site,venueField (cellAt
      (measured (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (w:=p) (groups:=S.groupCount S.length)
        (MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=S.groupCount S.length) (measuredRack).geometry 0) primitive (hosts ((placement).pos v).2)) (finProdFinEquiv (((placement).pos v).1,(placement).block v))) publicArity=
      DescentTerminalGraphRows.arity net p v)) := by
  have reached := venue_reads (tags:=tags) (X:=X) (G:=G) (S:=S) (b:=b) (base:=base) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase) (w:=w)
    (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
    (rolePages:=rolePages) (ptr:=ptr) (m:=m) (homes:=homes) low boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows
    paidFit signedRows io prior floor precision dateLog frame resident actorEnd source physicalPeer physicalWings stored cableRoom peerEnd price word hostFit
  exact ⟨reached.1,reached.2 hp⟩

include base radix low boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
theorem fixed_raster_actor_at_venue {tags venueLimit:ℕ} (io:DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (prior:Memory w) (floor precision:ℕ)
    (dateLog:stageVenue b.target b.target.valid.host io (S.groupCount S.length) precision venueLimit
      (b.target.venueRoster b.target.valid.host) prior)
    (frame:∀a<floor,m a=prior a) (resident:floor≤romBase)
    (actorEnd:∀i,(actor i).base+(actor i).size≤floor)
    (source:∀i,Reads (actor i) (liveBits i) (spec).actorLanes prior)
    (physicalPeer:(measuredRack).roster=io.roster)
    (physicalWings:∀i t,(measuredRack).wing i t=io.wire i.val t.val)
    (stored:∀(i:Block k)(t:Fin (2*(placement).cap)),(io.wire i.val t.val).base+(io.wire i.val t.val).size≤floor)
    (cableRoom:∀i:Block k,∀t:Fin (2*(placement).cap),
      H0*chunks (S.groupCount S.length) (S.groupCount S.length)≤(io.wire i.val t.val).size)
    (peerEnd:io.roster.base+io.roster.size≤floor)
    (price:2^(spec).printBits<2^w) (word:2<2^w) (hostFit:H0≤2^w) :
    (∀h:Fin H0,∀b:Block k,primitive (((measuredRack).geometry.occupied b).base+h.val)=
      ((encode 1 (S.groupCount S.length) (liveBits b h)).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    ((∀v:(net).Site,venueField (cellAt
      (measured (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (w:=p) (groups:=S.groupCount S.length)
        (MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=S.groupCount S.length) (measuredRack).geometry 0) primitive (hosts ((placement).pos v).2)) (finProdFinEquiv (((placement).pos v).1,(placement).block v))) publicArity=
      DescentTerminalGraphRows.arity net p v) →
      Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=Nat.clog 2 (q+1)) placement hosts S b.target.valid
      b.target.order (b.target.terminalRoster b.target.valid.host) measuredRack primitive) := by
  exact (venue_reads (tags:=tags) (X:=X) (G:=G) (S:=S) (b:=b) (base:=base) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase) (w:=w)
    (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
    (rolePages:=rolePages) (ptr:=ptr) (m:=m) (homes:=homes) low boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows
    paidFit signedRows io prior floor precision dateLog frame resident actorEnd source physicalPeer physicalWings stored cableRoom peerEnd price word hostFit).1

include base radix low boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
/-- Read the remaining Book fields after measuring the native public arity. -/
theorem fixed_raster_at_venue {tags venueLimit:ℕ} (io:DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (prior:Memory w) (floor precision:ℕ)
    (dateLog:stageVenue b.target b.target.valid.host io (S.groupCount S.length) precision venueLimit
      (b.target.venueRoster b.target.valid.host) prior)
    (frame:∀a<floor,m a=prior a) (resident:floor≤romBase)
    (actorEnd:∀i,(actor i).base+(actor i).size≤floor)
    (source:∀i,Reads (actor i) (liveBits i) (spec).actorLanes prior)
    (physicalPeer:(measuredRack).roster=io.roster)
    (physicalWings:∀i t,(measuredRack).wing i t=io.wire i.val t.val)
    (stored:∀(i:Block k)(t:Fin (2*(placement).cap)),(io.wire i.val t.val).base+(io.wire i.val t.val).size≤floor)
    (cableRoom:∀i:Block k,∀t:Fin (2*(placement).cap),
      H0*chunks (S.groupCount S.length) (S.groupCount S.length)≤(io.wire i.val t.val).size)
    (peerEnd:io.roster.base+io.roster.size≤floor)
    (price:2^(spec).printBits<2^w) (word:2<2^w) (hostFit:H0≤2^w)
    (scalar:∀v:(net).Site,venueField (cellAt
      (measured (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (w:=p) (groups:=S.groupCount S.length)
        (MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=S.groupCount S.length) (measuredRack).geometry 0) primitive (hosts ((placement).pos v).2)) (finProdFinEquiv (((placement).pos v).1,(placement).block v))) publicArity=
      DescentTerminalGraphRows.arity net p v) :
    Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=Nat.clog 2 (q+1)) placement hosts S b.target.valid
      b.target.order (b.target.terminalRoster b.target.valid.host) measuredRack primitive := by
  exact (fixed_raster_actor_at_venue (tags:=tags) (X:=X) (G:=G) (S:=S) (b:=b) (base:=base) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase)
    (w:=w) (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
    (rolePages:=rolePages) (ptr:=ptr) (m:=m) (homes:=homes) low boot space matrixEnd roleBefore
    roleEnd ptrEnd ptrRows paidFit signedRows io prior floor precision dateLog frame resident actorEnd source
    physicalPeer physicalWings stored cableRoom peerEnd price word hostFit).2 scalar

include base radix low boot space matrixEnd roleBefore roleEnd ptrEnd ptrRows paidFit signedRows in
theorem fixed_raster_of_venue {tags:ℕ} (io:DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (prior:Memory w) (floor precision:ℕ)
    (dateLog:stageVenue b.target b.target.valid.host io (S.groupCount S.length) precision floor
      (b.target.venueRoster b.target.valid.host) prior)
    (frame:∀a<floor,m a=prior a) (resident:floor≤romBase)
    (actorEnd:∀i,(actor i).base+(actor i).size≤floor)
    (source:∀i,Reads (actor i) (liveBits i) (spec).actorLanes prior)
    (physicalPeer:(measuredRack).roster=io.roster)
    (physicalWings:∀i t,(measuredRack).wing i t=io.wire i.val t.val)
    (stored:∀(i:Block k)(t:Fin (2*(placement).cap)),(io.wire i.val t.val).base+(io.wire i.val t.val).size≤floor)
    (cableRoom:∀i:Block k,∀t:Fin (2*(placement).cap),
      H0*chunks (S.groupCount S.length) (S.groupCount S.length)≤(io.wire i.val t.val).size)
    (price:2^(spec).printBits<2^w) (word:2<2^w) (hostFit:H0≤2^w)
    (scalar:∀v:(net).Site,venueField (cellAt
      (measured (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (w:=p) (groups:=S.groupCount S.length)
        (MaskAllocation.shelf (q:=q) (t:=tags) (H:=maxArgs) (N:=nodes) (A:=maxArgs) (p:=p) (groups:=S.groupCount S.length) (measuredRack).geometry 0) primitive (hosts ((placement).pos v).2)) (finProdFinEquiv (((placement).pos v).1,(placement).block v))) publicArity=
      DescentTerminalGraphRows.arity net p v) :
    Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=Nat.clog 2 (q+1)) placement hosts S b.target.valid
      b.target.order (b.target.terminalRoster b.target.valid.host) measuredRack primitive := by
  exact fixed_raster_at_venue (X:=X) (G:=G) (S:=S) (b:=b) (base:=base) (q:=q) (drift:=drift)
    (op:=op) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=origin) (romBase:=romBase)
    (w:=w) (peer:=peer) (paid:=paid) (actor:=actor) (signed:=signed) (matrix:=matrix) (roleBase:=roleBase)
    (rolePages:=rolePages) (ptr:=ptr) (m:=m) (homes:=homes) low boot space matrixEnd roleBefore
    roleEnd ptrEnd ptrRows paidFit signedRows io prior floor precision dateLog frame resident actorEnd source
    physicalPeer physicalWings stored cableRoom dateLog.1.roster.2.2 price word hostFit scalar

end NativeActors

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
