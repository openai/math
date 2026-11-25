import OAI.Hierarchy.DescentTerminalCompleteFields
import OAI.Hierarchy.DescentTerminalRolePrefix
import OAI.Hierarchy.DescentTerminalPrimitivePublicPair

namespace OAI
/-! # Fixed terminal public/operand dispatch followed by the distinct-count and width scans -/
namespace Hierarchy.DescentTerminalNormalizedFields
open Computability.BorderVNP.Crossing DescentSixParty DescentSharedCableNames DescentKernelHistory DescentTerminalPortChart
open DescentBundleHistory DescentTerminalBoundaryBasis DescentCompiler DescentColonies DescentLocalPrivateNames
open DescentOperandStateBanks DescentTerminalPointerDigits DescentTerminalChronologicalBooks DescentTerminalGraphPositions
open DescentTerminalPointerIssue DescentTerminalVertexFields DescentTerminalRecipeRows DescentTerminalSiteShelves
open ThreeFlat.Routing Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentSIMDLookup
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option maxHeartbeats 600000
set_option quotPrecheck false
variable {F P J V U:Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k step p q N M K tags H0:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:AtomSchedule) (ready:A.StateBounds S step)
    (homes:Stage.Host J V k↪ℕ) (coords:Function.Injective (fun s=>(A.pos s,A.block s))) (hp:0<p)
    (layout:Order W.graph H0 p) (host:Fin H0) (z:Fin (layout.site host).nodes)
    (rs:∀v:W.graph.Site,BitRecipe U (Boundary W.graph v) (boundaryWidth W.graph v))
    (sh:∀v,Shape p (rs v)) (code:U×List (List SliceCode)→Fin tags)
local notation "G'" => W.graph
local notation "atNode" => layout.node host z
local notation "rec" => fun v=>(sh v).recipe hp
local notation "r" => (sh atNode).recipe hp
variable (orders:∀v,((sh v).recipe hp).Node↪ℕ) (aliases:∀v,Slot ((sh v).recipe hp)↪Fin K)
local notation "active" => fun v=>(rec v).restricted
local notation "recipes" => DescentTerminalBundleRows.recipes layout active hp orders code host
include aliases in
def birth : Birth recipes where
  hidden := fun y=>(firstAlias (rec (layout.node host y)) (aliases _)).trans Fin.valEmbedding
  atom := fun y=>orders (layout.node host y)
local notation "localNames" => birth hp layout host rs sh code orders aliases
variable {hid groups blocks shops wb d0 dCount:ℕ}
    (hH : ∀y, Fintype.card
      (DescentTerminalBundleRows.recipes layout (fun v=>((sh v).recipe hp).restricted) hp orders code host y).Hidden ≤ hid)
    (hN : ∀y, Fintype.card
      (DescentTerminalBundleRows.recipes layout (fun v=>((sh v).recipe hp).restricted) hp orders code host y).Node ≤ N)
    (hA : ∀y u,
      (DescentTerminalBundleRows.recipes layout (fun v=>((sh v).recipe hp).restricted) hp orders code host y).arity u≤M) (short:∀y,(layout.site host).arity y≤q)
    (port:Attached W.graph (layout.node host z)↪ℕ) (ranked:layout.operandRank (layout.node host z)=rank A native S ready homes (layout.node host z) port)
    (scale psize:ℕ) (whole:A.z*G.b=scale*p)
    (common:∀j:Attached W.graph (layout.node host z),poolBatchCount (bits j.val) p=psize)
    (t:CellInputs A.degree A.cap N M)
    (config:Widths) (index:ℕ→ℕ→ℕ→ℕ) (frozenBits:ℕ) (pages:Gather.Pages blocks A.cap M)
    (before:Memory wb) (origin:ℕ) (channels:MaskAllocation.Channels blocks) (maskBase:ℕ)
local notation "machine" => MaskAllocation.shelf (q:=q) (t:=tags) (H:=hid) (N:=N) (A:=M) (p:=p) (groups:=groups) channels maskBase
local notation "L" => columns A.cap N M
local notation "H" => blocks*shops
local notation "sz" => Nat.clog 2 (q+hid+1)
local notation "sz₀" => Nat.clog 2 (q+1)
local notation "f7" => output A.cap N M A.degree groups d0 sz q scale psize config index
local notation "f0" => publicCell (cap:=A.cap) (N:=N) (A:=M) (d:=d0) A.degree q scale psize frozenBits groups config
local notation "ps" => Gather.dropOff origin blocks shops L pages.address
local notation "B" => Gather.banks («L»:=L) origin H
local notation "base" => Gather.rom origin L H
local notation "shelf" => DescentTerminalPointerFrame.size L d0
local notation "a0" => base+shelf
local notation "base7" => a0+H
local notation "a7" => base7+shelf
local notation "warm" => ProtocolRAM.result ps before
local notation "mid" => DescentTerminalPointerFrame.result base B H f0 warm
local notation "done" => DescentTerminalPointerFrame.result base7 B H f7 mid
local notation "p0" => DescentTerminalPointerFrame.program wb base B H f0
local notation "p7" => DescentTerminalPointerFrame.program wb base7 B H f7
local notation "work" => ((4+10*shelf)+(4+H*(16+26*L)))
local notation "meas" => measured (q:=q) (t:=tags) («H»:=hid) (N:=N) (A:=M) (w:=p) (groups:=groups)
variable (b:Fin blocks) (h:Fin shops) (g:Fin groups)
local notation "cell" => pages.source (N:=N) (d:=d0) before b h
local notation "rk" => rank A native S ready homes atNode port
local notation "sig" => Stage.signedPanel A native S ready homes (Stage.home A atNode)
local notation "afterPorts" => done
local notation "nodeAt" => fun u=>(ordinal (orders atNode) u).castLE (hN z)
local notation "measuredAt" => fun mem k=>venueField (cellAt (meas machine mem h) (finProdFinEquiv (g,b))) k
variable (legal:∀j x,(pages.address (N:=N) j x).Fits origin shops wb) (off:2^d0<2^wb)
    (space :
      ((((Gather.rom origin (columns A.cap N M) (blocks*shops))+(DescentTerminalPointerFrame.size (columns A.cap N M) d0))+(blocks*shops))+(DescentTerminalPointerFrame.size (columns A.cap N M) d0))+(blocks*shops)<2^wb)
    (fits₀:(Nat.clog 2 (q+1))*groups≤wb) (fits₇:(Nat.clog 2 (q+hid+1))*(N*M)*groups≤wb)
    (pbase:(channels.primitive b 0).base=((Gather.rom origin (columns A.cap N M) (blocks*shops))+(DescentTerminalPointerFrame.size (columns A.cap N M) d0))+b.val*shops)
    (abase:(channels.primitive b 7).base=((((Gather.rom origin (columns A.cap N M) (blocks*shops))+(DescentTerminalPointerFrame.size (columns A.cap N M) d0))+(blocks*shops))+(DescentTerminalPointerFrame.size (columns A.cap N M) d0))+b.val*shops)
    (pkeep:shops≤(channels.primitive b 0).size) (akeep:shops≤(channels.primitive b 7).size)
    (read:SourceRead config (pages.source (N:=N) (d:=d0) before b h) g.val t)
    (prior:Origin W.graph (layout.node host z) ((sh (layout.node host z)).recipe hp) (orders (layout.node host z)) (hN z) (hA z) (aliases (layout.node host z)) (rank A native S ready homes (layout.node host z) port) port
      (reindexed t (index ((pages.source (N:=N) (d:=d0) before b h) mcol).val ((pages.source (N:=N) (d:=d0) before b h) fcol).val)))
    (ports:DescentTerminalFrozenRoster.length frozenBits ((pages.source (N:=N) (d:=d0) before b h) fcol).val=Fintype.card (Attached W.graph (layout.node host z))) (chips:t.chips=(Stage.signedPanel A native S ready homes (Stage.home A (layout.node host z))))
    (source:Fin 3→Bank) (countBase out:ℕ)
local notation "fee" => DescentTerminalPointerFrame.size 3 dCount
local notation "finalMem" => DescentTerminalCountWidthPair.final dCount q hid N M groups blocks shops p countBase out source afterPorts
local notation "lastPass" => DescentTerminalCountWidthPair.program wb dCount q hid N M groups blocks shops p countBase out source
local notation "lastCost" => DescentTerminalCountWidthPair.clocks dCount blocks shops
local notation "fieldSize" => familySize (q:=q) (t:=tags) («H»:=hid) (N:=N) (A:=M) (w:=p)
local notation "sf" => DescentTerminalPrivateSourceChannels.family
variable (ok:DescentTerminalPointerFrame.Room source countBase dCount (blocks*shops) wb) (apart:countBase+(DescentTerminalPointerFrame.size 3 dCount)+(blocks*shops)≤out)
    (room:out+(blocks*shops)<2^wb) (fit:groups*span q tags hid N M p≤wb)
    (fromBase:∀f,(channels.primitive b (DescentTerminalPrivateSourceChannels.family f)).base=(source f).base+b.val*shops)
    (fromSize:∀f,shops≤(channels.primitive b (DescentTerminalPrivateSourceChannels.family f)).size)
    (covers:∀f,familySize (q:=q) (t:=tags) («H»:=hid) (N:=N) (A:=M) (w:=p)
      (DescentTerminalPrivateSourceChannels.family f)*groups≤dCount)
    (countAt:(channels.primitive b 2).base=countBase+(DescentTerminalPointerFrame.size 3 dCount)+b.val*shops) (countSize:shops≤(channels.primitive b 2).size)
    (widthAt:(channels.primitive b 4).base=out+b.val*shops) (widthSize:shops≤(channels.primitive b 4).size)
    (alias_:channels.primitive b 1=channels.occupied b)
    (old:∀f:Fin 8, f=1 ∨ f=3 ∨ f=5 ∨ f=6→(channels.primitive b f).base+(channels.primitive b f).size≤origin)
    (keep:∀f:Fin 8,f≠2→f≠4→(channels.primitive b f).base+(channels.primitive b f).size≤countBase)
    (ordered:origin≤countBase)

attribute [local irreducible] ProtocolRAM.program ProtocolRAM.result DescentTerminalPointerFrame.program
attribute [local irreducible] DescentTerminalPointerFrame.result DescentTerminalCountWidthPair.program DescentTerminalCountWidthPair.final
attribute [local irreducible] measured MaskAllocation.shelf cellAt venueField blankAt

include coords ranked short whole common legal off space fits₀ fits₇ pbase abase pkeep akeep read prior ports chips ok apart room fit
  fromBase fromSize covers countAt countSize widthAt widthSize alias_ old keep ordered in
theorem primitive_finish
    (occupied:(blankAt (meas machine before h) (finProdFinEquiv (g,b))).val=1)
    (population:measuredAt before nodeCount=Fintype.card (r).Node)
    (roles:∀u,measuredAt before (nodeRole (nodeAt u))=(code ((r).tag u)).val+1)
    (lengths:∀u,measuredAt before (nodeArity (nodeAt u))=(r).arity u) :
    ((((ProtocolRAM.program wb ps).seq p0).seq p7).seq lastPass).Exec before finalMem
      (((ProtocolRAM.clock ps+work)+work)+lastCost) ∧
    CheapCode ((((ProtocolRAM.program wb ps).seq p0).seq p7).seq lastPass) ∧
    PrimitiveReceipts (q:=q) (layout.site host) recipes localNames hH hN hA z (measuredAt finalMem) ∧
    (∀j,j<origin→finalMem j=before j) ∧ ProtocolRAM.clock ps≤4+(L*blocks)*(4+shops*18) := by
  have pp:((machine).channel (finProdFinEquiv (b,(0:Fin 8).succ))).base=a0+b.val*shops:=by simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using pbase
  have ap:((machine).channel (finProdFinEquiv (b,(7:Fin 8).succ))).base=a7+b.val*shops:=by simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using abase
  have pk:shops≤((machine).channel (finProdFinEquiv (b,(0:Fin 8).succ))).size:=by simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using pkeep
  have ak:shops≤((machine).channel (finProdFinEquiv (b,(7:Fin 8).succ))).size:=by simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using akeep
  obtain ⟨pairExec,pairCheap,portsRead,argsRead,pairFrame,pairClock⟩ := primitive_pair
    (q:=q) (hid:=hid) (N:=N) (M:=M) (groups:=groups) (blocks:=blocks) (shops:=shops) (wb:=wb) (d0:=d0)
    A native S ready homes atNode coords port hp scale psize whole common r code
    (orders atNode) (hN z) (hA z) (aliases atNode) t config index frozenBits pages before origin machine b h g legal off
    space fits₀ fits₇ pp ap pk ak (short z) (hH z) read prior ports chips
  have frame (j:ℕ) (hj:j<origin):afterPorts j=before j:=pairFrame j (.inl hj)
  have hold (k:Key hid N M) (which:group k=1 ∨ group k=3 ∨ group k=5 ∨ group k=6) :
      measuredAt afterPorts k=measuredAt before k := by
    apply DescentTerminalPrimitiveFrames.field_below machine before afterPorts b h g origin k _ frame
    simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using old (group k) which
  have occ:(blankAt (meas machine afterPorts h) (finProdFinEquiv (g,b))).val=1 := by
    rw [DescentTerminalPrimitiveFrames.occupation_below machine before afterPorts b h g origin _ frame]
    · exact occupied
    · simpa only [MaskAllocation.shelf,MaskAllocation.Channels.occupied_at,←alias_] using old 1 (.inl rfl)
  have actual (u:(r).Node) (j:Fin ((r).arity u)) :
      measuredAt afterPorts (nodeArg (nodeAt u) (j.castLE (hA z u)))=
        ((recipes z).operand u j).elim (fun a=>a.val+1) (fun a=>q+(ordinal ((localNames).hidden z) a).val+1) := by
    have a:=argsRead u j
    change _=(((numbered G' hp atNode (layout.operandRank atNode) (r).restricted code).operand u j).elim _ _)
    rw [ranked]
    exact a
  obtain ⟨finishExec,finishCheap,receipt,finishFrame⟩ := DescentTerminalCountWidthPair.primitive_receipts
    (q:=q) (t:=tags) (hid:=hid) (N:=N) (A:=M) (blocks:=blocks) (shops:=shops) (groups:=groups) (wb:=wb) (d:=dCount)
    G' hp layout rs sh code orders host localNames hH hN hA short z
    source countBase out maskBase channels afterPorts ok apart room fit b h g fromBase fromSize covers countAt countSize widthAt widthSize
    portsRead occ alias_ ((hold _ (.inr (.inl rfl))).trans population)
    (fun u=>(hold _ (.inr (.inr (.inl rfl)))).trans (roles u))
    (fun u=>(hold _ (.inr (.inr (.inr rfl)))).trans (lengths u)) actual keep
  let packed := ((ProtocolRAM.program wb ps).seq p0).seq p7
  exact ⟨@Procedure.Exec.then wb packed lastPass before afterPorts finalMem ((ProtocolRAM.clock ps+work)+work) lastCost (@pairExec) (@finishExec),
    @cheap_seq wb packed lastPass (@pairCheap) (@finishCheap),receipt,
    fun j hj=>(finishFrame j (.inl (hj.trans_le ordered))).trans (frame j hj),pairClock⟩

/- Compose the earlier, actual role/arity RAM issue with all four later numerical
fields. The packed primitive and slice words at its input are required only at
the live coordinates of the genuine local birth order. -/
section BirthFields
open DescentEpochTagKeys
variable {palette aMax chunks stride:ℕ} (dictionary:Codec U palette)
    (first second:DescentTerminalCombinedRole.Shelf) (roleOut:ℕ) (initial:Memory wb)
local notation "roleData" => DescentTerminalCombinedRole.observed (n:=palette) (A:=aMax) (G:=chunks) (p:=p) (R:=stride) (N:=N) (M:=groups)
local notation "roleProc" => DescentTerminalCombinedRole.paired (wb:=wb) first second roleOut H
local notation "birthEnd" => DescentTerminalCombinedRole.memory first second roleOut H initial
local notation "ticks" => DescentTerminalCombinedRole.steps H
local notation "tagCount" => DescentBundleTagKeys.capacity palette aMax chunks p stride
variable (tags_eq:(DescentBundleTagKeys.capacity palette aMax chunks p stride)=tags)
    (table_eq:∀u,(code (((sh (layout.node host z)).recipe hp).tag u)).val=((DescentBundleTagKeys.codec dictionary aMax chunks p stride).store (((sh (layout.node host z)).recipe hp).tag u)).val)
    (roleSetup:(DescentTerminalCombinedRole.emit first).Fits wb roleOut)
    (countSetup:(DescentTerminalCombinedRole.emit second).Fits wb roleOut)
    (roleEnd:roleOut+(blocks*shops)+(blocks*shops)<2^wb)
    (readyRole:DescentTerminalCombinedRole.Static (A:=aMax) (G:=chunks) (p:=p) (R:=stride) (N:=N) (M:=groups) dictionary first initial)
    (readyCount:DescentTerminalCombinedRole.CountStatic (n:=palette) (A:=aMax) (G:=chunks) (p:=p) (R:=stride) (N:=N) (M:=groups) M second initial)
    (same:second.input=first.input)
    (roleWidth:DescentTerminalCombinedRole.output palette aMax chunks p stride*N*groups≤wb) (countWidth:Nat.clog 2 (M+1)*N*groups≤wb)
    (roleBase:((MaskAllocation.shelf (q:=q) (t:=tags) («H»:=hid) (N:=N) (A:=M) (p:=p) (groups:=groups) channels maskBase).channel (finProdFinEquiv (b,(5:Fin 8).succ))).base=roleOut+b.val*shops)
    (countRow:((MaskAllocation.shelf (q:=q) (t:=tags) («H»:=hid) (N:=N) (A:=M) (p:=p) (groups:=groups) channels maskBase).channel (finProdFinEquiv (b,(6:Fin 8).succ))).base=roleOut+(blocks*shops)+b.val*shops)
    (roleKeep:shops≤((MaskAllocation.shelf (q:=q) (t:=tags) («H»:=hid) (N:=N) (A:=M) (p:=p) (groups:=groups) channels maskBase).channel (finProdFinEquiv (b,(5:Fin 8).succ))).size)
    (countKeep:shops≤((MaskAllocation.shelf (q:=q) (t:=tags) («H»:=hid) (N:=N) (A:=M) (p:=p) (groups:=groups) channels maskBase).channel (finProdFinEquiv (b,(6:Fin 8).succ))).size)
    (fitBirth:∀u,dictionary.fits ((rs (layout.node host z)).tag u))
    (liveWords:∀u,DescentTerminalCombinedRole.Printed dictionary (DescentTerminalCombinedRole.fields
      (DescentTerminalCombinedRole.node ((DescentTerminalCombinedRole.observed (n:=palette) (A:=aMax) (G:=chunks) (p:=p) (R:=stride) (N:=N) (M:=groups)) first initial ((finProdFinEquiv (b,h)).val:Computability.VPVNP.BurstRAM.Word wb)) g ((fun u=>(ordinal (orders (layout.node host z)) u).castLE (hN z)) u)))
        ((rs (layout.node host z)).tag u) ((sh (layout.node host z)).sliceFields u))
    (oldOcc:(channels.occupied b).base+(channels.occupied b).size≤roleOut)
    (oldPop:(channels.primitive b 3).base+(channels.primitive b 3).size≤roleOut)
    (roleTime:roleOut≤origin)

include legal off space ok apart room ordered roleSetup countSetup roleEnd readyRole readyCount same roleTime in
omit [Fintype P] in
/-- Executability and retention do not require a live site in a bin, a home or
even in the whole graph. Tableau observations are needed only for semantic reads. -/
theorem physical_run (link:before=birthEnd) :
    ((roleProc).seq ((((ProtocolRAM.program wb ps).seq p0).seq p7).seq lastPass)).Exec initial finalMem
      ((ticks+ticks)+(((ProtocolRAM.clock ps+work)+work)+lastCost)) ∧
    CheapCode ((roleProc).seq ((((ProtocolRAM.program wb ps).seq p0).seq p7).seq lastPass)) ∧
    (∀j,j<roleOut→finalMem j=initial j) ∧ ProtocolRAM.clock ps≤4+(L*blocks)*(4+shops*18) := by
  have later : (DescentTerminalCombinedRole.emit second).Fits wb (roleOut+H) :=
    ProtocolRAMGeneratedWrite.fits_mono (w:=wb) (a:=roleOut) (b:=roleOut+H)
      (DescentTerminalCombinedRole.emit second) (Nat.le_add_right roleOut H) countSetup
  obtain ⟨roleExec,roleCheap,_⟩ := DescentTerminalCombinedRole.both
    (n:=palette) (A:=aMax) (G:=chunks) (p:=p) (R:=stride) (N:=N) (M:=groups) (slots:=M)
    dictionary first second roleOut H initial roleSetup countSetup later roleEnd readyRole readyCount same
  have roleToBefore : (roleProc).Exec initial before (ticks+ticks) := by
    rw [link]
    exact @roleExec
  obtain ⟨gatherExec,gatherCheap,_,gatherFrame,gatherClock⟩ :=
    Gather.Pages.pair pages before origin shops f0 f7 legal off space
  obtain ⟨countExec,countCheap,countFrame⟩ := DescentTerminalCountWidthPair.run
    (q:=q) (hid:=hid) (N:=N) (A:=M) (p:=p) (groups:=groups) source countBase out afterPorts ok apart room
  let gatherCode := ((ProtocolRAM.program wb ps).seq p0).seq p7
  have tailExec : (gatherCode.seq lastPass).Exec before finalMem (((ProtocolRAM.clock ps+work)+work)+lastCost) :=
    @Procedure.Exec.then wb gatherCode lastPass before afterPorts finalMem
      ((ProtocolRAM.clock ps+work)+work) lastCost (@gatherExec) (@countExec)
  refine ⟨@Procedure.Exec.then wb roleProc (gatherCode.seq lastPass) initial before finalMem
    (ticks+ticks) (((ProtocolRAM.clock ps+work)+work)+lastCost) (@roleToBefore) (@tailExec),
    @cheap_seq wb roleProc (gatherCode.seq lastPass) (@roleCheap)
      (@cheap_seq wb gatherCode lastPass (@gatherCheap) (@countCheap)), ?_, gatherClock⟩
  intro j hj
  calc
    finalMem j = afterPorts j := countFrame j (.inl (hj.trans_le (roleTime.trans ordered)))
    _ = before j := gatherFrame j (.inl (hj.trans_le roleTime))
    _ = birthEnd j := congrFun link j
    _ = initial j := DescentTerminalPrimitiveFrames.paired_below first second roleOut H initial j hj

include coords ranked short whole common legal off space fits₀ fits₇ pbase abase pkeep akeep read prior ports chips ok apart room fit
  fromBase fromSize covers countAt countSize widthAt widthSize alias_ old keep ordered tags_eq table_eq
  roleSetup countSetup roleEnd readyRole readyCount same roleWidth countWidth roleBase countRow roleKeep countKeep
  fitBirth liveWords oldOcc oldPop roleTime in
theorem primitive_from_birth (link:before=birthEnd)
    (homeOf:(G').Site→Fin shops) (groupOf:(G').Site→Fin groups) (blockOf:(G').Site→Fin blocks)
    (here:homeOf atNode=h ∧ groupOf atNode=g ∧ blockOf atNode=b)
    (occSize:shops≤(channels.occupied b).size) (wide:groups≤wb)
    (actorWord:initial ((channels.occupied b).base+h.val)=
      ((encode 1 groups (fun z=>(if ∃v,homeOf v=h ∧ groupOf v=z ∧ blockOf v=b then 1 else 0):Fin groups→Cell 1)).val:Computability.VPVNP.BurstRAM.Word wb))
    (populationWord:digit (Nat.clog 2 (N+1)) g.val (initial ((channels.primitive b 3).base+h.val)).val=Fintype.card (r).Node) :
    ((roleProc).seq ((((ProtocolRAM.program wb ps).seq p0).seq p7).seq lastPass)).Exec initial finalMem
      ((ticks+ticks)+(((ProtocolRAM.clock ps+work)+work)+lastCost)) ∧
    CheapCode ((roleProc).seq ((((ProtocolRAM.program wb ps).seq p0).seq p7).seq lastPass)) ∧
    PrimitiveReceipts (q:=q) (layout.site host) recipes localNames hH hN hA z (measuredAt finalMem) ∧
    (∀j,j<roleOut→finalMem j=initial j) := by
  have hosts:shops≤H :=by simpa using Nat.mul_le_mul_right shops (Nat.succ_le_of_lt (Nat.zero_lt_of_lt b.isLt))
  have hostFits:shops≤2^wb:=by omega
  have occupied:(blankAt (meas machine initial h) (finProdFinEquiv (g,b))).val=1 := by
    rw [DescentTerminalRolePrefix.presence channels maskBase initial homeOf groupOf blockOf b h g hostFits occSize actorWord wide,
      ite_eq_left ⟨atNode,here⟩]
  have population:measuredAt initial nodeCount=Fintype.card (r).Node := by
    apply DescentTerminalRolePrefix.population channels maskBase initial b h g hostFits _ populationWord
    exact fromSize (0:Fin 3)
  have later : (DescentTerminalCombinedRole.emit second).Fits wb (roleOut+H) :=
    ProtocolRAMGeneratedWrite.fits_mono (w:=wb) (a:=roleOut) (b:=roleOut+H) (DescentTerminalCombinedRole.emit second) (Nat.le_add_right roleOut H) countSetup
  obtain ⟨roleExec,roleCheap,_⟩ := DescentTerminalCombinedRole.both
    (n:=palette) (A:=aMax) (G:=chunks) (p:=p) (R:=stride) (N:=N) (M:=groups) (slots:=M)
    dictionary first second roleOut H initial roleSetup countSetup later roleEnd readyRole readyCount same
  have launched : (roleProc).Exec initial before (ticks+ticks) := by rw [link]; exact @roleExec
  have frame (j:ℕ) (hj:j<roleOut):before j=initial j := by
    rw [link];exact DescentTerminalPrimitiveFrames.paired_below first second roleOut H initial j hj
  have nodeFields (u:(r).Node) := DescentTerminalRolePairFields.paired_fields (q:=q) (hid:=hid) dictionary hp (sh atNode) u
    first second roleOut machine initial roleSetup countSetup roleEnd readyRole readyCount same roleWidth countWidth h b g
    (nodeAt u) roleBase roleKeep countRow countKeep (fitBirth u) (hA z u) (liveWords u)
  have transport (key : Key hid N M) :
      venueField (cellAt (measured (q:=q) (t:=tagCount) («H»:=hid) (N:=N) (A:=M) (w:=p)
        (groups:=groups) machine birthEnd h) (finProdFinEquiv (g,b))) key = measuredAt birthEnd key :=
    congrArg (fun n => venueField (cellAt (measured (q:=q) (t:=n) («H»:=hid) (N:=N) (A:=M)
      (w:=p) (groups:=groups) machine birthEnd h) (finProdFinEquiv (g,b))) key) tags_eq
  have occ:(blankAt (meas machine before h) (finProdFinEquiv (g,b))).val=1 := by
    rw [DescentTerminalPrimitiveFrames.occupation_below machine initial before b h g roleOut _ frame]
    · exact occupied
    · simpa only [MaskAllocation.shelf,MaskAllocation.Channels.occupied_at] using oldOcc
  have pop:measuredAt before nodeCount=Fintype.card (r).Node := by
    rw [DescentTerminalPrimitiveFrames.field_below machine initial before b h g roleOut nodeCount _ frame]
    · exact population
    · simpa only [DescentTerminalVertexFields.group,nodeCount,MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using oldPop
  obtain ⟨restExec,restCheap,receipt,restFrame,_⟩ := primitive_finish
    (q:=q) (hid:=hid) (N:=N) (M:=M) (blocks:=blocks) (shops:=shops) (groups:=groups) (wb:=wb) (d0:=d0) (dCount:=dCount)
    A native S ready homes coords hp layout host z rs sh code orders aliases hH hN hA short port ranked
    scale psize whole common t config index frozenBits pages before origin channels maskBase b h g legal off space fits₀ fits₇
    pbase abase pkeep akeep read prior ports chips source countBase out ok apart room fit fromBase fromSize covers countAt countSize
    widthAt widthSize alias_ old keep ordered occ pop (fun u=>by rw [link,table_eq]; exact (transport _).symm.trans (nodeFields u).2.2.1)
    (fun u=>by rw [link]; exact (transport _).symm.trans (nodeFields u).2.2.2.1)
  let scans := (((ProtocolRAM.program wb ps).seq p0).seq p7).seq lastPass
  exact ⟨@Procedure.Exec.then wb roleProc scans initial before finalMem (ticks+ticks) (((ProtocolRAM.clock ps+work)+work)+lastCost) (@launched) (@restExec),
    @cheap_seq wb roleProc scans (@roleCheap) (@restCheap),receipt,
    fun j hj=>(restFrame j (hj.trans_le roleTime)).trans (frame j hj)⟩
end BirthFields

end
end Hierarchy.DescentTerminalNormalizedFields

end OAI
