import OAI.Hierarchy.DescentPreparedMatrixFrame
import OAI.Hierarchy.DescentReachedPrimitiveRoot
import OAI.Hierarchy.DescentRecordedRotationWord
import OAI.Hierarchy.DescentPreparedPrimitiveObservation
import OAI.Hierarchy.DescentResetPeerGoodInputs
import OAI.Hierarchy.DescentRecordedRotorBatchRoom
import OAI.Hierarchy.DescentRecordedGoodBaseFlag

namespace OAI
/-! # Reading a physical root operation from its admitted prior role packet -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentResetLocalNodes DescentNamedContact
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit) (a : Archive W) (earlier : Local a.bit)
local notation "split" => BitDescription.granular W b.count (z*G.b) b.fit a.bit
local notation "key" => DescentOrderedReset.grains W b.count b.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "m" => b.reset.unit/p
local notation "pre" => (split).batchedReset b.reset b.terminals key m p hp fit (resetMenu b)
local notation "prog" => b.reset.laneRecipe key m p hp fit
local notation "next" => (resetArchive b p hp whole a).bit
local notation "names" => resetOrigin b hp whole a
local notation "oldId" => cap.placement.site cap.vertex cap.valid.coordinates
local notation "who" => (fun t=>(b.reset.homeTicket b.terminals oldId t).trans Fin.valEmbedding)
local notation "prior" => (fun v=>(earlier v).toEmbedding.trans Fin.valEmbedding)
local notation "fresh" => b.reset.laneNodeOrder key m p hp fit
local notation "order" => DescentLocalArchiveOrder.reset b p hp whole a earlier


open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentResetActorClass DescentCommonHost
open Reached.NodeCells DescentColonies
open scoped Classical Fin.CommRing
variable [Fintype P] (stored : b.Recorded p) (token : a.bit.Tokenized cap.placement.records)
local notation "Y" => b.next
local notation "H" => S.hostSize (i+1)
local notation "Groups" => S.groupCount (i+1)
local notation "prevRank" => (Y).vertex.trans (Fin.castLEEmb (Y).valid.host)
local notation:max "census" precision:arg => Census.count (Y).placement (Equiv.refl _) prevRank precision
local notation "cell" => whereAt Y next order
local notation "res" => b.reset.k-b.terminals.commonDepth
local notation:max "cls" rack:arg => (ClosedReset.Window.paidActorAt b rack).elim 0 (fun u=>indexed b.reset.graph res u.val)
local notation:max "leftSite" u:arg => b.reblock.destination ((b.reset.resetNames b.terminals).symm u)
local notation "original" => W.granular b.count (z*G.b) b.fit

open DescentPackedResetRotorRoles DescentResetMetadataInputs DescentBundleHistory
variable (layout : DescentPrimitiveBirth.Layout)
local notation:max "rootSite" wing:arg g:arg v:arg => (⟨(wing,.inl g),⟨v,.inl false⟩⟩:b.reset.bank.Site)

open DescentPrimitiveBirth DescentCommonHost DescentRotorRootPresence DescentSIMDLookup
open DescentPacking.PackedMatch.Local
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "rr" => (Z).placement
local notation "dim" => (T).commonDepth
local notation "oldDigits" => S.resetOutputDigits ctl.base ctl.radix b.age b.commonDepth
local notation:max "rootLow" g:arg => ((Z).goodLabel T g).val.2
local notation:max "rootNode" side:arg g:arg v:arg op:arg => (⟨rootSite side g v,op⟩:NodeOrder.Global prog)

open DescentDenseHostOrder DescentResetActorClass
local notation "former" => cap.vertex.trans (Fin.castLEEmb cap.valid.host)
local notation "ownerId" => b.frame.host.symm.toEmbedding.trans former
local notation "rawRoot" => ClosedReset.Window.originalCompactName b (S.hostSize i) cap.valid.host
local notation "address" => (Z).denseHostRank T ownerId
local notation:max "hostOf" v:arg => ((Y).placement.pos v).2
local notation:max "venue" side:arg g:arg v:arg => (Z).placed T (((Z).resetNames T).symm (.inr (rootSite side g v)))
local notation:max "high" g:arg => (Z).rootBlock T (.inl g)

open DescentRotorWindowArchive DescentIssuedRotorRoles DescentSIMDLookup DescentRotorRootPresence
open DescentSharedBookScan DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentPacking.PackedMatch.Local.Stage DescentResetGates DescentHostDirectory DescentResetHostSize
open DescentPackedColony DescentPackedFallbackTree.Image ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescentStageEdgeReceipt DescentColonies

private theorem prior_data {D r cap field : ℕ}
    (v : Fin (count D (2^r) cap)→Cell field) (c l p : Cell field)
    (i : Fin (count D (2^r) cap)) :
    chartPart (D:=D) (L:=2^r) (cap:=cap) (priorFields (D:=D) (r:=r) (cap:=cap) v c l p)
      i.castSucc=v i:=by
  rw [show i.castSucc=Fin.castAdd 1 i from rfl]
  simp [chartPart,priorFields]

private theorem prior_capacity {D r cap field : ℕ}
    (v : Fin (count D (2^r) cap)→Cell field) (c l p : Cell field) :
    chartPart (D:=D) (L:=2^r) (cap:=cap) (priorFields (D:=D) (r:=r) (cap:=cap) v c l p)
      (Fin.last (count D (2^r) cap))=c:=by
  rw [show Fin.last (count D (2^r) cap)=Fin.natAdd (count D (2^r) cap) (0:Fin 1) by
    apply Fin.ext;simp]
  simp [chartPart,priorFields]

variable {field nodes args bits₀ stop lanes oldLanes classes priceBits spanBits : ℕ}
local notation "height₀" => GroupStage.depthBound D n f g
local notation "seats" => (roster (Z).graph res height₀).card
local notation "board" => (⟨⟨S.hostSize i,H,seats,Groups,2^k,lanes⟩,
  res,(Z).n,nodes,args,bits₀,stop,oldLanes,classes,priceBits,spanBits⟩:DescentPrimitiveBirth.Layout)
local notation "deg₀" => cap.placement.degree
local notation "cap₀" => cap.placement.cap
local notation "oldAxis" => congrArg (fun t : ℕ=>2^(t-dim)) b.keyWidth
local notation:max "rank₀" snap:arg => ranks (a:=res) («Y»:=2^(Z).n) (D:=deg₀) (snap).chart (2^height₀) (height₀+2) (snap).memory
local notation "peer₀" => PackedFlow.Padded.roster (D:=deg₀) cap.placement (ClosedReset.Recorded.oldName cap) cap.valid.host
local notation "paid₀" => ClosedReset.Recorded.paddedValue (b:=field) dim res peer₀
  (ClosedReset.Recorded.oldDepth b) (ClosedReset.Recorded.oldWidth b)
local notation "small₀" => b.frame.enough.trans (Nat.sub_le ..)
local notation:max "oldData" snap:arg => RootSources.paddedRow (snap).stencil peer₀ (snap).marks
  (fun u j=>((rank₀ snap) u j).val) (fun _=>Receiver.matrixBefore b.frame.basis small₀) paid₀

variable (snap : DescentPaidResidentCount.Reset.PaddedSnapshot b cap.valid.host field)
variable (equalAxis : Groups*2^k=2^dim)
local notation "data₀" => fun (hostIndex : Fin (S.hostSize i)) (groupIndex : Fin (Groups*2^k))
  (j : Fin (count deg₀ (2^res) cap₀))=>(oldData snap) hostIndex (groupIndex.cast equalAxis)
    (j.cast (congrArg (fun l=>count deg₀ l cap₀) oldAxis))
local notation "priorLevel" => fun (hostIndex : Fin (S.hostSize i)) (_ : Fin (Groups*2^k))=>
  (Receiver.depthDigit dim (Fintype.card cap.V) (ClosedReset.Recorded.oldDepth b) hostIndex:Cell field)
local notation "priorFlag" => fun (lo : Block res) (hostIndex : Fin (S.hostSize i)) (groupIndex : Fin (Groups*2^k))=>
  ((snap).stencil hostIndex (groupIndex.cast equalAxis) (lo.cast oldAxis):Cell field)
local notation "sensors" => (board).measuredFields (D:=deg₀) (cap:=cap₀) data₀ (fun _ _=>(cap₀:Cell field)) priorLevel priorFlag
local notation "levels" => fun hostIndex groupIndex=>activeDepth res (priorLevel hostIndex groupIndex).val
local notation "mapping" => (fun t : CanonicalTag (2^(Z).n)=>(role t:Cell bits₀))
local notation "oldRoles" => (board).observedWord (Z).width f m (DescentRecordedRotorLayers.width f cap₀) mapping sensors
local notation:max "sampled" goodRoot:arg => (snap).stencil (former (b.frame.host.symm ((goodRoot : (rr).Good).val.1))) (high goodRoot) ((sample ((Z).goodLabel T goodRoot)).cast oldAxis)

set_option hygiene true

omit [Fintype P] in
include stored in
set_option maxHeartbeats 1200000 in
/-- The original numerical inputs are the actual predecessor's ordered matrix,
measured flag, cap and attained depth. The current node only chooses their address. -/
theorem registered_root_rotation (elapsed : 0< i) (sorted : SourceSorted W cap.order)
    (baseRoom : max (max res (2^(Z).n)) (2^res)<2^field) (nRoom : (Z).n<field)
    (depthRoom : res+1<2^field) (capRoom : cap₀<2^field)
    (side : Bool) (g₀ : (rr).Good) (gate : Fin (2^(Z).n))
    (flagRoom : sampled g₀<2^field) (clean : sampled g₀%2=0)
    (op : (prog (rootSite side g₀ gate)).Node) (atom : NodeOrder.All next)
    (slot : Fin nodes) (x : Block k) (h₀ : Fin H) (group : Fin Groups)
    (found : cell x slot h₀ group=some atom)
    (origin : names atom=.inr (.inr (rootNode side g₀ gate op)))
    (row : Fin (board).roots)
    (keyRow : (originClass b hp whole a (.inr (.inr (rootNode side g₀ gate op)))).val=6+row.val)
    (layer : Fin ((Z).circuit side g₀).layers) (number : slot.val/m=layer.val)
    (inside : slot.val<stop) :
    (board).rootActual levels oldRoles rawRoot slot x row h₀ group=
      (rotorNumber (((Z).circuit side g₀).rotation layer) gate:Cell bits₀):=by
  have addr:=physical_root_coordinates b hp whole a earlier side g₀ gate op atom slot x h₀ group found origin
  obtain ⟨member,hostAt,laneAt⟩:=addr
  let tag:=(Z).goodLabel T g₀
  let lev : Fin (res+1):=⟨tag.val.1,Nat.lt_succ_of_le (Nat.sub_le_sub_right ((rr).depth _) dim)⟩
  have lowBound : tag.val.2<2^lev.val:=Nat.mod_lt _ (Nat.two_pow_pos _)
  have parts:=physical_root_parts b hp whole a side g₀ gate op row keyRow
  let host:=former (b.frame.host.symm g₀.val.1)
  let slot₀:=finProdFinEquiv (group,x)
  have highAt : slot₀.cast equalAxis=high g₀:=Fin.ext laneAt
  have levelAt : (priorLevel host slot₀).val=lev.val+1:=by
    have depthAt:=ClosedReset.Recorded.oldDepth_at b (b.frame.host.symm g₀.val.1)
    simp only [Equiv.apply_symm_apply] at depthAt
    have hostLive : host.val < Fintype.card cap.V:=(cap.vertex (b.frame.host.symm g₀.val.1)).isLt
    change ClosedReset.Recorded.oldDepth b host=_ at depthAt
    change (Receiver.depthDigit dim _ _ host:Cell field).val=_
    rw [Receiver.depthDigit,ite_eq_left hostLive,depthAt,Fin.val_cast_of_lt]
    · rfl
    · exact (Nat.succ_le_succ (Nat.sub_le_sub_right ((rr).depth _) dim)).trans_lt depthRoom
  have locate : (board).placement.previous (rawRoot ⟨h₀.val,member⟩)=host:=hostAt
  have live : levels ((board).placement.previous (rawRoot ⟨h₀.val,member⟩)) slot₀=some lev:=by
    rw [locate]
    exact (activeDepth_at res _ lev).mpr levelAt
  rw [(board).root_actual slot levels oldRoles rawRoot x h₀ group member row lev live,locate]
  apply Fin.ext
  rw [(board).digit_value slot _ inside]
  have lo : (rootParts res (Z).n row).2.1.val<2^lev.val:=by rw [parts];exact lowBound
  have measured : sensors row lev host slot₀=
      priorFields (D:=deg₀) (r:=res) (cap:=cap₀) (data₀ host slot₀) (cap₀:Cell field)
        (priorLevel host slot₀) (priorFlag (sample tag) host slot₀):=by
    simp only [DescentPrimitiveBirth.Layout.measuredFields,parts]
    split
    · rfl
    · rename_i outside
      exact (outside lowBound).elim
  have seenLevel : (flagPart (D:=deg₀) (L:=2^res) (cap:=cap₀) (sensors row lev host slot₀) 0).val=lev.val+1:=by
    rw [measured,prior_level];exact levelAt
  have seenFlag : (flagPart (D:=deg₀) (L:=2^res) (cap:=cap₀) (sensors row lev host slot₀) 1).val%2=0:=by
    rw [measured,prior_sample]
    change (((snap).stencil host (slot₀.cast equalAxis) ((sample tag).cast oldAxis):Cell field).val)%2=0
    rw [highAt,Fin.val_cast_of_lt flagRoom];exact clean
  rw [(board).observed_active (Z).width f m (DescentRecordedRotorLayers.width f cap₀) mapping sensors
    row lev host slot₀ lo seenLevel seenFlag,parts]
  obtain ⟨_,unitBatch,_,_⟩:=(Z).good_root_role key m p hp fit side g₀ gate op
  have positive : 0< m:=Nat.zero_lt_of_lt unitBatch.isLt
  let batch : Fin m:=⟨slot.val%m,Nat.mod_lt _ positive⟩
  have index : slot.val=layer.val*m+batch.val:=by
    rw [←number];exact (Nat.div_add_mod' slot.val m).symm
  let measuredChart:=chartPart (D:=deg₀) (L:=2^res) (cap:=cap₀) (sensors row lev host slot₀)
  have readMatrix (j : DescentRotorWindowArchive.Input deg₀ (2^(S.groupWidth k tail i+k-dim)) cap₀) :
      measuredChart (Fin.castSucc ((ix j).cast (congrArg (fun t=>count deg₀ t cap₀) (oldAxis).symm)))=
        (oldData snap) host (high g₀) (ix j):=by
    dsimp only [measuredChart]
    rw [measured]
    rw [prior_data]
    simp [highAt]
  have readCap : (measuredChart (Fin.last _)).val=cap₀:=by
    dsimp only [measuredChart]
    rw [measured]
    rw [prior_capacity,Fin.val_cast_of_lt capRoom]
  have digitAt:=ClosedReset.Window.recorded_rotation_cast b snap stored oldAxis elapsed sorted baseRoom nRoom
    side g₀ gate m stop mapping measuredChart readMatrix readCap layer batch (index ▸ inside)
  rw [index]
  exact digitAt

set_option hygiene false
set_option maxHeartbeats 1500000

/-- A single acquired prior board supplies both the guarded operation page
and its meaning at each occupied root of the reached graph. -/
structure RootRegister (Q : DescentPrimitiveBirth.Layout) (selectors : Q.Guards) {w : ℕ} (memory : Memory w)
    (buttons : Q.placement.blocks=2^k) (hosts : Q.placement.newHosts=H) (groups : Q.placement.groups=Groups) where
  population : Q.Population
  words : Q.Original
  name : Fin (Fintype.card (Y).V)→Fin Q.placement.sparse
  name_val : ∀v,(name v).val=(rawRoot v).val
  seen : Q.Observed selectors memory population words
  operation : ∀(slot : Fin Q.nodes) (x : Fin Q.placement.blocks) (h : Fin Q.placement.newHosts)
    (group : Fin Q.placement.groups) (atom : NodeOrder.All next) (side : Bool) (g₀ : (rr).Good)
    (gate : Fin (2^(Z).n)) (op : (prog (rootSite side g₀ gate)).Node)
    (row : Fin Q.roots) (layer : Fin ((Z).circuit side g₀).layers),
    cell (x.cast buttons) slot (h.cast hosts) (group.cast groups)=some atom →
    names atom=.inr (.inr (rootNode side g₀ gate op)) →
    (originClass b hp whole a (.inr (.inr (rootNode side g₀ gate op)))).val=6+row.val →
    slot.val/m=layer.val →
    Q.rootActual population words name slot x row h group=
      (rotorNumber (((Z).circuit side g₀).rotation layer) gate:Cell Q.rootBits)

namespace RootRegister
variable {Q₀ Q₁ : DescentPrimitiveBirth.Layout} {w₀ : ℕ} {memory : Memory w₀}
variable {oldGuard : Q₀.Guards} {newGuard : Q₁.Guards}

/-- The dated allocation is the same finite rectangle. All the words,
source coordinates and registered host order are carried along that equality. -/
def onBoard (same : Q₀=Q₁) (guardEq : HEq oldGuard newGuard)
    {b₀ : Q₀.placement.blocks=2^k} {h₀ : Q₀.placement.newHosts=H} {g₀ : Q₀.placement.groups=Groups}
    {b₁ : Q₁.placement.blocks=2^k} {h₁ : Q₁.placement.newHosts=H} {g₁ : Q₁.placement.groups=Groups}
    (r : RootRegister b hp whole a earlier Q₀ oldGuard memory b₀ h₀ g₀) :
    RootRegister b hp whole a earlier Q₁ newGuard memory b₁ h₁ g₁:=by
  subst Q₁
  have e := eq_of_heq guardEq
  cases e
  exact r

omit [Fintype P] in
theorem onBoard_name (same : Q₀=Q₁) (guardEq : HEq oldGuard newGuard)
    {b₀ : Q₀.placement.blocks=2^k} {h₀ : Q₀.placement.newHosts=H} {g₀ : Q₀.placement.groups=Groups}
    {b₁ : Q₁.placement.blocks=2^k} {h₁ : Q₁.placement.newHosts=H} {g₁ : Q₁.placement.groups=Groups}
    (r : RootRegister b hp whole a earlier Q₀ oldGuard memory b₀ h₀ g₀) (v : Fin (Fintype.card (Y).V)) :
    ((onBoard b hp whole a earlier (b₁:=b₁) (h₁:=h₁) (g₁:=g₁) same guardEq r).name v).val=(r.name v).val:=by
  subst Q₁
  have e := eq_of_heq guardEq
  cases e
  rfl

end RootRegister

open DescentPaidResidentCount.Reset
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
variable {bw N₀ K₀ R₀ M₀ hm lb tiny nbits t : ℕ}
    (rc : Receiver deg₀ cap₀ N₀ (Z).n res dim (S.hostSize i) (S.groupCount i) K₀ R₀ M₀ hm lb tiny field height₀ bw)
    (book : RootBook (Z).n res deg₀ (2^res) cap₀ field) (space : rc.PreparedFits book) (mem : Memory bw)
    (hdr : OriginalHeader b cap.valid.host rc book mem) (src : RootSources deg₀ (2^res) cap₀)
    (raw : OriginalArrays b cap.valid.host field)
    (packet : ClosedReset.Window.RootPacket b rc book space mem hdr src raw nbits t)
local notation "view₀" => root_snapshot b cap.valid.host rc book space mem hdr raw
local notation "fieldData" => fun (h : Fin (S.hostSize i)) (g : Fin (Groups*2^k))=>
  ClosedReset.Window.calendar_sender_matrix b M₀ field rc book space mem hdr raw h (g.cast equalAxis)
local notation "fieldFlag" => fun (lo : Block res) (h : Fin (S.hostSize i)) (g : Fin (Groups*2^k))=>
  (raw.stencil h (g.cast equalAxis) (lo.cast oldAxis):Cell field)
local notation "fieldInputs" => (board).measuredFields (D:=deg₀) (cap:=cap₀) fieldData
  (fun _ _=>(cap₀:Cell field)) priorLevel fieldFlag
local notation "paidRoles" => (board).observedWord (Z).width f m (DescentRecordedRotorLayers.width f cap₀) mapping fieldInputs
local notation "total₀" => cap.placement.wire*(cap.placement.z*G.b)*cap₀

include stored packet in
omit [Fintype P] in
/-- This is the actual issued packet: its matrix is the register in
`RootPacket.matrix` and its sampled stencil comes from that same rectangle. -/
theorem root_packet_rotation (elapsed : 0< i) (sorted : SourceSorted W cap.order)
    (baseRoom : max (max res (2^(Z).n)) (2^res)<2^field) (nRoom : (Z).n<field)
    (depthRoom : res+1<2^field) (capRoom : cap₀<2^field)
    (narrow : t≤field) (level : res<2^nbits) (one : 1<2^nbits) (amount : 2^res*total₀<2^nbits)
    (shape : 2*DescentFallbackShapeTable.rows res (2^(Z).n)≤2^t)
    (active : 0<total₀) (quotaPos : 0<quota S.rounds) (degreePos : 0<32*Nat.clog 2 (2*deg₀))
    (side : Bool) (g₀ : (rr).Good) (gate : Fin (2^(Z).n))
    (op : (prog (rootSite side g₀ gate)).Node) (atom : NodeOrder.All next)
    (slot : Fin nodes) (x : Block k) (h₀ : Fin H) (group : Fin Groups)
    (found : cell x slot h₀ group=some atom)
    (origin : names atom=.inr (.inr (rootNode side g₀ gate op)))
    (row : Fin (board).roots)
    (keyRow : (originClass b hp whole a (.inr (.inr (rootNode side g₀ gate op)))).val=6+row.val)
    (layer : Fin ((Z).circuit side g₀).layers) (number : slot.val/m=layer.val)
    (date : ℕ) (grain : z=S.grainAt G.b p date)
    (stopAt : ClosedReset.calendarBatchCount S n ctl.bitsR f cap₀ G.b date≤ stop) :
    (board).rootActual levels paidRoles rawRoot slot x row h₀ group=
      (rotorNumber (((Z).circuit side g₀).rotation layer) gate:Cell bits₀):=by
  obtain ⟨_,unitBatch,_,_⟩:=(Z).good_root_role key m p hp fit side g₀ gate op
  have positive : 0< m:=Nat.zero_lt_of_lt unitBatch.isLt
  have bound : slot.val/m<((Z).circuit side g₀).layers:=number.symm ▸ layer.isLt
  have inside:=((Nat.div_lt_iff_lt_mul positive).mp bound).trans_le
    ((ClosedReset.attained_batch_count b stored date grain side g₀).symm ▸ stopAt)
  have mode:=ClosedReset.Window.RootPacket.good_base_flag b rc book space mem hdr src packet stored
    level one amount shape active quotaPos degreePos g₀
  have flagBound:=(packet.short (former (b.frame.host.symm g₀.val.1)) (high g₀)
    ((sample ((Z).goodLabel T g₀)).cast oldAxis)).trans_le (Nat.pow_le_pow_right (by decide) narrow)
  have agreement : fieldData=
      fun (v : Fin (S.hostSize i)) (j : Fin (Groups*2^k)) (ell : Fin (count deg₀ (2^res) cap₀))=>
        (oldData view₀) v (j.cast equalAxis) (ell.cast (congrArg (fun l=>count deg₀ l cap₀) oldAxis)):=by
    funext v j ell
    dsimp only [ClosedReset.Window.calendar_sender_matrix,DescentOldContactSender.matrixCast,ClosedReset.Window.senderMatrix]
    have peers : (view₀).peers=peer₀ := packet.routes
    rw [peers]
    rfl
  let result (data : Fin (S.hostSize i)→Fin (Groups*2^k)→Fin (count deg₀ (2^res) cap₀)→Cell field) :=
    (board).rootActual levels ((board).observedWord (Z).width f m (DescentRecordedRotorLayers.width f cap₀)
      mapping ((board).measuredFields (D:=deg₀) (cap:=cap₀) data (fun _ _=>(cap₀:Cell field)) priorLevel fieldFlag))
      rawRoot slot x row h₀ group
  refine (congrArg result agreement).trans ?_
  exact registered_root_rotation (args:=args) (lanes:=lanes) (oldLanes:=oldLanes) (classes:=classes)
    (priceBits:=priceBits) (spanBits:=spanBits) b hp whole a earlier stored view₀ equalAxis
    elapsed sorted baseRoom nRoom depthRoom capRoom side g₀ gate flagBound mode op atom slot x h₀ group
    found origin row keyRow layer number inside

private theorem pitch_source {hostsJ J K t M w : ℕ} {e : Expr} {mem : Memory w}
    (same : J=K) (v : Fin hostsJ→Fin K→Cell t) (run : DescentPackedZip.Source e v M mem) :
    DescentPackedZip.Source e (fun h g=>v h (g.cast same)) M mem:=by subst J;exact run

omit [Fintype P] in
include packet in
set_option maxHeartbeats 3000000 in
/-- The role packet and the root rotation above share the previous signed matrix.
The slot and sheet inequalities are the original issued book's address receipts. -/
theorem root_packet_observed {hw : ℕ} (builder : RootSources deg₀ (2^res) cap₀)
    (graph : NonlinearExpanders.Graph (Z).n hw) (factor hubBits : ℕ)
    (neighbors hubs : Bank) (start cmp : ℕ)
    (pair : ℕ→DescentSharedLeafLookup.Header→Fin deg₀→Fin deg₀→Fin 6→Expr)
    (page : RootPage res (2^(Z).n))
    (sameLanes : oldLanes=M₀)
    (sameBook : book=builder.reserved (field:=field) graph (Z).width f height₀ C m stop
      (DescentRecordedRotorLayers.width f cap₀) mapping (S.hostSize i) factor hubBits neighbors hubs
      start (Groups*2^k) M₀ cmp pair page)
    (sameMatrix : ∀s root j,((book.good s root (.inl false)).2.reads j)=
      src.matrixRow (S.hostSize i) (j.cast (by rw [sameBook]; rfl)))
    (sameFlag : builder.here=src.here)
    (operands : src.OperandRoom (S.hostSize i) (2^dim) M₀ bw (rc.headerEnd book))
    (flagRoom : ∀lo,(S.hostSize i)*DescentSIMDLookup.chunks (2^dim) M₀≤(src.here lo).size)
    (controls : DescentPackedZip.Source builder.priorCap (fun (_ : Fin (S.hostSize i)) (_ : Block dim)=>(cap₀:Cell field))
        M₀ (rc.preparedMid book space mem) ∧
      DescentPackedZip.Source builder.relativeDepth (fun (h : Fin (S.hostSize i)) (_ : Block dim)=>
        (Receiver.depthDigit dim (Fintype.card cap.V) (ClosedReset.Recorded.oldDepth b) h:Cell field))
        M₀ (rc.preparedMid book space mem))
    (held : ∀side root gate j,((book.good side root (.inr gate)).2.reads j).Fits bw
      ((RootTemplates.arena (rc.headerEnd book) (S.hostSize i) (2^dim) M₀ res (Z).n deg₀).middle
        ((rootIndex res (2^(Z).n) (side,.inl (root,.inr gate))).val)))
    (short : M₀*max (field*guardInputs deg₀ (2^res) cap₀) (bits₀*stop)≤bw/2)
    (pos : 0<M₀) (floor : ℕ) (later : Memory bw) (past : rc.preparedEnd book≤floor)
    (room : floor<2^bw) (frame : ∀j,j<floor→later j=rc.preparedImage book space mem j) :
    (board).Observed (guards (rc.headerEnd book) (S.hostSize i) (Groups*2^k) M₀ res (Z).n deg₀)
      later levels paidRoles:=by
  let values := fieldData
  have matrixRead (j : Fin (count deg₀ (2^res) cap₀)) :
      DescentPackedZip.Source (src.matrixRow (S.hostSize i) j) (fun host group => values host group j)
        M₀ (rc.preparedMid book space mem) := by
    let column := fun (host : Fin (S.hostSize i)) (hi : Block dim) =>
      ClosedReset.Window.calendar_sender_matrix b M₀ field rc book space mem hdr raw host hi j
    have atMid : DescentPackedZip.Source (src.matrixRow (S.hostSize i) j) column M₀ (rc.preparedMid book space mem) := by
      intro pos
      exact (eval_below _ _ _ _ (src.matrix_fit operands j) (rc.before_header _ space mem)).symm.trans (packet.matrix j pos)
    exact pitch_source equalAxis column atMid
  have matrixIssued (side : Bool) (row : ↥(DescentHostDirectory.codes res))
      (j : Fin (book.good side row (.inl false)).1) :
      DescentPackedZip.Source ((book.good side row (.inl false)).2.reads j)
        (fun host group => values host group (j.cast (by rw [sameBook]; rfl)))
        M₀ (rc.preparedMid book space mem) := by
    rw [sameMatrix]
    exact matrixRead _
  have capacityIssued := pitch_source equalAxis _ controls.1
  have depthIssued := pitch_source equalAxis _ controls.2
  have flagsIssued (lo : Block res) : DescentPackedZip.Source (builder.self lo) (fieldFlag lo) M₀
      (rc.preparedMid book space mem) := by
    change DescentPackedZip.Source (.lookup (builder.here lo) .row) _ _ _
    rw [sameFlag]
    exact pitch_source equalAxis _ (DescentPackedZip.source_column (src.here lo) _ (operands.localShape _) _ _ (flagRoom _) (packet.sites lo))
  let Q := (board)
  subst oldLanes
  subst book
  exact Q.observed_prepared builder graph (Z).width f height₀ C m (DescentRecordedRotorLayers.width f cap₀)
    mapping factor hubBits neighbors hubs start cmp pair page rc equalAxis space mem values
    (fun _ _=>(cap₀:Cell field)) priorLevel fieldFlag matrixIssued capacityIssued depthIssued flagsIssued
    held short pos floor later past room frame

include stored packet in
omit [Fintype P] in
/-- Both halves refer to the same original packet and the same later memory. -/
theorem root_packet_registers {hw : ℕ} (builder : RootSources deg₀ (2^res) cap₀)
    (graph : NonlinearExpanders.Graph (Z).n hw) (factor hubBits : ℕ)
    (neighbors hubs : Bank) (start cmp : ℕ)
    (pair : ℕ→DescentSharedLeafLookup.Header→Fin deg₀→Fin deg₀→Fin 6→Expr)
    (page : RootPage res (2^(Z).n))
    (sameLanes : oldLanes=M₀)
    (sameBook : book=builder.reserved (field:=field) graph (Z).width f height₀ C m stop
      (DescentRecordedRotorLayers.width f cap₀) mapping (S.hostSize i) factor hubBits neighbors hubs
      start (Groups*2^k) M₀ cmp pair page)
    (sameMatrix : ∀s root j,((book.good s root (.inl false)).2.reads j)=
      src.matrixRow (S.hostSize i) (j.cast (by rw [sameBook]; rfl)))
    (sameFlag : builder.here=src.here)
    (operands : src.OperandRoom (S.hostSize i) (2^dim) M₀ bw (rc.headerEnd book))
    (flagRoom : ∀lo,(S.hostSize i)*DescentSIMDLookup.chunks (2^dim) M₀≤(src.here lo).size)
    (controls : DescentPackedZip.Source builder.priorCap (fun (_ : Fin (S.hostSize i)) (_ : Block dim)=>(cap₀:Cell field))
        M₀ (rc.preparedMid book space mem) ∧
      DescentPackedZip.Source builder.relativeDepth (fun (h : Fin (S.hostSize i)) (_ : Block dim)=>
        (Receiver.depthDigit dim (Fintype.card cap.V) (ClosedReset.Recorded.oldDepth b) h:Cell field))
        M₀ (rc.preparedMid book space mem))
    (held : ∀side root gate j,((book.good side root (.inr gate)).2.reads j).Fits bw
      ((RootTemplates.arena (rc.headerEnd book) (S.hostSize i) (2^dim) M₀ res (Z).n deg₀).middle
        ((rootIndex res (2^(Z).n) (side,.inl (root,.inr gate))).val)))
    (short : M₀*max (field*guardInputs deg₀ (2^res) cap₀) (bits₀*stop)≤bw/2)
    (pos : 0<M₀) (floor : ℕ) (later : Memory bw) (past : rc.preparedEnd book≤floor)
    (room : floor<2^bw) (frame : ∀j,j<floor→later j=rc.preparedImage book space mem j)
    (elapsed : 0< i) (sorted : SourceSorted W cap.order)
    (baseRoom : max (max res (2^(Z).n)) (2^res)<2^field) (nRoom : (Z).n<field)
    (depthRoom : res+1<2^field) (capRoom : cap₀<2^field)
    (narrow : t≤field) (level : res<2^nbits) (one : 1<2^nbits) (amount : 2^res*total₀<2^nbits)
    (shape : 2*DescentFallbackShapeTable.rows res (2^(Z).n)≤2^t)
    (active : 0<total₀) (quotaPos : 0<quota S.rounds) (degreePos : 0<32*Nat.clog 2 (2*deg₀))
    (date : ℕ) (grain : z=S.grainAt G.b p date)
    (stopAt : ClosedReset.calendarBatchCount S n ctl.bitsR f cap₀ G.b date≤ stop) :
    (board).Observed (guards (rc.headerEnd book) (S.hostSize i) (Groups*2^k) M₀ res (Z).n deg₀)
      later levels paidRoles ∧
      ∀(slot : Fin nodes) (x : Block k) (h : Fin H) (group : Fin Groups) (atom : NodeOrder.All next)
      (side : Bool) (g₀ : (rr).Good) (gate : Fin (2^(Z).n)) (op : (prog (rootSite side g₀ gate)).Node)
      (row : Fin (board).roots) (layer : Fin ((Z).circuit side g₀).layers),
      cell x slot h group=some atom → names atom=.inr (.inr (rootNode side g₀ gate op)) →
      (originClass b hp whole a (.inr (.inr (rootNode side g₀ gate op)))).val=6+row.val →
      slot.val/m=layer.val →
      (board).rootActual levels paidRoles rawRoot slot x row h group=
        (rotorNumber (((Z).circuit side g₀).rotation layer) gate:Cell bits₀):=by
  constructor
  · exact root_packet_observed (nodes:=nodes) (args:=args) (lanes:=lanes) (classes:=classes)
      (priceBits:=priceBits) (spanBits:=spanBits) b equalAxis rc book space mem hdr src raw packet
      builder graph factor hubBits neighbors hubs start cmp pair page sameLanes sameBook sameMatrix sameFlag
      operands flagRoom controls held short pos floor later past room frame
  · intro slot x host group atom side good gate op row layer found origin keyRow number
    exact root_packet_rotation (args:=args) (lanes:=lanes) (oldLanes:=oldLanes) (classes:=classes)
      (priceBits:=priceBits) (spanBits:=spanBits) b hp whole a earlier stored equalAxis rc book space mem hdr src raw
      packet elapsed sorted baseRoom nRoom depthRoom capRoom narrow level one amount shape active quotaPos degreePos
      side good gate op atom slot x host group found origin row keyRow layer number date grain stopAt

include stored packet in
/-- The subscribed compact inverse in this register is the genuine sparse physical
actor rank recovered from the original chronological root packet. -/
def acquired_root_register {hw : ℕ} (builder : RootSources deg₀ (2^res) cap₀)
    (graph : NonlinearExpanders.Graph (Z).n hw) (factor hubBits : ℕ)
    (neighbors hubs : Bank) (start cmp : ℕ)
    (pair : ℕ→DescentSharedLeafLookup.Header→Fin deg₀→Fin deg₀→Fin 6→Expr)
    (page : RootPage res (2^(Z).n))
    (sameLanes : oldLanes=M₀)
    (sameBook : book=builder.reserved (field:=field) graph (Z).width f height₀ C m stop
      (DescentRecordedRotorLayers.width f cap₀) mapping (S.hostSize i) factor hubBits neighbors hubs
      start (Groups*2^k) M₀ cmp pair page)
    (sameMatrix : ∀s root j,((book.good s root (.inl false)).2.reads j)=
      src.matrixRow (S.hostSize i) (j.cast (by rw [sameBook]; rfl)))
    (sameFlag : builder.here=src.here)
    (operands : src.OperandRoom (S.hostSize i) (2^dim) M₀ bw (rc.headerEnd book))
    (flagRoom : ∀lo,(S.hostSize i)*DescentSIMDLookup.chunks (2^dim) M₀≤(src.here lo).size)
    (controls : DescentPackedZip.Source builder.priorCap (fun (_ : Fin (S.hostSize i)) (_ : Block dim)=>(cap₀:Cell field))
        M₀ (rc.preparedMid book space mem) ∧
      DescentPackedZip.Source builder.relativeDepth (fun (h : Fin (S.hostSize i)) (_ : Block dim)=>
        (Receiver.depthDigit dim (Fintype.card cap.V) (ClosedReset.Recorded.oldDepth b) h:Cell field))
        M₀ (rc.preparedMid book space mem))
    (held : ∀side root gate j,((book.good side root (.inr gate)).2.reads j).Fits bw
      ((RootTemplates.arena (rc.headerEnd book) (S.hostSize i) (2^dim) M₀ res (Z).n deg₀).middle
        ((rootIndex res (2^(Z).n) (side,.inl (root,.inr gate))).val)))
    (short : M₀*max (field*guardInputs deg₀ (2^res) cap₀) (bits₀*stop)≤bw/2)
    (pos : 0<M₀) (floor : ℕ) (later : Memory bw) (past : rc.preparedEnd book≤floor)
    (room : floor<2^bw) (frame : ∀j,j<floor→later j=rc.preparedImage book space mem j)
    (elapsed : 0< i) (sorted : SourceSorted W cap.order)
    (baseRoom : max (max res (2^(Z).n)) (2^res)<2^field) (nRoom : (Z).n<field)
    (depthRoom : res+1<2^field) (capRoom : cap₀<2^field)
    (narrow : t≤field) (level : res<2^nbits) (one : 1<2^nbits) (amount : 2^res*total₀<2^nbits)
    (shape : 2*DescentFallbackShapeTable.rows res (2^(Z).n)≤2^t)
    (active : 0<total₀) (quotaPos : 0<quota S.rounds) (degreePos : 0<32*Nat.clog 2 (2*deg₀))
    (date : ℕ) (grain : z=S.grainAt G.b p date)
    (stopAt : ClosedReset.calendarBatchCount S n ctl.bitsR f cap₀ G.b date≤ stop) :
    RootRegister b hp whole a earlier board
      (guards (rc.headerEnd book) (S.hostSize i) (Groups*2^k) M₀ res (Z).n deg₀) later rfl rfl rfl:=by
  have acquired:=root_packet_registers (nodes:=nodes) (args:=args) (lanes:=lanes) (classes:=classes)
    (priceBits:=priceBits) (spanBits:=spanBits) b hp whole a earlier stored equalAxis rc book space mem hdr src raw packet
    builder graph factor hubBits neighbors hubs start cmp pair page sameLanes sameBook sameMatrix sameFlag operands
    flagRoom controls held short pos floor later past room frame elapsed sorted baseRoom nRoom depthRoom capRoom narrow
    level one amount shape active quotaPos degreePos date grain stopAt
  exact ⟨levels,paidRoles,rawRoot,fun _=>rfl,acquired.1,acquired.2⟩

end
end Hierarchy.DescentPrimitivePalette

end OAI
