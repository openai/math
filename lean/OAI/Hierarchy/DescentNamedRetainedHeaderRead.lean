import OAI.Hierarchy.DescentOriginalRetainedFields
import OAI.Hierarchy.DescentRegisteredPrimarySigned
import OAI.Hierarchy.DescentRegisteredWindowSelectors
import OAI.Hierarchy.DescentCalendarRetainedOperandHeaders
import OAI.Hierarchy.DescentNamedPrimaryShape
import OAI.Hierarchy.DescentOriginalOperandLocation
import OAI.Hierarchy.DescentNamedCableHeaderRoom

namespace OAI
/-! The registered four pointer fields for one formal argument of an actual retained node. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open DescentSixParty.PackedFlow.Channels
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F Pin : Type} [Field F] {d : ℕ} {abits : Pin→ℕ} {W : MarkedWorld F d Pin abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
local notation "datedInputValue" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

open DescentSortedRoster

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open DescentSharedCableNames
local notation "A₁" => (v).receiver
local notation "ST" => (v).sheetsStart base₀
local notation "plan" => (v).linkedRankInputs (datedInputValue).sectors ST
local notation "draw" => (v).renderFromRanks plan base₀
local notation "physicalRack" => rackOf B (((Z).denseHostRank T rank).trans (Fin.castLEEmb B.next.valid.host))
open DescentResetTrunks

local notation "fetch" gg:arg hx:arg hj:arg peers:arg h:arg gr:arg x:arg j:arg =>
  ((physicalRack (((h):Fin (A₁).hosts).cast peers)).bind (fun z=>
    candidateRows B (fieldNames B) ((((gr):Fin (A₁).groups).cast gg,z),((x):Fin (A₁).blocks).cast hx)
      (((j):Fin (2*(A₁).candidates)).cast (congrArg (2*·) hj))))


local notation "I" => datedInputValue
open DescentPackedZip DescentResetOperandSetup
variable (ok : (I).Ready) (actorMem : Memory w) {N : ℕ}
local notation "hw" => (v).setup
local notation "r₀" => (hw).retained
local notation "hh" => (hw).placement.newHosts
local notation "gg" => (hw).placement.groups
local notation "base" => (v).operandFloor base₀
local notation "m" => (I).beforeSetupImage ok actorMem
local notation "cfg" => publicOperands (I).atlas (I).roots (I).menu.payload
variable (x₀ : Fin (v).receiver.blocks) (arg : Fin (r₀).args) (node : Fin (r₀).nodes)
local notation "x" => x₀.cast (I).operandBlocks
local notation "ctrl" => (v).controlRegisters
local notation "controlFloor_" => (v).controlFloor base₀
local notation "actor" => (v).actor
local notation "origin" => (v).middle.stop base₀
local notation "active" => (ctrl).live controlFloor_ (x).val
local notation "reg" => (ctrl).ports controlFloor_ ((a).c/2) (x).val ((actor).directory origin).inverse
    ((actor).depths origin) ((actor).levels origin)
local notation "ports" => OperandMenu.publicPorts («a»:=(a)) (I).shape start (I).count (I).hub (I).g (I).Y active reg
variable (values : (ports).Values hh gg)
variable (name : Fin N→Fin (hw).placement.sparse)
variable (hostEq : (hw).placement.oldHosts=(r₀).hosts) (groupEq : (hw).placement.groups*(hw).placement.blocks=(r₀).grouped)
variable (X : (hw).seven.Packets) (strips : (r₀).Strips)
local notation "s" => (I).bank
local notation "Ys" => (hw).assignedDigits hostEq groupEq (s).which X strips
variable (signed : Fin (hw).strip→Fin (hw).placement.oldHosts→Fin ((hw).placement.groups*(hw).placement.blocks)→Cell (hw).signedBits)
variable (hubWord : Fin hh→Fin gg→Cell (hw).fieldBits) (tickets : Fin (hw).strip→Fin hh→Fin gg→Cell (hw).fieldBits)
local notation "raw" => (hw).carriedRow (s) name (Ys) signed x arg node hubWord tickets
local notation "rowData" => (I).menu.publicData (I).shape start (I).count (I).hub (I).g (I).Y active reg values rfl (x).val
local notation "at_" => (finProdFinEquiv (arg,node) : Fin (hw).members)
local notation "dst" => ((hw).code base w (s) (I).laws).image m
local notation "oldCell" f:arg h:arg k:arg => ((DescentRetainedTargetPlacement.Chart.compact (hw).placement (hw).seven.batch
  (s).primary name (Ys) ((r₀).outputID 1 f arg node) x h k).val : Cell (hw).fieldBits)
local notation "rot" width:arg f:arg h:arg k:arg => ((cfg).rotor.flatReg (I).atlas.board (cfg).multiplicity (cfg).grain (cfg).split
   node.val arg.val f ((cfg).reg ((rowData) h k)) : Cell width)
local notation "pub" width:arg f:arg h:arg k:arg => (cfg).column (I).atlas.board width f at_ ((rowData) h k)
local notation "mark" => (v).retainedHub base₀ x
local notation "fee" => (v).retainedTicket base₀ x
local notation "ord" f:arg => (v).operandOrdinal (I).operand f arg x₀ node

open DescentSixParty.Chronology.DatePorts DescentOperandCandidateLookup

local notation "A" => (v).receiver
local notation "realFields" => DateInputs.IssuedFieldsAt G S board k tail age p f g drift degree payload e previous
  M nextM C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut
  count previousMeta previousArguments initial prepared sceneRoom ok actorMem x₀ arg node values name hostEq groupEq
  X strips signed hubWord tickets


variable (small : 2*(A).candidates<2^(A).queryBits)
variable (choice : ∀f₀:Fin 7,OrdinalRead (I) ok small actorMem (ord f₀)) (read : realFields)

variable (observed : (I).PublicValuesRead ok actorMem x rfl name values)
variable (hx : (A₁).blocks=2^k) (hj : (A₁).candidates=totalLocal B)
    (groupsAt : (A₁).groups=S.groupCount (age+1)) (aligned : (A₁).hosts=(v).sheets.hosts)
variable (archive : ∀i j,let y:=(v).operandIndex (I).operand i
      Source ((v).previous (I).operand draw base₀ i j)
        (fun h gr=>ResetOutput.signedCandidateField (A₁).signedBits y.2.1
          (fetch groupsAt hx hj aligned h gr y.1 j)) (A₁).lanes ((I).operandEntry ok actorMem))
local notation "real" f₀:arg j:arg h:arg gr:arg => ResetOutput.nativeCandidateField (A₁).signedBits (A₁).valueBits f₀
  (fetch groupsAt hx hj aligned h gr x₀ j)
local notation "candidate" f₀:arg h:arg gr:arg => (DescentOperandCandidateLookup.selected (choice 0).query (fun j h gr=>real f₀ j h gr) h gr).val

local notation "issued" h:arg gr:arg => OperandMenu.queryDigit («a»:=(a)) ((hw).cable.query ((raw) h gr))
  (rot (hw).queryBits 0 h gr) (pub (hw).queryBits none h gr)
local notation "posted" f:arg h:arg gr:arg => ((((oldCell f h gr).val+((hw).cable.priceField f ((raw) h gr)).val+
  (rot (hw).fieldBits (f).succ h gr).val+(pub (hw).fieldBits (some f) h gr).val:ℕ):Cell (hw).fieldBits).val:Cell (A).valueBits)


open DescentSixParty.Chronology DescentSixParty.ResetInput DescentResetLocalNodes
open DescentPlainTerminal DescentPackedResetDonors DescentBaseProfile DescentResetHostSize DescentPaidResidentCount.Reset
open DescentPacking.PackedMatch.Local.Stage DescentPhysicalOrder DescentRetainedResetPinPointer
open DescentPrimitivePalette DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder
open DescentIssuedFallbackPanel DescentPaidResidentCount.Reset DescentRetainedRangeDigits
open DescentRetainedPrivateSlotBook DescentRelativeContacts DescentFallbackShapeTable DescentPackedWalsh
open DescentLocalPrivateNames DescentRetainedControl DescentSixParty.ClosedReset
open DescentPacking.PackedMatch.Local.Stage DescentRotorWindowArchive DescentGL
open scoped BigOperators
variable (oldA:Archive W) (oldNum:Local oldA.bit) (hp:0<p) (whole:p∣(Z).unit) {R:ℕ}
  (one:1≤R) (unitPos:0<(Z).unit) (widthBound:max 1 (max (Z).width (C*(Z).width))≤R)
  (shape:WorldShape p R oldA.bit)
local notation "after_" => (resetArchive B p hp whole oldA).bit
local notation "order_" => DescentLocalArchiveOrder.reset B p hp whole oldA oldNum
variable (now:NodeOrder.All after_) (prior:NodeOrder.All oldA.bit) (source:resetOrigin B hp whole oldA now=Sum.inl prior)
local notation "term" => (T).home prior.1
local notation "residual" => (Z).k-(T).commonDepth
local notation "fib" => DescentNamedContact.Fibre (T).home term
local notation "small_" => B.frame.enough.trans (Nat.sub_le ..)
local notation "wide_" => S.groupWidth k tail age+k
local notation "ix" t:arg => StarKeys.filled W.graph input.placement.pos input.placement.block (S.resetInputDigits ctl.base ctl.radix age) t
local notation "split_" => shape.granular B.count (z*G.b) B.fit hp (B.unit ▸ unitPos) (B.unit ▸ whole)
local notation "legal" => ((Nat.div_mul_cancel whole).symm:(Z).unit=(Z).unit/p*p)
local notation "installed" => reentryWorldShape split_ (Z) (T) (DescentOrderedReset.grains W B.count B.order) _ hp legal
    (resetMenu B) one widthBound
local notation "successor" => WorldShape.follow hp unitPos whole B.reblock B.cuts installed
local notation "current" => ((successor).sites now.1).recipe hp
local notation "oldRecipe" u:arg => (shape.sites (u:fib).val).recipe hp
local notation "donorBook" => reached B hp one unitPos whole widthBound oldA shape now prior source
variable (oldRoom:∀u,Fintype.card (oldA.bit.recipe u).Node≤(r₀).previousNodes)
  (newRoom:Fintype.card ((after_).recipe now.1).Node≤(r₀).nodes)
  (oldArgs:∀(u:fib) n₀,(oldRecipe u).arity n₀≤(r₀).previousArgs)
  (newArgs:∀n₀,(current).arity n₀≤(r₀).args) (pin:Pin→ℕ)
  (mouth:Slot current)
local notation "newAddr" => reached_mouth current ((order_ now.1).toEmbedding.trans (Fin.castLEEmb newRoom)) newArgs
local notation "pos_" => (finProdFinEquiv.symm (newAddr mouth):Fin (r₀).nodes×Fin (r₀).args)
variable (atArg:arg=(pos_).2) (atNode:node=(pos_).1)
variable (total:(r₀).high+(r₀).low=wide_) (axis:(r₀).cut=(T).commonDepth)
  (oldBlocks:(r₀).blocks=2^k) (oldGroups:(r₀).groups=S.groupCount age)
  (length:2^((r₀).high+(r₀).low)=(r₀).groups*(r₀).blocks)
  (cutRoom:(r₀).cut≤(r₀).high+(r₀).low) (basis:DescentGL.Layout ((r₀).high+(r₀).low))
  (attained:HEq basis B.frame.basis) (oldValues:(r₀).Values)
  (oldStrips:strips=fun j=>blockValues cutRoom ((r₀).before length oldValues j) basis)
  (oldHosts:Fintype.card input.V≤(r₀).hosts)
local notation "oldNames" => input.vertex.trans (Fin.castLEEmb oldHosts)
local notation "sourceHost" => B.frame.host.symm ((T).code term).1
local notation "carrier" => oldNames sourceHost
local notation "hi" => (Z).rootBlock T (.inr term)
local notation "coarse" => (hi).cast (congrArg (2^·) axis).symm
local notation "lowAxis" => congrArg (fun bitsCount : ℕ => 2^bitsCount) (congrArg₂ Nat.sub total axis)
local notation "coords" => finCongr lowAxis
local notation "source_" lo:arg => (rearrange B.frame.basis).symm (join small_ hi lo)
local notation "rail" lo:arg => (rearrange basis).symm (join cutRoom coarse ((coords).symm lo))
local notation "place" lo:arg => (finProdFinEquiv.symm ((rail lo).cast length):Fin (r₀).groups×Fin (r₀).blocks)
local notation "wrd" => (r₀).site strips carrier coarse
local notation "donors" => calendar_donor_index (b:=B) («a»:=oldA) (yy:=prior) (chart:=hw) (total:=total) (axis:=axis)
variable (rh:Fin hh) (rg:Fin gg) (present:rh.val<N)
local notation "token" => (hw).placement.shape (name ⟨rh.val,present⟩)
local notation "keeper" => (hw).placement.previous (name ⟨rh.val,present⟩)
variable (homeHost:(keeper).cast hostEq=carrier) (homeBlock:(finProdFinEquiv (rg,x)).cast groupEq=coarse)

local notation "key" => DescentFallbackShapeTable.cell residual (shortName (T).commonDepth ((T).code term)).2
variable (rootBits:ℕ) (xs:OriginalArrays B input.valid.host rootBits)
local notation "word" => xs.stencil (idx sourceHost) hi
local notation "coarseSize" => (T).commonDepth
local notation "rootDep" => GroupStage.depthBound D n f g
variable {N₀ K₀ R₀ hm lb bit:ℕ} (M₀:ℕ)
  (received:DescentFallbackPeriod.Projected.Receiver input.placement.degree input.placement.cap N₀ (Z).n residual coarseSize
    (S.hostSize age) (S.groupCount age) K₀ R₀ M₀ hm lb bit rootBits rootDep w)
  (rootBook:DescentFallbackPeriod.Projected.RootBook (Z).n residual input.placement.degree (2^residual) input.placement.cap rootBits)
  (room₀:received.PreparedFits rootBook) (measured:Memory w)
  (hdr:OriginalHeader B input.valid.host received rootBook measured)
  (target:(s).which token=some key)
  (matrixRead:(X carrier coarse).val=(encode rootBits (DescentRotorWindowArchive.count input.placement.degree
    (2^residual) input.placement.cap) (calendar_sender_matrix B M₀ rootBits received rootBook room₀ measured hdr xs
      (idx sourceHost) hi)).val)
  (rowDegree:(hw).seven.degree=input.placement.degree) (rowCap:(hw).seven.capacity=input.placement.cap)
  (rowBits:(hw).seven.packetBits=rootBits) (rowPos:0<rootBits)
  (stencilFits:∀lo,word lo<2^rootBits)
  (pop:∀lo,(r₀).originalCount wrd ((coords).symm lo)=∑u:W.graph.Site,
    if DescentPaidResidentCount.occupies input.placement (Equiv.refl _) oldNames carrier ((place lo).1.cast oldGroups)
      ((place lo).2.cast oldBlocks) u then Fintype.card (oldA.bit.recipe u).Node else 0)
local notation "oldN" u:arg n:arg => (oldNum (u:fib).val n).castLE (oldRoom (u:fib).val)
local notation "oldJ" u:arg entrySlot:arg => (entrySlot:Slot (oldRecipe u)).2.castLE (oldArgs u (entrySlot:Slot (oldRecipe u)).1)
variable (arities:∀(u:fib) n,((r₀).entry wrd (donors u) (oldN u n) (r₀).arityField).val=(oldRecipe u).arity n)
  (oldReads:∀(u:fib)(s₀:Slot (oldRecipe u))(f₀:Fin 4),
    ((r₀).entry wrd (donors u) (oldN u s₀.1) ((r₀).operandField (f₀.castLE (by decide:4≤7)) (oldJ u s₀))).val=
      (Reached.argumentPointer input oldA.bit oldNum shape hp pin (r₀).previousArgs ⟨u.val,s₀.1⟩ s₀.2.val).header f₀)
local notation "p_" => ((hw).sources base w (s)).image m
variable (moved:(hw).Moved base (s) name p_ Ys signed)
local notation "here" => (raw) rh rg
local notation "prevSign" => input.order.trans Fin.valEmbedding
local notation "peerNames" => DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank
    ((Function.Embedding.refl (Fin (S.groupCount age))).trans Fin.valEmbedding) (input.vertex.trans Fin.valEmbedding))
local notation "anc" => ((donorBook).slots mouth).1
local notation "selectedDonor" => donors anc
local notation "grains" => W.granular B.count (z*G.b) B.fit
set_option maxHeartbeats 900000
variable (deg:(hw).cable.degree=input.placement.degree) (capEq:(hw).cable.cap=input.placement.cap)
  (donorEq:(hw).cable.donors=2^(wide_-(T).commonDepth)) (unitEq:(hw).cable.units=(Z).unit/p)
  (lowOld:(r₀).donors=2^((Z).k-(T).commonDepth))
  (hiOld:(hw).placement.groups*(hw).placement.blocks=2^(T).commonDepth)
  (signedRead:∀j h₀ hi₀,(signed j h₀ hi₀).val=
    (((DescentSignedCableCodec.encode (originalCable B xs h₀ (hi₀.cast hiOld)
      ((finProdFinEquiv.symm j).1.cast lowOld) ((finProdFinEquiv.symm j).2.cast (congrArg (2*·) capEq)))).val:Cell rootBits)).val)
  (oldCodec:DescentSignedCableCodec.width input.placement.degree input.placement.cap≤rootBits)
  (incoming:∀incomingEdge:(grains).graph.Edge,(T).home ((grains).graph.dst incomingEdge)=term→∀j:Fin (hw).strip,
    j.val=(incomingIndex B incomingEdge).val→(tickets j rh rg).val=earlierIncoming B incomingEdge)
  (hub:hubWord rh rg=if ((T).code term).2.2.isSome then 0 else 1)
local notation "loc_" h:arg g:arg => operandLocation B (x₀.cast hx) (((h):Fin (A₁).hosts).cast aligned) (((g):Fin (A₁).groups).cast groupsAt)
variable (located:loc_ rh rg=some (Stage.home B.next.placement now.1))
local notation "pointer" => Reached.argumentPointer B.next after_ order_ successor hp pin (r₀).args ⟨now.1,mouth.1⟩ mouth.2.val
variable (digitRoom:(r₀).bits*(hw).lanes≤w) (fieldRoom:(r₀).bits≤(hw).fieldBits)
  (output:(r₀).bits≤(A).valueBits) (shelf:(r₀).donors<2^(r₀).bits)
  (chipRoom:DescentSignedCableCodec.width input.placement.degree input.placement.cap≤(hw).fieldBits) (grainRoom:(hw).cable.units*B.next.placement.cap≤2^(hw).cable.fieldBits)
  (positive:1<2^(hw).fieldBits) (alphabet:max (B.next.placement.degree+1) (B.next.placement.cap+1)≤2^(A).signedBits)
  (oldWidth:(r₀).previousNodes*(r₀).previousArgs≤2^(r₀).bits) (newWidth:(r₀).nodes*(r₀).args≤2^(r₀).bits)
  (cableRoom:∀peer serial part,pointer=.cable peer serial part→∀f₀:Fin 4,(pointer).header f₀<2^(A).valueBits)

local notation "pairedRot" width:arg field:arg h:arg gr:arg =>
  ((cfg).rotor.flatReg (I).atlas.board (cfg).multiplicity (cfg).grain (cfg).split
    ((@finProdFinEquiv (r₀).args (r₀).nodes).symm at_).2.val
    ((@finProdFinEquiv (r₀).args (r₀).nodes).symm at_).1.val field ((cfg).reg ((rowData) h gr)) : Cell width)
local notation "pairedQuery" h:arg gr:arg => OperandMenu.queryDigit («a»:=(a)) ((hw).cable.query ((raw) h gr))
  (pairedRot (hw).queryBits 0 h gr) (pub (hw).queryBits none h gr)
local notation "pairedField" f:arg h:arg gr:arg => ((((oldCell f h gr).val+((hw).cable.priceField f ((raw) h gr)).val+
  (pairedRot (hw).fieldBits (f).succ h gr).val+(pub (hw).fieldBits (some f) h gr).val:ℕ):Cell (hw).fieldBits).val:Cell (A).valueBits)

set_option maxHeartbeats 2400000 in
include source read archive observed oldStrips atArg atNode attained homeHost homeBlock target matrixRead rowDegree rowCap rowBits rowPos stencilFits pop arities
  oldReads moved deg capEq donorEq unitEq signedRead oldCodec incoming hub located digitRoom fieldRoom output shelf chipRoom
  grainRoom positive alphabet oldWidth newWidth cableRoom in
theorem DateInputs.original_primary_header :
    ∀f₀:Fin 4,((choice (f₀.castLE (by decide:4≤7))).amount rh rg).val=(pointer).header f₀:=by
  obtain ⟨_,_,_,_,_,blank,physical⟩:=observed
  have lanePos:0<(hw).lanes:=ok.placed.lanes
  let ch:Fin (chunks gg (hw).lanes):=(DescentSIMDLookup.position rh rg lanePos).2
  let lane₀:=DescentSIMDLookup.lane rg lanePos
  have active_:ch.val*(hw).lanes+lane₀.val=rg.val:=Nat.div_add_mod' ..
  have chosen: (I).menu.keep token=true:=(I).menu.keep_of_target token key target
  obtain ⟨measuredOwn,measuredCmp⟩:=registered_window_selectors B M₀ rootBits received rootBook room₀ measured
    hdr xs (hw) (s).which X token carrier coarse (idx sourceHost) hi key target rowDegree lowOld rowCap rowBits
    matrixRead rowPos stencilFits
  have owns:ownerAt hw (s).which X token carrier coarse=(fun j=>decide (word (coords j)/2=key)):=by
    refine measuredOwn.trans ?_
    funext j
    apply congrArg (fun lo => decide (word lo / 2 = key))
    exact Fin.ext rfl
  have cmp:priorAt hw X carrier coarse=(fun d j=>decide (source_ (coords d)<source_ (coords j))):=by
    refine measuredCmp.trans ?_
    funext d j
    apply congrArg₂ (fun l₁ l₂ => decide (source_ l₁ < source_ l₂))
    · exact Fin.ext rfl
    · exact Fin.ext rfl
  have stencil:=primary_original_stencil B xs sourceHost hi
  have oldAt:keeper=idx (input.placement.pos (anc).val).2:=by
    have trueHost : sourceHost=(input.placement.pos (anc).val).2 := by
      apply B.frame.host.injective
      exact (B.frame.host.apply_symm_apply _).trans
        ((congrArg (fun t => ((T).code t).1) (anc).property.symm).trans (B.frame.homeHost _))
    apply Fin.ext
    have hostVal := congrArg (fun t : Fin (r₀).hosts => t.val) homeHost
    change (keeper).val = (input.vertex sourceHost).val at hostVal
    change (keeper).val = (input.vertex (input.placement.pos (anc).val).2).val
    exact hostVal.trans (congrArg (fun t => (input.vertex t).val) trueHost)
  have covered:=old_home_digit B.frame term (anc)
  have highOld:DescentPlainTerminal.high small_ (rearrange B.frame.basis (ix (anc).val))=hi:=by
    conv_lhs => rw [covered,Equiv.apply_symm_apply,high_join]
  let oldReg:Fin (hw).strip→Cell (hw).signedBits:=fun j=>signed j keeper (finProdFinEquiv (rg,x))
  have readOld:∀j,(oldReg j).val=(((DescentSignedCableCodec.encode (originalCable B xs
      (idx (input.placement.pos (anc).val).2) (DescentPlainTerminal.high small_ (rearrange B.frame.basis (ix (anc).val)))
      ((finProdFinEquiv.symm j).1.cast lowOld) ((finProdFinEquiv.symm j).2.cast (congrArg (2*·) capEq)))).val:Cell rootBits)).val:=by
    intro j
    have atHi:(finProdFinEquiv (rg,x)).cast hiOld=hi:=Fin.ext (congrArg (fun t : Fin (r₀).grouped => t.val) homeBlock)
    simpa only [oldReg,oldAt,highOld,atHi] using signedRead j keeper (finProdFinEquiv (rg,x))
  have honest:=fun j=>acquired_primary_signed B xs (anc).val lowOld capEq deg selectedDonor rfl oldReg readOld oldCodec j
  have short:=fun j=>acquired_primary_volume B xs (anc).val lowOld capEq selectedDonor oldReg readOld chipRoom j
  subst strips
  let strips:(r₀).Strips:=fun j=>blockValues cutRoom ((r₀).before length oldValues j) basis
  subst arg
  let arg:Fin (r₀).args:=(pos_).2
  subst node
  let node:Fin (r₀).nodes:=(pos_).1
  let registered:=fun (f₀:Fin 7) (j:Fin (2*(A₁).candidates)) h gr=>real f₀ j h gr
  have accounted : DescentOperandCandidateLookup.code small ((choice 0).query rh rg)=pairedQuery rh rg ∧
      ∀f₀:Fin 7,((choice f₀).amount rh rg).val=(pairedField f₀ rh rg).val+candidate f₀ rh rg := by
    have acquired:=DateInputs.original_retained_amount (B:=B) drift degree payload e previous M nextM
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
      previousArguments initial prepared sceneRoom ok actorMem x₀ arg node values name hostEq groupEq X strips
      signed hubWord tickets small choice read hx hj groupsAt aligned archive rh rg
    have pairAt := (@finProdFinEquiv (r₀).args (r₀).nodes).symm_apply_apply (arg,node)
    rw [pairAt]
    exact acquired
  have exactFields:=(calendar_retained_header_at_cable (b:=B)) («a»:=oldA) («early»:=oldNum) (menu:=(I).menu)
    (total:=total) (axis:=axis) (blocks:=oldBlocks) (groups:=oldGroups) (size:=length) (fits:=cutRoom)
    (L:=basis) (won:=attained) (room:=oldHosts) (nodeRoom:=oldRoom) (hp:=hp) (whole:=whole) (one:=one)
    (posUnit:=unitPos) (widthBound:=widthBound) («sh»:=shape) (xx:=now) (yy:=prior) («origin»:=source)
    (which:=(s).which) (window:=X) (shape:=token) (input:=oldValues) («word»:=word)
    (owns:=owns) (compared:=cmp) (stencil:=stencil) (counts:=pop) (oldArgs:=oldArgs) (nextRoom:=newRoom)
    (newArgs:=newArgs) (arityWords:=arities) (pin:=pin) (headerWords:=oldReads) (namesAt:=name)
    (data:=(rowData) rh rg) (mouth:=at_) (hostEq:=hostEq) (groupEq:=groupEq) (bank:=s) (whichEq:=rfl)
    (primaryEq:=rfl) (q:=mouth) (block:=x) (h₁:=rh) (g₁:=rg) (live:=present) (compactShape:=rfl)
    (compactHost:=homeHost) (compactGroup:=homeBlock) (keep:=chosen) (row:=here) (tag:=rfl)
    (blank:=blank rh rg) («actor»:=physical rh rg) (mem:=p_) («base»:=base) (chunk:=ch) (lane:=lane₀)
    (signed:=signed) (moved:=moved) (hit:=active_) (bits:=digitRoom) (enough:=fieldRoom) (outBits:=output)
    (space:=small) (query:=(choice 0).query) (decoded:=accounted.1) (candidates:=registered)
    (hubs:=hubWord) (fees:=tickets) (concrete:=rfl) (degree_:=deg) (cap_:=capEq) (donors_:=donorEq)
    (alignedUnits:=unitEq) (shelf:=shelf) (chipFits:=short) (grainFit:=grainRoom) (observed:=honest)
    (incoming:=incoming) (hubAt:=hub) (oneBit:=positive)
    (location:=fun h gr=>loc_ h gr) (whereAt:=located) (namesRoom:=alphabet) (count_:=congrArg (2*·) hj)
    (sourceWords:=by intro f₀ j h gr; dsimp only [registered]; rw [candidate_at_location])
    (cableRoom:=cableRoom) newWidth oldWidth
  intro f₀
  exact (accounted.2 (f₀.castLE (by decide : 4 ≤ 7))).trans (exactFields f₀)
variable (currentPorts:DescentSixParty.Chronology.DatePorts)
  (atRoom:DescentSixParty.Chronology.DatePorts.RangeRoom currentPorts B.next after_)
  (xb:Fin (2^currentPorts.venue.k)) (ny:Fin currentPorts.nodes) (hv:Fin currentPorts.operandHosts)
  (gy:Fin currentPorts.venue.groups)
  (slotAt:DescentSixParty.Chronology.DatePorts.slotAt currentPorts B.next after_ order_ atRoom xb ny hv gy=some now)
  (hostAxis:currentPorts.operandHosts=S.hostSize (age+1))
  (rhAt:rh.val=hv.val) (rgAt:rg.val=gy.val) (blockAt:(x).val=xb.val)
  (numHosts:N=Fintype.card B.next.V)
  (size_:S.hostSize age*(roster (Z).graph residual rootDep).card=(hw).placement.sparse)
  (storedName:∀j,name j=((Z).rawAtIndex T rank (j.cast numHosts)).cast size_)
  (degreeAt:venue.degree=D)
  (allFees:Fin (2^k)→Fin (hw).strip→Fin hh→Fin gg→Cell (hw).fieldBits) (atFee:tickets=allFees x)
local notation "controls_" => DateInputs.PrimaryWordsAt (B:=B) drift degree payload e previous M nextM oldLanes
  primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom ok actorMem hubWord allFees
include source slotAt hostAxis rhAt rgAt blockAt storedName degreeAt atFee in
set_option maxHeartbeats 1000000 in
private theorem registered_header_coordinates (controls:controls_) :
    ∃present:rh.val<N,
    ((hw).placement.previous (name ⟨rh.val,present⟩)).cast hostEq=carrier ∧ (finProdFinEquiv (rg,x)).cast groupEq=coarse ∧
    (s).which ((hw).placement.shape (name ⟨rh.val,present⟩))=some key ∧
    (∀incomingEdge:(grains).graph.Edge,(T).home ((grains).graph.dst incomingEdge)=term→∀j:Fin (hw).strip,
      j.val=(incomingIndex B incomingEdge).val→(tickets j rh rg).val=earlierIncoming B incomingEdge) ∧
    (hubWord rh rg=if ((T).code term).2.2.isSome then 0 else 1) ∧
    loc_ rh rg=some (Stage.home B.next.placement now.1):=by
  obtain ⟨occupied,whichAt,_,oldHostAt,oldBlockAt,_⟩:=DateInputs.named_primary_shape (B:=B)
    drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w
    fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom oldA oldNum hp whole
    currentPorts atRoom xb ny hv gy now prior slotAt source degreeAt size_
  have present : rh.val<N := by
    rw [numHosts,rhAt]
    exact occupied
  have cellEq:name ⟨rh.val,present⟩=((Z).rawAtIndex T rank ⟨hv.val,occupied⟩).cast size_:=by
    have namesEq:(⟨rh.val,present⟩:Fin N).cast numHosts=⟨hv.val,occupied⟩:=Fin.ext rhAt
    exact (storedName ⟨rh.val,present⟩).trans
      (congrArg (fun index : Fin (Fintype.card B.next.V) => ((Z).rawAtIndex T rank index).cast size_) namesEq)
  have target_:(s).which ((hw).placement.shape (name ⟨rh.val,present⟩))=some key:=by
    exact (congrArg (fun cell => (s).which ((hw).placement.shape cell)) cellEq).trans whichAt
  have host_:((hw).placement.previous (name ⟨rh.val,present⟩)).cast hostEq=carrier:=by
    apply Fin.ext
    exact (congrArg (fun cell => ((hw).placement.previous cell).val) cellEq).trans oldHostAt
  have group_:(finProdFinEquiv (rg,x)).cast groupEq=coarse:=by
    apply Fin.ext
    simp only [Fin.val_cast,finProdFinEquiv_apply_val,rgAt]
    rw [show (hw).placement.blocks=2^k from rfl]
    have blockSame:x₀.val=xb.val:=blockAt
    rw [blockSame]
    simpa only [Nat.mul_comm,Nat.add_comm] using oldBlockAt
  obtain ⟨hubAt,feeAt,whereAt⟩:=DateInputs.named_primary_fee (B:=B) drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom ok actorMem oldA oldNum hp whole currentPorts atRoom xb ny hv gy now prior
    slotAt source hostAxis hubWord allFees controls
  have hcast:rh=hv.cast hostAxis:=Fin.ext rhAt
  have gcast:rg=gy.cast atRoom.groups.symm:=Fin.ext rgAt
  have xcast:x=xb.cast (congrArg (2^·) atRoom.radix.symm):=Fin.ext blockAt
  have hw_:hubWord rh rg=if ((T).code term).2.2.isSome then 0 else 1:=by
    exact (congrArg₂ hubWord hcast gcast).trans hubAt
  have fees_:∀incomingEdge:(grains).graph.Edge,(T).home ((grains).graph.dst incomingEdge)=term→∀j:Fin (hw).strip,
      j.val=(incomingIndex B incomingEdge).val→(tickets j rh rg).val=earlierIncoming B incomingEdge:=by
    intro incomingEdge homeAt j indexAt
    have blockFees := congrArg (fun block => allFees block j rh rg) xcast
    have seatFees := congrArg₂ (allFees (xb.cast (congrArg (2^·) atRoom.radix.symm)) j) hcast gcast
    have ticketEq := ((congrArg (fun fieldFamily => fieldFamily j rh rg) atFee).trans blockFees).trans seatFees
    exact (congrArg Fin.val ticketEq).trans (feeAt incomingEdge homeAt j indexAt)
  have locationProof:loc_ rh rg=some (Stage.home B.next.placement now.1):=by
    have blockSame:x₀.cast hx=xb.cast (congrArg (2^·) atRoom.radix.symm):=Fin.ext blockAt
    have groupSame:rg.cast groupsAt=gy.cast atRoom.groups.symm:=Fin.ext rgAt
    rw [blockSame,groupSame]
    exact (location_at_archive B currentPorts after_ order_ atRoom xb ny hv gy now slotAt (rh.cast aligned) rhAt).1
  exact ⟨present,host_,group_,target_,fees_,hw_,locationProof⟩

set_option maxHeartbeats 1600000 in
include source read archive observed oldStrips atArg atNode attained matrixRead rowDegree rowCap rowBits rowPos stencilFits pop arities
  oldReads moved deg capEq donorEq unitEq signedRead oldCodec digitRoom fieldRoom output shelf chipRoom
  grainRoom positive alphabet oldWidth newWidth cableRoom slotAt hostAxis rhAt rgAt blockAt storedName degreeAt atFee in
theorem DateInputs.registered_primary_header (controls:controls_) :
    ∀f₀:Fin 4,((choice (f₀.castLE (by decide:4≤7))).amount rh rg).val=(pointer).header f₀:=by
  obtain ⟨present,host_,group_,target_,fees_,hw_,locationProof⟩ := registered_header_coordinates (B:=B)
    drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w
    fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom ok
    actorMem x₀ name hostEq groupEq hubWord tickets hx groupsAt aligned oldA oldNum hp whole now prior
    source axis oldHosts rh rg currentPorts atRoom xb ny hv gy slotAt hostAxis rhAt rgAt blockAt numHosts
    size_ storedName degreeAt allFees atFee controls
  apply DateInputs.original_primary_header (B:=B) (choice:=choice) (oldA:=oldA) (oldNum:=oldNum)
    (shape:=shape) (now:=now) (prior:=prior) (mouth:=mouth) (hp:=hp) (pin:=pin)
    (basis:=basis) (oldValues:=oldValues) (oldHosts:=oldHosts)
    (strips:=strips) (X:=X) (signed:=signed) (name:=name) (values:=values) (small:=small)
    (rh:=rh) (rg:=rg) (present:=present) (xs:=xs) (received:=received) (rootBook:=rootBook)
    (room₀:=room₀) (measured:=measured) (hdr:=hdr) (oldArgs:=oldArgs) (newArgs:=newArgs)
    (oldRoom:=oldRoom) (newRoom:=newRoom) (total:=total) (axis:=axis) (length:=length)
    (cutRoom:=cutRoom) (oldBlocks:=oldBlocks) (oldGroups:=oldGroups)
    (homeHost:=host_) (homeBlock:=group_) (target:=target_) (rowDegree:=rowDegree) (rowCap:=rowCap)
    (incoming:=fees_) (hub:=hw_) (located:=locationProof)
  all_goals assumption

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
