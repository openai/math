import OAI.Hierarchy.DescentCalendarPrimaryPrivateKeys
import OAI.Hierarchy.DescentRetainedOriginalHeaders
import OAI.Hierarchy.DescentRegisteredCarriedHeader
import OAI.Hierarchy.DescentRetainedArchivedCable
import OAI.Hierarchy.DescentCarriedOriginFields

namespace OAI
/-! Native scalar header values on true retained primary private and pin operands. -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentSixParty.Chronology DescentSixParty.ResetInput DescentKernelHistory
open DescentCompiler DescentColonies DescentGL DescentResetLocalNodes DescentOrdinaryAtomFieldRAM
open DescentPaidResidentCount.Reset DescentLocalArchiveOrder DescentSIMDLookup DescentIssuedFallbackPanel
open DescentPlainTerminal DescentChosenRouter DescentFallbackShapeTable DescentRelativeContacts
open DescentRetainedControl DescentResetHostSize Reached.NodeCells
open DescentRetainedRangeDigits
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open DescentSixParty.PackedFlow.Channels
variable {F P : Type} [Field F] {d : ℕ} {bits₀ : P→ℕ} {W : MarkedWorld F d P bits₀}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (a : Archive W) (early : Local a.bit)
local notation "A" => cap.placement
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "dim" => (T).commonDepth
local notation "wide" => S.groupWidth k tail i+k
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "ix" u:arg => StarKeys.filled W.graph (A).pos (A).block digits u
local notation "oldId" => (A).site cap.vertex cap.valid.coordinates
local notation "small" => b.frame.enough.trans (Nat.sub_le ..)
local notation "roster" => ClosedReset.Recorded.old_roster (reset:=b)
local notation "safe" => (roster).2.2.2.2.2.choose
local notation "Node" u:arg => (a.bit.recipe u).Node
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSIMDLookup DescentResetPublicOperandBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.BorderVNP.Crossing DescentResetOperandSetup DescentDenseHostOrder
variable {machine : PhysicalReset} {atlas : machine.Atlas} {roots : machine.RootInputs} (menu : OperandMenu atlas roots)
local notation "chart" => machine.successor.setup
local notation "ret" => (chart).retained
variable (total:(ret).high+(ret).low=wide) (axis:(ret).cut=dim)
  (blocks:(ret).blocks=2^k) (groups:(ret).groups=S.groupCount i)
  (size:2^((ret).high+(ret).low)=(ret).groups*(ret).blocks) (fits:(ret).cut≤(ret).high+(ret).low)
  (L:DescentGL.Layout ((ret).high+(ret).low)) (won:HEq L b.frame.basis)
  (room:Fintype.card cap.V≤(ret).hosts)
   (nodeRoom:∀u,Fintype.card (Node u)≤(ret).previousNodes)
local notation "hl" => congrArg (fun k:ℕ=>2^k) axis
local notation "ll" => congrArg (fun k:ℕ=>2^k) (congrArg₂ Nat.sub total axis)
local notation "coords" => finCongr ll
local notation "name" => cap.vertex.trans (Fin.castLEEmb room)
variable {R:ℕ} (hp : 0<p) (whole : p∣(Z).unit) (one:1≤R) (posUnit:0<(Z).unit)
  (widthBound:max 1 (max (Z).width (C*(Z).width))≤R) (sh:DescentBundleHistory.WorldShape p R a.bit)
local notation "nextBit" => (resetArchive b p hp whole a).bit
variable (xx : NodeOrder.All nextBit) (yy : NodeOrder.All a.bit)
  (origin : resetOrigin b hp whole a xx=Sum.inl yy)
local notation "term" => (T).home yy.1
local notation "u₀" => b.frame.host.symm ((T).code term).1
local notation "carrier" => name u₀
local notation "hi" => (Z).rootBlock T (.inr term)
local notation "coarse" => (hi).cast (hl).symm
local notation "source" lo:arg => (rearrange b.frame.basis).symm (join small hi lo)
local notation "rail" lo:arg => (rearrange L).symm (join fits coarse ((coords).symm lo))
local notation "pos" lo:arg => (finProdFinEquiv.symm (Fin.cast size (rail lo)):Fin (ret).groups×Fin (ret).blocks)
local notation "census" lo:arg => ∑u:W.graph.Site,if ((A).pos u).2=u₀ ∧ ix u=source lo then Fintype.card (Node u) else 0

local notation "after_" => (resetArchive b p hp whole a).bit
local notation "names" => resetOrigin b hp whole a
local notation "order_" => DescentLocalArchiveOrder.reset b p hp whole a early
variable (which : (chart).seven.control.Targets) (window : (chart).seven.Packets) (shape : Fin (chart).placement.shapes)
variable (input : (ret).Values)
local notation "strips" => (fun j=>blockValues fits ((ret).before size input j) L)
local notation "wrd" => (ret).site strips carrier coarse
variable (word : Block (wide-dim)→ℕ)
local notation "code" => cell ((Z).k-dim) (shortName dim ((T).code term)).2
variable (owns : ownerAt chart which window shape carrier coarse=(fun i=>decide (word (coords i)/2=code)))
variable (compared : priorAt chart window carrier coarse=(fun i j=>decide (source (coords i)<source (coords j))))
variable (stencil : ∀lo,word lo/2=DescentPlainTerminal.Suffix.Stencil.shapeCode (wide-dim)
  (2^(Z).n) (DescentPlainTerminal.Suffix.fieldsRelative dim (ClosedReset.Recorded.originalCell (reset:=b) u₀ (source lo))))
variable (counts : ∀lo,(ret).originalCount wrd ((coords).symm lo)=∑u:W.graph.Site,
    if DescentPaidResidentCount.occupies (A) (Equiv.refl _) name carrier ((pos lo).1.cast groups)
      ((pos lo).2.cast blocks) u then Fintype.card (Node u) else 0)


open DescentRetainedPrivateSlotBook DescentBundleHistory DescentLocalPrivateNames DescentOperandStateBanks
open DescentRetainedResetPinPointer DescentPackedResetDonors DescentResetTrunks DescentRotorWindowArchive
open DescentSixParty.ClosedReset
local notation "D₀" => reached b hp one posUnit whole widthBound a sh xx yy origin
local notation "split_" => sh.granular b.count (z*G.b) b.fit hp (b.unit ▸ posUnit) (b.unit ▸ whole)
local notation "fit_" => ((Nat.div_mul_cancel whole).symm : b.reset.unit=b.reset.unit/p*p)
local notation "installed" => reentryWorldShape split_ b.reset b.terminals (DescentOrderedReset.grains W b.count b.order)
  _ hp fit_ (resetMenu b) one widthBound
local notation "sh₁" => WorldShape.follow hp posUnit whole b.reblock b.cuts installed
local notation "r" => ((sh₁).sites xx.1).recipe hp
local notation "fibre" => DescentNamedContact.Fibre (T).home term
local notation "src" u:arg => (sh.sites (u:fibre).val).recipe hp
local notation "oldNode" u:arg n:arg => (early (u:fibre).val n).castLE (nodeRoom (u:fibre).val)
local notation "dof" u:arg => (coords).symm (low («c»:=dim) (rearrange b.frame.basis (ix (u:fibre).val)))
local notation "ord" => physicalDonorOrder b.frame term ret coords
local notation "take_" => ownerAt chart which window shape carrier coarse
local notation "prior_" => priorAt chart window carrier coarse
local notation "routed" => (ret).routedWord take_ prior_ wrd
local notation "ownerOf" q:arg => ((D₀).slots q).1
local notation "slotOf" q:arg => ((D₀).slots q).2

variable (oldArgs : ∀(u:fibre) n,(src u).arity n≤(ret).previousArgs)
  (nextRoom : Fintype.card ((after_).recipe xx.1).Node≤(ret).nodes)
  (newArgs : ∀n,(r).arity n≤(ret).args)
local notation "originalAddr" u:arg => reached_mouth (src u) ((early (u:fibre).val).toEmbedding.trans (Fin.castLEEmb (nodeRoom (u:fibre).val))) (oldArgs u)
local notation "newAddr" => reached_mouth r ((order_ xx.1).toEmbedding.trans (Fin.castLEEmb nextRoom)) newArgs
local notation "donors" => calendar_donor_index (b:=b) (a:=a) (yy:=yy) («chart»:=(chart)) (total:=total) (axis:=axis)
local notation "current" q:arg => (finProdFinEquiv.symm (newAddr q):Fin (ret).nodes×Fin (ret).args)
local notation "a₀" u:arg s:arg => (s:Slot (src u)).2.castLE (oldArgs u (s:Slot (src u)).1)
local notation "atMouth" u:arg s:arg f:arg => (ret).entry wrd (donors u) (oldNode u (s:Slot (src u)).1) ((ret).operandField f (a₀ u s))
variable (arityWords : ∀(u:fibre) n,((ret).entry wrd (donors u) (oldNode u n) (ret).arityField).val=(src u).arity n)
variable (pin:P→ℕ)
local notation "oldPtr" u:arg s:arg => Reached.argumentPointer cap a.bit early sh hp pin (ret).previousArgs ⟨(u:fibre).val,(s:Slot (src u)).1⟩ (s:Slot (src u)).2.val
variable (headerWords : ∀(u:fibre)(s:Slot (src u))(f:Fin 4),(atMouth u s (f.castLE (by decide:4≤7))).val=(oldPtr u s).header f)
variable (aliasRoom:(ret).previousNodes*(ret).previousArgs≤2^(ret).bits)
local notation "key" => (D₀).key ((donors).trans (ord).toEmbedding) (fun u=>originalAddr u) aliasRoom


variable {U:ℕ} (namesAt:Fin U→Fin (chart).placement.sparse)
local notation "cfg" => publicOperands atlas roots menu.payload
variable (data:(cfg).Data machine.successor.middle.rotorBits) (mouth:Fin (cfg).mouths)
local notation "regs" => (cfg).reg data
local notation "loc" => (finProdFinEquiv.symm mouth : Fin (cfg).args×Fin (cfg).nodes)
local notation "rot" width:arg f:arg => ((cfg).rotor.flatReg atlas.board (cfg).multiplicity (cfg).grain (cfg).split
  (loc).2.val (loc).1.val f regs : Cell width)
local notation "public_" width:arg f:arg => (cfg).column atlas.board width f mouth data
variable (hostEq:(chart).placement.oldHosts=(ret).hosts) (groupEq:(chart).placement.groups*(chart).placement.blocks=(ret).grouped)
  (bank:(chart).Sources) (whichEq:bank.which=which) (primaryEq:bank.primary=menu.keep)
  (q:Slot r) (block:Fin (chart).placement.blocks) (h₁:Fin (chart).placement.newHosts) (g₁:Fin (chart).placement.groups)
  (live:h₁.val<U)
local notation "lookup_" => namesAt ⟨h₁.val,live⟩
local notation "node₁" => (current q).1
local notation "arg₁" => (current q).2
local notation "shp₁" => (chart).placement.shape lookup_
variable (compactShape:shp₁=shape) (compactHost:((chart).placement.previous lookup_).cast hostEq=carrier)
  (compactGroup:(finProdFinEquiv (g₁,block)).cast groupEq=coarse) (keep:menu.keep shape=true)
local notation "Y" => (chart).assignedDigits hostEq groupEq bank.which window strips
local notation "index_" t:arg f:arg => (ret).outputID t f arg₁ node₁
local notation "kept_" t:arg f:arg => ((DescentRetainedTargetPlacement.Chart.compact (chart).placement (chart).seven.batch
  menu.keep namesAt Y (index_ t f) block h₁ g₁).val:Cell (chart).fieldBits)
variable (row:(chart).cable.Input) (tag:(chart).cable.header row 0=kept_ 0 0)
  (blank:((cfg).oldConfig.header ((cfg).basic data) 0).val=0→(regs 1).val=0)
  (actor:∀hu:h₁.val<U,((cfg).oldConfig.header ((cfg).basic data) 0).val≠0→
    (regs 3).val=((chart).placement.shape (namesAt ⟨h₁.val,hu⟩)).val)
local notation "qry" => (chart).cable.query row
local notation "rq" => rot (chart).queryBits 0
local notation "pq" => public_ (chart).queryBits none
local notation "charge" f:arg => (chart).cable.priceField f row
local notation "rotorValue" f:arg => rot (chart).fieldBits (f).succ
local notation "publicValue" f:arg => public_ (chart).fieldBits (some f)
local notation "posted" f:arg => (((kept_ 1 f).val+(charge f).val+(rotorValue f).val+(publicValue f).val:ℕ) : Cell (chart).fieldBits)


local notation "ordinal" => OperandMenu.queryDigit (a:=machine) qry rq pq

open DescentPackedZip ProtocolRAM DescentOperandCandidateLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure

variable {bw:ℕ} (mem:Memory bw) (base:ℕ) (chunk:Fin (chunks (chart).placement.groups (chart).lanes)) (lane:Fin (chart).lanes)
  (signed:Fin (chart).strip→Fin (chart).placement.oldHosts→Fin ((chart).placement.groups*(chart).placement.blocks)→Cell (chart).signedBits)
  (moved:(chart).Moved base bank namesAt mem Y signed)
  (hit:chunk.val*(chart).lanes+lane.val=g₁.val) (bits:(ret).bits*(chart).lanes≤bw)
  (enough:(ret).bits≤(chart).fieldBits) (outBits:(ret).bits≤ machine.successor.receiver.valueBits)
  {J:ℕ} (space:J<2^(chart).queryBits) (query:Fin (chart).placement.newHosts→Fin (chart).placement.groups→Option (Fin J))
  (decoded:DescentOperandCandidateLookup.code space (query h₁ g₁)=ordinal)
  (candidates:Fin 7→Fin J→Fin (chart).placement.newHosts→Fin (chart).placement.groups→Cell machine.successor.receiver.valueBits)
local notation "f₇" f:arg => (f:Fin 4).castLE (by decide:4≤7)
local notation "actual" f:arg => (((posted (f₇ f)).val:Cell machine.successor.receiver.valueBits).val+
  (DescentOperandCandidateLookup.selected query (candidates (f₇ f)) h₁ g₁).val)
local notation "nextPtr" => Reached.argumentPointer b.next after_ order_ sh₁ hp pin (ret).args ⟨xx.1,q.1⟩ q.2.val
local notation "previousPtr" => oldPtr (ownerOf q) (slotOf q)
local notation "old_" f:arg => atMouth (ownerOf q) (slotOf q) (f₇ f)
open private calendar_registered_slots calendar_aligned_slot from OAI.Hierarchy.DescentCalendarPrimaryPrivateKeys
set_option maxHeartbeats 650000 in
include won owns compared stencil counts arityWords headerWords compactShape compactHost compactGroup whichEq
  keep tag blank actor moved hit bits enough outBits primaryEq decoded in
theorem calendar_retained_pin_header (socket:Attached W.graph (ownerOf q).val) (fine:ℕ)
    (portWidth:(fine+1)*p≤bits₀ socket.val)
    (oldSource:(src (ownerOf q)).operand (slotOf q).1 (slotOf q).2=.inl ⟨.inr socket,fine,portWidth⟩) :
    ∀f:Fin 4,actual f=(nextPtr).header f:=by
  have origin_q:=reached_slot_origin b hp one posUnit whole widthBound a sh xx yy origin q
  obtain ⟨take,count,used,position,argument⟩ := calendar_registered_slots b a early chart total axis
    blocks groups size fits L won room nodeRoom hp whole one posUnit widthBound sh xx yy origin
    which window shape input word owns compared stencil counts oldArgs nextRoom newArgs arityWords q
  have rank := calendar_aligned_slot b a chart total axis room yy window compared
  have previous:=Reached.argumentPointer_pin cap a.bit early sh hp pin (ret).previousArgs
    (ownerOf q).val (slotOf q).1 (slotOf q).2 socket fine portWidth oldSource
  have final_:=closed_pin b hp one posUnit whole widthBound a sh order_ pin (ret).args
    ⟨xx.1,q.1⟩ ⟨(ownerOf q).val,(slotOf q).1⟩ origin_q.1 (slotOf q).2 socket fine portWidth oldSource
  rw [origin_q.2] at final_
  rw [final_]
  exact OperandMenu.retained_archived_pin (menu:=menu) («name»:=namesAt) (x:=data) (i:=mouth) (hostEq:=hostEq) (groupEq:=groupEq)
    (packet:=window) («strips»:=strips) (owner:=bank) (block:=block) (arg:=arg₁) (node:=node₁)
    (host:=h₁) (g:=g₁) (row:=row) (head:=tag) (blank:=blank) (physical:=actor) (mem:=mem) (base:=base)
    (chunk:=chunk) (lane:=lane) (live:=live) (primary:=compactShape.symm ▸ keep) (primaryBank:=primaryEq)
    (signed:=signed) (moved:=moved) (hit:=hit) (room:=bits) (enough:=enough) (output:=outBits)
    (order:=ord) (rank:=by simp only [compactHost,compactGroup]; exact rank)
    (d:=donors (ownerOf q)) («oldNode»:=oldNode (ownerOf q) (slotOf q).1) (oldArg:=a₀ (ownerOf q) (slotOf q))
    (take:=by simp only [whichEq,compactShape,compactHost,compactGroup]; exact take)
    (exists_:=by simp only [compactHost,compactGroup]; exact count)
    (le:=by simp only [compactHost,compactGroup]; exact used)
    (position:=by simp only [whichEq,compactHost,compactGroup,compactShape]; exact position)
    (argument:=argument) (space:=space) (q₀:=query) (decoded:=decoded) (candidates:=candidates)
    (pin socket.val) fine (by intro f;simp only [compactHost,compactGroup,←previous]; exact headerWords (ownerOf q) (slotOf q) f)

set_option maxHeartbeats 650000 in
include aliasRoom won owns compared stencil counts arityWords headerWords compactShape compactHost compactGroup whichEq
  keep tag blank actor moved hit bits enough outBits primaryEq decoded in
theorem calendar_retained_private_header (oldName:ℕ) (private_:previousPtr=Pointer.privateWord oldName)
    (outputRoom:(ret).nodes*(ret).args≤2^(ret).bits) :
    ∀f:Fin 4,actual f=(nextPtr).header f:=by
  have origin_q:=reached_slot_origin b hp one posUnit whole widthBound a sh xx yy origin q
  obtain ⟨take,count,used,position,argument⟩ := calendar_registered_slots b a early chart total axis
    blocks groups size fits L won room nodeRoom hp whole one posUnit widthBound sh xx yy origin
    which window shape input word owns compared stencil counts oldArgs nextRoom newArgs arityWords q
  have rank := calendar_aligned_slot b a chart total axis room yy window compared
  have ranges := calendar_primary_private_keys b a early chart total axis blocks groups size fits L won room
    nodeRoom hp whole one posUnit widthBound sh xx yy origin which window shape input word owns compared
    stencil counts oldArgs nextRoom newArgs arityWords pin headerWords aliasRoom
  obtain ⟨w,_,keyAt,renewed⟩:=calendar_primary_private_pointer (b:=b) (a:=a) (early:=early) («chart»:=(chart))
    (total:=total) (axis:=axis) (size:=size) (fits:=fits) (L:=L) (room:=room) (nodeRoom:=nodeRoom)
    (hp:=hp) (whole:=whole) (one:=one) (posUnit:=posUnit) (widthBound:=widthBound) (sh:=sh) (xx:=xx) (yy:=yy)
    (origin:=origin) (input:=input) (oldArgs:=oldArgs) (nextRoom:=nextRoom) (newArgs:=newArgs)
    (pin:=pin) (headerWords:=headerWords) (aliasRoom:=aliasRoom) q oldName private_
  intro indexField
  refine Eq.trans ?_ (congrArg (fun ptr : Pointer => ptr.header indexField) renewed.symm)
  exact OperandMenu.retained_archived_private (menu:=menu) («name»:=namesAt) (x:=data) (i:=mouth) (hostEq:=hostEq) (groupEq:=groupEq)
    (packet:=window) («strips»:=strips) (owner:=bank) (block:=block) (arg:=arg₁) (node:=node₁)
    (host:=h₁) (g:=g₁) (row:=row) (head:=tag) (blank:=blank) (physical:=actor) (mem:=mem) (base:=base)
    (chunk:=chunk) (lane:=lane) (live:=live) (primary:=compactShape.symm ▸ keep) (primaryBank:=primaryEq)
    (signed:=signed) (moved:=moved) (hit:=hit) (room:=bits) (enough:=enough) (output:=outBits)
    (order:=ord) (rank:=by simp only [compactHost,compactGroup]; exact rank)
    (d:=donors (ownerOf q)) («oldNode»:=oldNode (ownerOf q) (slotOf q).1) (oldArg:=a₀ (ownerOf q) (slotOf q))
    (take:=by simp only [whichEq,compactShape,compactHost,compactGroup]; exact take)
    (exists_:=by simp only [compactHost,compactGroup]; exact count)
    (le:=by simp only [compactHost,compactGroup]; exact used)
    (position:=by simp only [whichEq,compactHost,compactGroup,compactShape]; exact position)
    (argument:=argument) (space:=space) (q₀:=query) (decoded:=decoded) (candidates:=candidates)
    r newAddr key w oldName
    (by intro f;simp only [compactHost,compactGroup,←private_]; exact headerWords (ownerOf q) (slotOf q) f)
    (by simp only [whichEq,compactShape,compactHost,compactGroup]; exact ranges.1)
    (by simp only [whichEq,compactShape,compactHost,compactGroup]; exact ranges.2)
    (by simp only [compactHost,compactGroup]; exact keyAt) ((firstAlias r newAddr w).isLt.trans_le outputRoom) indexField

open DescentSharedCableNames DescentStageEdgeReceipt DescentOperandPriorIncidence DescentResetOperandComponents
open DescentResetOperandSlices DescentNextSignedWindow.Native DescentSixParty.ClosedReset.Window DescentDatedAddressBook.ResetOutput
local notation "peerNames" => DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank
  ((Function.Embedding.refl (Fin (S.groupCount i))).trans Fin.valEmbedding) (cap.vertex.trans Fin.valEmbedding))
local notation "home_" u:arg => Stage.home (A) (u:fibre).val
local notation "sub_" u:arg => subcell (c:=dim) digits b.frame.basis (home_ u)
local notation "prevSign" => cap.order.trans Fin.valEmbedding
local notation "site_" => Stage.Host (Fin (S.groupCount (i+1))) b.next.V k
local notation "anc" => ownerOf q
local notation "as_" => slotOf q
local notation "sel_" => donors (anc)
local notation "M" => Fin (chart).placement.newHosts→Fin (chart).placement.groups→Cell (chart).fieldBits
variable (hubs:M) (fees:Fin (chart).strip→M)
  (concrete:row=(chart).carriedRow bank namesAt Y signed block arg₁ node₁ hubs fees h₁ g₁)
  (degree_:(chart).cable.degree=(A).degree) (cap_:(chart).cable.cap=(A).cap)
  (donors_:(chart).cable.donors=2^(wide-dim)) (alignedUnits:(chart).cable.units=(Z).unit/p)
  (shelf:(ret).donors<2^(ret).bits) (signFits:(chart).signedBits≤(chart).fieldBits)
  (grainFit:(chart).cable.units*b.next.placement.cap≤2^(chart).cable.fieldBits)
local notation "sl" j:arg => (j:Fin (2*(chart).oldCap)).cast (congrArg (2*·) cap_)
local notation "here_" => (chart).placement.previous lookup_
local notation "prevGroup" => finProdFinEquiv (g₁,block)
local notation "signed₀" d:arg j:arg => signed (finProdFinEquiv (d,j)) here_ prevGroup
variable (chipFits : ∀j : Fin (2*(chart).oldCap),(signed₀ (sel_) j).val<2^(chart).fieldBits)
variable (observed:∀j:Fin (2*(chart).oldCap),HEq
  (((signed₀ (sel_) j).val:Cell (DescentSignedCableCodec.width (chart).oldDegree (chart).oldCap)))
  (DescentSignedCableCodec.encode (Stage.signedPanel (A) prevSign S cap.valid peerNames (home_ (anc)) (sl j))))
variable (incoming:∀e:(W.granular b.count (z*G.b) b.fit).graph.Edge,
  (T).home ((W.granular b.count (z*G.b) b.fit).graph.dst e)=term→∀j:Fin (chart).strip,
    j.val=(incomingIndex b e).val→(fees j h₁ g₁).val=earlierIncoming b e)
  (hubAt:hubs h₁ g₁=if ((T).code term).2.2.isSome then 0 else 1) (oneBit:1<2^(chart).fieldBits)
  (location:Fin (chart).placement.newHosts→Fin (chart).placement.groups→Option site_)
  (whereAt:location h₁ g₁=some (Stage.home b.next.placement xx.1))
  (namesRoom:max (b.next.placement.degree+1) (b.next.placement.cap+1)≤2^machine.successor.receiver.signedBits)
  (count_:J=2*totalLocal b)
  (sourceWords:∀f:Fin 4,∀j h g,candidates (f₇ f) j h g=
    nativeCandidateField machine.successor.receiver.signedBits machine.successor.receiver.valueBits (f₇ f)
      ((location h g).bind (fun v=>candidateRows b (fieldNames b) v (j.cast count_))))
  (valueRoom:∀f:Fin 4,(nextPtr).header f<2^machine.successor.receiver.valueBits)

set_option maxHeartbeats 1250000 in
include won owns compared stencil counts arityWords headerWords whichEq compactShape compactHost compactGroup keep tag blank
  actor moved hit bits enough outBits primaryEq decoded concrete degree_ cap_ donors_ alignedUnits shelf chipFits grainFit
  observed incoming hubAt oneBit whereAt namesRoom count_ sourceWords valueRoom in
omit tag outBits in
theorem calendar_retained_cable_header (edge:Incident W.graph (anc).val) (fine:ℕ)
    (valid:(fine+1)*p≤W.graph.width edge.val)
    (oldSource:(src (anc)).operand (as_).1 (as_).2=.inl ⟨.inl edge,fine,valid⟩) :
    ∀f:Fin 4,actual f=(nextPtr).header f:=by
  subst J
  have origin_q:=reached_slot_origin b hp one posUnit whole widthBound a sh xx yy origin q
  obtain ⟨take,count,used,position,argument⟩ := calendar_registered_slots b a early chart total axis blocks groups size fits L won room nodeRoom hp whole one posUnit widthBound sh xx yy origin which window shape input word owns compared stencil counts oldArgs nextRoom newArgs arityWords q
  have rank := calendar_aligned_slot b a chart total axis room yy window compared
  let oldLabel:=Reached.firstCable cap hp (anc).val edge fine valid
  have oldPtrAt:previousPtr=oldLabel:=Reached.argumentPointer_cable cap a.bit early sh hp pin (ret).previousArgs
    (anc).val (as_).1 (as_).2 edge fine valid oldSource
  have kind:(atMouth (anc) (as_) (0:Fin 7)).val=1:=by
    have hd:=headerWords (anc) (as_) 0
    rw [oldPtrAt] at hd
    exact hd
  have ⟨queryAt,priced⟩:=OperandMenu.retained_archived_cable (menu:=menu) («name»:=namesAt) (x:=data) (i:=mouth) (hostEq:=hostEq) (groupEq:=groupEq)
    (packet:=window) («strips»:=strips) (owner:=bank) (block:=block) (arg:=arg₁) (node:=node₁)
    (host:=h₁) (g:=g₁) (row:=row) (blank:=blank) (physical:=actor) (mem:=mem) (base:=base)
    (chunk:=chunk) (lane:=lane) (live:=live) (primary:=compactShape.symm ▸ keep) (primaryBank:=primaryEq)
    (signed:=signed) (moved:=moved) (hit:=hit) (room:=bits) (enough:=enough)
    (order:=ord) (rank:=by simp only [compactHost,compactGroup]; exact rank)
    (d:=donors (ownerOf q)) («oldNode»:=oldNode (ownerOf q) (slotOf q).1) (oldArg:=a₀ (ownerOf q) (slotOf q))
    (take:=by simp only [whichEq,compactShape,compactHost,compactGroup]; exact take)
    (exists_:=by simp only [compactHost,compactGroup]; exact count)
    (le:=by simp only [compactHost,compactGroup]; exact used)
    (position:=by simp only [whichEq,compactHost,compactGroup,compactShape]; exact position)
    (argument:=argument) (space:=space) (q₀:=query) (decoded:=decoded) (candidates:=candidates)
    (0:Cell 1) (by simp only [compactHost,compactGroup]; exact kind)
  have movedFields:=DescentRetainedRangeDigits.carried_origin_fields (C:=chart) (X:=window) (panels:=strips)
    (s:=bank) («name»:=namesAt) (host:=hostEq) (group:=groupEq) (signed:=signed)
    (block:=block) (rack:=h₁) (group_:=g₁) (alive:=live) (hub:=hubs) (fee:=fees)
    (by rw [primaryEq,compactShape];exact keep) ord (by simp only [compactHost,compactGroup]; exact rank)
    (sel_) (oldNode (anc) (as_).1) (a₀ (anc) (as_))
    (by simp only [whichEq,compactShape,compactHost,compactGroup]; exact take)
    (by simp only [compactHost,compactGroup]; exact count) (by simp only [compactHost,compactGroup]; exact used)
    node₁ (by simp only [whichEq,compactHost,compactGroup,compactShape]; exact position) arg₁ argument shelf enough
  have donEq:(sel_).val=(sub_ (anc)).val:=rfl
  have srcDonor:(sub_ (anc)).cast donors_.symm=(sel_):=Fin.ext donEq.symm
  have header (f:Fin 4):((chart).cable.header row f).val=(previousPtr).header f:=by
    apply (congrArg (fun data : (chart).cable.Input => ((chart).cable.header data f).val) concrete).trans
    apply (movedFields.1 f).trans
    simp only [compactHost,compactGroup]
    exact headerWords (anc) (as_) f
  have donorRead:((chart).cable.donorCell row).val=(sub_ (anc)).val+1:=by
    exact (congrArg (fun data : (chart).cable.Input => ((chart).cable.donorCell data).val) concrete).trans
      (movedFields.2.trans (congrArg (·+1) donEq))
  have faces (j:Fin (2*(chart).oldCap)):=DescentRetainedRangeDigits.carried_faces_wide (C:=chart) (X:=window) (panels:=strips)
    (s:=bank) («name»:=namesAt) (host:=hostEq) (group:=groupEq) (signed:=signed)
    (block:=block) (rack:=h₁) (group_:=g₁) (alive:=live) (hub:=hubs) (fee:=fees)
    node₁ arg₁ (sel_) j (chipFits j)
  let j₀:=originalCableGrain b hp posUnit whole edge fine valid
  let sign:=originFace (W:=W) (anc).val edge
  let sn:=Stage.signed (A) prevSign S cap.valid (home_ (anc)).1 (home_ (anc)).2
    (originPort (A) (anc).val edge j₀)
  let s₀:=sn.cast (congrArg (2*·) cap_.symm)
  let e₀:=oldEndOf b (⟨edge.val,j₀⟩:Stage.Grain (A))
  have endAt(signAt:sign=true):(T).home ((W.granular b.count (z*G.b) b.fit).graph.dst e₀)=term:=by
    have srcNe:W.graph.src edge.val≠(anc).val:=of_decide_eq_true signAt
    exact (congrArg (T).home (edge.property.resolve_left srcNe)).trans (anc).property
  let oldFields:=fun j:Fin 7=>((atMouth (anc) (as_) j).val:Cell (chart).fieldBits)
  have oldHeader (f:Fin 4):(oldFields (f₇ f)).val=(previousPtr).header f:=by
    change (((atMouth (anc) (as_) (f₇ f)).val:Cell (chart).fieldBits)).val=_
    rw [Fin.val_cast_of_lt ((atMouth (anc) (as_) (f₇ f)).isLt.trans_le (Nat.pow_le_pow_right (by decide) enough))]
    exact headerWords (anc) (as_) f
  have home:=reached_node_site b hp whole a ⟨xx.1,q.1⟩
  rw [origin_q.1] at home
  intro f
  rw [priced f]
  have result:=registered_carried_header b hp one posUnit whole widthBound a sh early order_ pin (ret).previousArgs (ret).args
    ⟨xx.1,q.1⟩ ⟨(anc).val,(as_).1⟩ origin_q.1 (as_).2 edge fine valid oldSource (chart).cable row
    degree_ cap_ donors_ alignedUnits header donorRead (by
      intro j
      have eqRow := congrArg₂ (fun (d : (chart).cable.Donor) (x : (chart).cable.Input) =>
        (chart).cable.row x d j) srcDonor concrete
      exact (heq_of_eq (eqRow.trans (faces j).1)).trans (observed j)) space (by
      intro j incomingAt
      have eqTicket := congrArg₂ (fun (d : (chart).cable.Donor) (x : (chart).cable.Input) =>
        (chart).cable.ticket x d s₀) srcDonor concrete
      apply (eqTicket.trans (faces s₀).2.1).trans
      apply incoming e₀ (endAt incomingAt)
      apply Eq.trans _ (congrArg Fin.val (original_incoming_slot b edge j₀ incomingAt).symm)
      change (finProdFinEquiv (sel_,s₀)).val=(finProdFinEquiv (sub_ (anc),sn)).val
      simp only [finProdFinEquiv_apply_val,s₀,Fin.val_cast,donEq]
      exact congrArg (fun n : ℕ => sn.val+2*n*(sub_ (anc)).val) cap_)
    (by
      intro j incomingAt
      have eqHub := (congrArg (fun x : (chart).cable.Input => (chart).cable.hubCell x) concrete).trans (faces s₀).2.2
      exact (congrArg (fun h : Cell (chart).fieldBits => decide (h.val=1)) eqHub).trans
        ((original_hub_bit b term _ oneBit hubAt).trans (congrArg (T).hub (endAt incomingAt).symm)))
    grainFit oldFields (0:Cell 1) oldHeader machine.successor.receiver.signedBits machine.successor.receiver.valueBits
    namesRoom rfl space location query h₁ g₁ (whereAt.trans (congrArg (fun v=>some (Stage.home b.next.placement v)) home.symm))
    queryAt f (origin_q.2.symm ▸ valueRoom f)
  rw [origin_q.2] at result
  simp only [compactHost,compactGroup,DescentOperandCandidateLookup.selected,sourceWords,Fin.cast_refl] at result ⊢
  exact result

include nodeRoom oldArgs in
/-- Classify the reached operand, retaining the emitted cable address in the edge case. -/
private theorem original_operand_cases {result : Prop}
    (privateAt : ∀ serial, previousPtr = Pointer.privateWord serial → result)
    (pinAt : ∀ (socket : Attached W.graph (anc).val) (fine : ℕ)
      (valid : (fine+1)*p ≤ bits₀ socket.val),
      (src (anc)).operand (as_).1 (as_).2 = .inl ⟨.inr socket,fine,valid⟩ → result)
    (cableAt : ∀ (edge : Incident W.graph (anc).val) (fine : ℕ)
      (valid : (fine+1)*p ≤ W.graph.width edge.val),
      (src (anc)).operand (as_).1 (as_).2 = .inl ⟨.inl edge,fine,valid⟩ →
      (∃ peer serial part, nextPtr = Pointer.cable peer serial part) → result) : result := by
  cases original:(src (anc)).operand (as_).1 (as_).2 with
  | inr label =>
    let hidden : (src (anc)).UsedWord := ⟨label,⟨(as_).1,(as_).2,original⟩⟩
    exact privateAt _ (Reached.argumentPointer_private cap a.bit early sh hp pin (ret).previousArgs (anc).val
      (as_).1 (as_).2 (originalAddr (anc))
      (fun j => (reached_mouth_number (src (anc)) ((early (anc).val).toEmbedding.trans
        (Fin.castLEEmb (nodeRoom (anc).val))) (oldArgs (anc)) j).symm) hidden original)
  | inl ref =>
    obtain ⟨edge|socket,fine,valid⟩ := ref
    · let grain := originalCableGrain b hp posUnit whole edge fine valid
      let incomingGrain := oldEndOf b (⟨edge.val,grain⟩ : Stage.Grain (A))
      have origin_q := reached_slot_origin b hp one posUnit whole widthBound a sh xx yy origin q
      have found := posted_cable b hp one posUnit whole widthBound a sh order_ pin (ret).args
        ⟨xx.1,q.1⟩ ⟨(anc).val,(as_).1⟩ origin_q.1 (as_).2 edge fine valid original incomingGrain.2 rfl
      rw [origin_q.2] at found
      exact cableAt edge fine valid original ⟨_,_,_,found⟩
    · exact pinAt socket fine valid original

variable (cableRoom : ∀peer serial part,nextPtr=Pointer.cable peer serial part →
  ∀f : Fin 4,(nextPtr).header f<2^machine.successor.receiver.valueBits)

set_option maxHeartbeats 1200000 in
include won owns compared stencil counts arityWords headerWords whichEq compactShape compactHost compactGroup keep tag blank
  actor moved hit bits enough outBits primaryEq decoded concrete degree_ cap_ donors_ alignedUnits shelf chipFits grainFit
  observed incoming hubAt oneBit whereAt namesRoom count_ sourceWords cableRoom in
theorem calendar_retained_header_at_cable (outputRoom:(ret).nodes*(ret).args≤2^(ret).bits)
    (oldWidth:(ret).previousNodes*(ret).previousArgs≤2^(ret).bits) :
    ∀f:Fin 4,actual f=(nextPtr).header f:=by
  apply (original_operand_cases (b:=b)) (a:=a) (early:=early) (xx:=xx) (yy:=yy)
    (hp:=hp) (whole:=whole) (one:=one) (posUnit:=posUnit) (widthBound:=widthBound)
    (sh:=sh) (origin:=origin) (pin:=pin) (q:=q) (nodeRoom:=nodeRoom) (oldArgs:=oldArgs)
    (result:=∀f:Fin 4,actual f=(nextPtr).header f)
  · intro oldName previous
    apply (calendar_retained_private_header (b:=b)) (a:=a) (early:=early) (menu:=menu) (L:=L) (xx:=xx) (yy:=yy) (sh:=sh)
        (which:=which) (window:=window) (shape:=shape) (input:=input) (word:=word) (pin:=pin)
        (namesAt:=namesAt) (data:=data) (mouth:=mouth) (bank:=bank) (q:=q) (block:=block)
        (h₁:=h₁) (g₁:=g₁) (row:=row) (mem:=mem) (base:=base) (chunk:=chunk) (lane:=lane)
        (signed:=signed) (query:=query) (candidates:=candidates) (oldName:=oldName) (private_:=previous)
        (aliasRoom:=oldWidth) (outputRoom:=outputRoom)
    all_goals assumption
  · intro socket fine valid oldSource
    apply (calendar_retained_pin_header (b:=b)) (a:=a) (early:=early) (menu:=menu) (L:=L) (xx:=xx) (yy:=yy) (sh:=sh)
        (which:=which) (window:=window) (shape:=shape) (input:=input) (word:=word) (pin:=pin)
        (namesAt:=namesAt) (data:=data) (mouth:=mouth) (bank:=bank) (q:=q) (block:=block)
        (h₁:=h₁) (g₁:=g₁) (row:=row) (mem:=mem) (base:=base) (chunk:=chunk) (lane:=lane)
        (signed:=signed) (query:=query) (candidates:=candidates) (socket:=socket) (fine:=fine) (portWidth:=valid) (oldSource:=oldSource)
    all_goals assumption
  · intro edge fine valid oldSource cable
    obtain ⟨peer,serial,part,found⟩ := cable
    apply (calendar_retained_cable_header (b:=b)) (a:=a) (early:=early) (menu:=menu) (L:=L) (xx:=xx) (yy:=yy) (sh:=sh)
        (which:=which) (window:=window) (shape:=shape) (input:=input) (word:=word) (pin:=pin)
        (namesAt:=namesAt) (data:=data) (mouth:=mouth) (bank:=bank) (q:=q) (block:=block)
        (h₁:=h₁) (g₁:=g₁) (row:=row) (mem:=mem) (base:=base) (chunk:=chunk) (lane:=lane)
        (signed:=signed) (query:=query) (candidates:=candidates)
        (hubs:=hubs) (fees:=fees) (location:=location) (edge:=edge) (fine:=fine) (valid:=valid) (oldSource:=oldSource) (valueRoom:=cableRoom peer serial part found)
    all_goals assumption

set_option maxHeartbeats 1200000 in
include won owns compared stencil counts arityWords headerWords whichEq compactShape compactHost compactGroup keep tag blank
  actor moved hit bits enough outBits primaryEq decoded concrete degree_ cap_ donors_ alignedUnits shelf signFits grainFit
  observed incoming hubAt oneBit whereAt namesRoom count_ sourceWords valueRoom in
/-- The four retained primary pointer fields match the operand in the original donor slot. -/
theorem calendar_retained_header_at (outputRoom:(ret).nodes*(ret).args≤2^(ret).bits)
    (oldWidth:(ret).previousNodes*(ret).previousArgs≤2^(ret).bits) :
    ∀f:Fin 4,actual f=(nextPtr).header f:=by
  have chipFits : ∀j : Fin (2*(chart).oldCap),(signed₀ (sel_) j).val<2^(chart).fieldBits :=
    fun j=>(signed₀ (sel_) j).isLt.trans_le (Nat.pow_le_pow_right (by decide) signFits)
  apply (calendar_retained_header_at_cable (b:=b)) (a:=a) (early:=early) (menu:=menu)
    (L:=L) (xx:=xx) (yy:=yy) (sh:=sh) (which:=which) (window:=window)
    (shape:=shape) (input:=input) (word:=word) (pin:=pin) (namesAt:=namesAt) (data:=data)
    (mouth:=mouth) (bank:=bank) (q:=q) (block:=block) (h₁:=h₁) (g₁:=g₁) (row:=row)
    (mem:=mem) (base:=base) (chunk:=chunk) (lane:=lane) (signed:=signed) (query:=query)
    (candidates:=candidates) (hubs:=hubs) (fees:=fees) (location:=location)
    (chipFits:=chipFits) (cableRoom:=fun _ _ _ _ => valueRoom)
  all_goals assumption

end
end Hierarchy.DescentPrimitivePalette

end OAI
