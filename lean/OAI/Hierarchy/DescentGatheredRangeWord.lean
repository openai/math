import OAI.Hierarchy.DescentDatedOrdinaryRangeExit
import OAI.Hierarchy.DescentRegisterArchiveValues
import OAI.Hierarchy.DescentOrdinarySlotMeaning
import OAI.Hierarchy.DescentSlotAbsentRange
import OAI.Hierarchy.DescentUnusedOperandHosts
import OAI.Hierarchy.DescentVacantOrdinaryPayload
import OAI.Hierarchy.DescentOrdinaryRangeAcquisition
import OAI.Hierarchy.DescentReachedOrdinaryRange
import OAI.Hierarchy.DescentRegisteredRangeWord
import OAI.Hierarchy.DescentNodeCellRoleCount
import OAI.Hierarchy.DescentOrdinaryIssuedRange
import OAI.Hierarchy.DescentOrdinaryWrittenRangeColumn

namespace OAI
/-! # Ordinary gathered span digits at the actual predecessor RAM -/
namespace Hierarchy.DescentLocalArchiveOrder.PaddedOrigin
open DescentNetworkPartition Computability.BorderVNP.Crossing
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentSharedCableNames DescentPackedActorMask
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentScalarBookReshape
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {pinBits : P→ℕ} {W : MarkedWorld F d P pinBits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
local notation "r" => BitDescription.scannedRows he T
local notation "sw" => branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c)
local notation "next" => (ticket.advance arch).bit
local notation "layout" => bestLayout sw
local notation "group" => GadgetNetwork.newSite W.graph (r).pick layout (r).pack

local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c

local notation "A" => cap.placement
local notation "deg" => (A).degree
local notation "bound" => (deg+1)^4*2^k

local notation "shelf"=>2^(packExponent 20 deg)+2
local notation "raw"=>2^(k+1)*shelf
local notation "walkCount"=>DescentHaloWalkRAM.breadth deg
local notation "K"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

open DescentPaidResidentCount
variable {mb : ℕ}
variable (tokens : Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→
  Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
local notation "stock" => Descriptors shelf k (A).pos (A).block (ticketParent (he:=he) (T:=T)) (ticketSlot (c:=c) ticket)
  (key∘group) cap.vertex (Function.Embedding.refl _) moves tokens

local notation "OH" => Fintype.card cap.V
local notation "OG" => S.groupCount i
variable (age : i<S.length) (radix : S.radix=2^k)

variable {w : ℕ} (ports : DatePorts) (mem : Memory w) (room : DatePorts.RangeRoom ports cap arch.bit)
    (population : Fintype.card cap.V≤ports.operandHosts)
local notation "K₀" => ports.nodes
local notation "fits₀" => maxNodes_le arch.bit room.capacity
local notation "oldN" => K₀
local notation "N₀" => DescentPackedActorMask.nodes bound oldN (A).cap
variable (prior : Local arch.bit)
variable (priorCount : Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell mb)
variable (old_live : ∀u,(priorCount (cap.placement.block u) (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1).val=
    Fintype.card (arch.bit.recipe u).Node)
variable (old_empty : ∀b h g,(¬∃u,cap.placement.block u=b ∧ cap.vertex (cap.placement.pos u).2=h ∧ (cap.placement.pos u).1=g)→priorCount b h g=0)

open DescentRetainedRangeDigits DescentOrdinaryAtomFieldRAM.ScalarOperand DescentHaloWalkRAM

local notation "oldSource" j:max f:max => DatePorts.physicalRangeSource ports cap arch.bit room population mem j f
local notation "oldRegister" => DatePorts.rangeRegister ports cap arch.bit prior room.capacity room.hosts
  room.groups room.radix room.positive mem
variable {newNodes width : ℕ}
variable (born : Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell ports.operandBits)
local notation "gathered" j:max f:max v:max => DescentScalarBookReshape.book
  (oldInput age radix (rangeRaster ticket arch tokens priorCount (oldSource j f) born newNodes))
  (target.placement.block v) (hostIndex ticket (target.vertex (target.placement.pos v).2))
  (target.placement.pos v).1

include old_live old_empty in
/-- Decoding the stable gather at an actual surviving scalar node gives its original dated
register. This uses the full recorded ancestor count and the selected ticket. -/
theorem gathered_range_word (auth : stock) (v : n.result.graph.Site) (node : ((next).recipe v).Node)
    (saved : NodeOrder.All arch.bit) (carried : roots ticket arch ⟨v,node⟩=Sum.inl saved)
    (j : ℕ) (f : Fin 3) (wide : N₀<2^width) (fits : (advance ticket arch prior v node).val<newNodes) :
    (take ⟨(advance ticket arch prior v node).val,fits⟩ (gathered j f v)).val =
      (oldRegister).word saved j f :=by
  have routed:=range_at_old_node ticket arch tokens age radix fits₀ prior priorCount old_live old_empty
    (oldSource j f) born auth v node saved carried wide fits
  exact (congrArg Fin.val routed).trans
    (DatePorts.physicalRangeSource_word ports cap arch.bit prior room population mem saved j f).symm

include old_live old_empty in
/-- A date whose returned argument sheet is the physical stable gather copies every
word of a retained node, including both in-range and out-of-range padding. -/
theorem gathered_range_copy (birthAt : ℕ→Fin 3→Block k→Fin (A).cap→Fin 6→Fin OH→Fin OG→Cell ports.operandBits)
    (auth : stock) (newPage : Register next) (nargs : ℕ)
    (keepsWidth : ports.argumentsPerNode≤nargs) (wide : N₀<2^width)
    (fits : ∀x : NodeOrder.All next,(advance ticket arch prior x.1 x.2).val<newNodes)
    (read : ∀(x : NodeOrder.All next) (j : Fin nargs) (f : Fin 3),
      newPage.word x j.val f =
        (take ⟨(advance ticket arch prior x.1 x.2).val,fits x⟩ (DescentScalarBookReshape.book
          (oldInput age radix (rangeRaster ticket arch tokens priorCount (oldSource j.val f) (birthAt j.val f) newNodes))
          (target.placement.block x.1) (hostIndex ticket (target.vertex (target.placement.pos x.1).2))
          (target.placement.pos x.1).1)).val)
    (outside : ∀(x : NodeOrder.All next) (j : ℕ) (f : Fin 3), nargs≤j→newPage.word x j f=0)
    (x : NodeOrder.All next) (saved : NodeOrder.All arch.bit) (carried : roots ticket arch x=Sum.inl saved)
    (j : ℕ) (f : Fin 3) :
    newPage.word x j f=(oldRegister).word saved j f :=by
  by_cases active : j<nargs
  · exact (read x ⟨j,active⟩ f).trans
      (gathered_range_word ticket arch tokens age radix ports mem room population prior priorCount
        old_live old_empty (birthAt j f) auth x.1 x.2 saved carried j f wide (fits x))
  · have beyond : nargs≤j:=Nat.le_of_not_lt active
    exact (outside x j f beyond).trans
      (DatePorts.rangeRegister_unallocated ports cap arch.bit prior room mem saved j f
        (keepsWidth.trans beyond)).symm

variable {roleBits : ℕ} (labels : NodeOrder.All arch.bit → Cell roleBits)
local notation "nodeCounts" => fun x h g=>DescentOrdinaryAtomFieldRAM.RoleCounts.count mb
  (Reached.NodeCells.rolePage (N:=ports.nodes) cap arch.bit prior labels x h g)

include room in
/-- The physical primitive-role page supplies both the complete original count of an occupied
site (including unpaid exterior nodes) and zero in each vacant group. -/
theorem ancestral_counts (active : ∀x,labels x≠0) (countWidth : ports.nodes<2^mb) :
    (∀u,((nodeCounts) ((A).block u) (cap.vertex ((A).pos u).2) ((A).pos u).1).val=Fintype.card (arch.bit.recipe u).Node) ∧
      (∀(x : Block k) (h : Fin OH) (g : Fin OG), (¬∃u,(A).block u=x ∧ cap.vertex ((A).pos u).2=h ∧
        ((A).pos u).1=g) → (nodeCounts) x h g=0) :=by
  constructor
  · intro u
    exact Reached.NodeCells.role_count_at cap arch.bit prior cap.vertex (fun _=>rfl) labels active u (room.capacity u) countWidth
  · intro x h g vacant
    apply Reached.NodeCells.role_count_empty
    rintro ⟨u,block,host,groupEq⟩
    exact vacant ⟨u,block,Fin.ext host,groupEq⟩

include room in
theorem issued_gathered_word (auth : stock) (active : ∀x,labels x≠0) (countWidth : ports.nodes<2^mb)
    (v : n.result.graph.Site) (node : ((next).recipe v).Node) (saved : NodeOrder.All arch.bit)
    (carried : roots ticket arch ⟨v,node⟩=Sum.inl saved)
    (j : ℕ) (f : Fin 3) (fits : (advance ticket arch prior v node).val<newNodes) :
    let rows:=rangeRaster ticket arch tokens (nodeCounts) (oldSource j f) born newNodes
    let column:=DescentScalarBookReshape.book (oldInput age radix rows)
      (target.placement.block v) (hostIndex ticket (target.vertex (target.placement.pos v).2)) (target.placement.pos v).1
    (take ⟨(advance ticket arch prior v node).val,fits⟩ column).val=(oldRegister).word saved j f :=by
  have counts:=ancestral_counts (cap:=cap) arch ports room prior labels active countWidth
  exact gathered_range_word ticket arch tokens age radix ports mem room population prior (nodeCounts)
    counts.1 counts.2 born auth v node saved carried j f (show N₀<2^N₀ from Nat.lt_two_pow_self) fits


open DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony DescentPackedOperand
open DescentDatedAddressBook
private theorem take_digit {b N : ℕ} (x : Cell (b*N)) (i : Fin N) :
    (take i x).val=digit b i.val x.val :=by
  change ((DescentSIMDLookup.encode b N).symm x i).val = _
  simpa only [Equiv.apply_symm_apply] using (digit_encode ((DescentSIMDLookup.encode b N).symm x) i).symm

/-- The physical final-chart pass, the stable vector gather and the predecessor word are
evaluated in order. The gather receipt identifies the whole packed column before the final
write and consequently observes the same word even on an unfunded retained node. -/
theorem ordinary_written_copy {Party : Type} (device : PhysicalOrdinary F Party) (root : ℕ)
    (safe : device.finalChart.Early (device.finalSources root) (device.metaEnd root) w)
    (space : device.afterEnd root<2^w) (before : Memory w) («meta» : device.MetaWords)
    (spans : Books device.resolver) (keys : Fin device.resolver.jobs→DescentDatedPriorOperand.Source device.resolver)
    (metaRead : ∀f x,Reads (device.nodeChart.bank (device.nodeBankBase root) f x) («meta» f x) device.resolver.lanes before)
    (spanRead : ∀x j,Reads (previousBank device.resolver (device.vectorOutput root) x j) (spans x j) device.resolver.lanes before)
    (keyRead : ∀j,Reads (Banks.wordBank device.resolver (device.normalizedEnd root) j)
      (fun h g=>word ((keys j).compiled h g)) device.resolver.lanes before)
    (block : NodeOrder.All next→Fin device.resolver.blocks) (host : NodeOrder.All next→Fin device.resolver.hosts)
    (groupOf : NodeOrder.All next→Fin device.resolver.groups) (number : NodeOrder.All next→Fin device.resolver.nodes)
    (lanes : 0<device.resolver.lanes) (wordFit : device.finalChart.field*device.resolver.nodes*device.resolver.lanes≤w)
    (widthEq : device.finalChart.field=ports.operandBits)
    (longer : ports.argumentsPerNode≤device.resolver.operands)
    (numbers : ∀x,(number x).val=(advance ticket arch prior x.1 x.2).val)
    (active : ∀x,labels x≠0) (countWidth : ports.nodes<2^mb) (auth : stock)
    (birthAt : Fin device.resolver.operands→Fin 3→Block k→Fin (A).cap→Fin 6→Fin OH→Fin OG→Cell ports.operandBits)
    (fromVector : ∀(x : NodeOrder.All next) (j : Fin device.resolver.operands) (f : Fin 3),
      (spans (block x) (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j) (host x) (groupOf x)).val =
        (DescentScalarBookReshape.book
          (oldInput age radix (rangeRaster ticket arch tokens (nodeCounts) (oldSource j.val f) (birthAt j f) device.resolver.nodes))
          (target.placement.block x.1) (hostIndex ticket (target.vertex (target.placement.pos x.1).2))
          (target.placement.pos x.1).1).val)
    (x : NodeOrder.All next) (saved : NodeOrder.All arch.bit) (carried : roots ticket arch x=Sum.inl saved)
    (j : ℕ) (f : Fin 3) :
    (fromRAM (PriorResetArchive.ordinary device root) device.resolver device.finalChart.field
      ((device.argumentsAfter root safe space).image before) lanes block host groupOf number).word x j f=
        (oldRegister).word saved j f :=by
  by_cases live : j<device.resolver.operands
  · let index : Fin device.resolver.operands:=⟨j,live⟩
    have found:=device.issued_range_at root safe space before «meta» spans keys metaRead spanRead keyRead
      block host groupOf number lanes wordFit x index f
    have inside : (advance ticket arch prior x.1 x.2).val<device.resolver.nodes:=(numbers x) ▸ (number x).isLt
    have previous:=issued_gathered_word ticket arch tokens age radix ports mem room population prior
      (birthAt index f) labels auth active countWidth x.1 x.2 saved carried j f inside
    apply found.trans
    apply Eq.trans _ previous
    have fieldEq : device.resolver.size + 2 = ports.operandBits := widthEq
    rw [take_digit,take_digit]
    exact congr (congrArg₂ digit fieldEq (numbers x)) (fromVector x index f)
  · have beyond:=Nat.le_of_not_lt live
    exact (unallocated _ _ _ _ lanes block host groupOf number x j f beyond).trans
      (DatePorts.rangeRegister_unallocated ports cap arch.bit prior room mem saved j f (longer.trans beyond)).symm

section PhysicalRange

open DescentOperandVectorArena DescentOrdinaryRasterReturn
local notation "Q₀" => (2^(k+1)-1)*shelf
local notation "G₁" => S.groupCount (i+1)
variable (device : PhysicalOrdinary F P) (shape : device.VectorShape)
local notation "vA" => device.vector
local notation "vL" => device.resolver
variable (fits : (Fintype.card cap.V)≤device.vector.hosts) (low : device.vector.lows=((2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))) (gs : device.vector.groups=(S.groupCount (i+1))) (rs : device.vector.radix=2^k)
    (bits : device.resolver.size+2=ports.operandBits)
    (birthAt : Fin device.resolver.operands→Fin 3→Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell ports.operandBits)
    (V : References.Rows device.vector cap.placement.degree k ports.nodes cap.placement.cap (device.resolver.size+2) (Packed.bits ((2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))) mb)
local notation:max "pg_" j:arg f:arg => DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j
local notation:max "sm_" j:arg f:arg l:arg => (rangeValues ticket arch tokens age radix (nodeCounts) (oldSource (j).val f)
    (birthAt j f) ((l).cast low)).reindex (congrArg₂ (·*·) gs rs).symm bits.symm
local notation "physicalFields" => previousValues vL vA shape.operands shape.blocks shape.hosts shape.groups
    (References.returnedValue vA V (vL).nodes)
local notation:max "block_" x:arg => ((target.placement.block (x).1).cast rs.symm).cast shape.blocks.symm
local notation:max "host_" x:arg => (widen fits ((hostIndex ticket (target.vertex (target.placement.pos (x).1).2)).cast
    (congrArg (OH*·) low.symm))).cast shape.hosts.symm
local notation:max "group_" x:arg => ((target.placement.pos (x).1).1.cast (shape.groups.trans gs).symm)

section AcquiredRows
variable (tall : Block k→Fin (1+cap.placement.cap*6)→Fin device.vector.hosts→Fin (S.groupCount i)→Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
    (hubs : Fin device.vector.hosts→Fin (S.groupCount i)→Cell 1)
    (roles : Block k→Fin device.vector.hosts→Fin (S.groupCount i)→Cell (roleBits*ports.nodes))
    (old : DescentOperandStateBanks.Pages device.vector.operands→Block k→Fin device.vector.hosts→Fin ((S.groupCount (i+1))*2^k)→Cell (ports.operandBits*ports.nodes))
    (fresh : DescentOperandStateBanks.Pages device.vector.operands→Block k→Fin cap.placement.cap→Fin 6→Fin device.vector.hosts→Fin ((S.groupCount (i+1))*2^k)→Cell ports.operandBits)
local notation "electedGeometry" => acquiredGeometry (fieldBits:=ports.operandBits) (mb:=mb) («K₀»:=K₀) (cap:=cap)
    age radix fits tall hubs roles
local notation:max "pgNative" j:arg f:arg => (pg_ j f).cast (congrArg (7*·) shape.operands)
local notation:max "oldGroup" y:arg => (S.groupDigits age radix).symm (finProdFinEquiv.symm y)

/-- Numerical source fields of all seven pages of the original transposed book at
the machine's own row and field widths. -/
def acquiredReferences : References.Rows vA deg k K₀ (A).cap ((vL).size+2) (Packed.bits Q₀) mb :=
  fun pg l=>(OrdinaryBooks.inputs old fresh electedGeometry pg (l.cast low)).reindex
    (congrArg₂ (·*·) gs rs).symm bits.symm

/-- Every chronological premise of the six-component prefix now describes a
literal paid input, prior one-based role count, or selected printed birth field. -/
theorem acquired_range_prefix
    (liveRows : ∀b s (h : Fin OH) g,tall b s (h.castLE fits) g=tokens b s h g)
    (liveHubs : ∀(h : Fin OH) g,hubs (h.castLE fits) g=flags (cap:=cap) h g)
    (liveRoles : ∀b (h : Fin OH) g,roles b (h.castLE fits) g=
      Reached.NodeCells.rolePage (N:=ports.nodes) cap arch.bit prior labels b h g)
    (oldCells : ∀j : Fin (vL).operands,∀f : Fin 3,∀b (h : Fin OH) y,old (pgNative j f) b (h.castLE fits) y=
      (oldSource j.val f) b h (oldGroup y))
    (birthCells : ∀j : Fin (vL).operands,∀f : Fin 3,∀b s t (h : Fin OH) y,
      fresh (pgNative j f) b s t (h.castLE fits) y=birthAt j f b s t h (oldGroup y)) :
    ∀j : Fin (vL).operands,∀f : Fin 3,∀l,Values.Prefix fits (sm_ j f l)
      (acquiredReferences age radix ports device fits low gs rs bits tall hubs roles old fresh (pgNative j f) l) :=by
  intro j f l
  exact (acquired_prefix ticket arch tokens age radix nodeCounts (oldSource j.val f) (birthAt j f)
    fits tall hubs roles old fresh (pgNative j f) (l.cast low) liveRows liveHubs
    (fun b h g=>congrArg (DescentOrdinaryAtomFieldRAM.RoleCounts.count mb) (liveRoles b h g))
    (oldCells j f) (birthCells j f)).reindex _ _

/-- On a retained node the native born-value words can be taken verbatim.
Their values are permitted to depend on the actually selected matcher vertices. -/
def retainedBirth (j : Fin (vL).operands) (f : Fin 3) (b : Block k) (socket : Fin (A).cap)
    (tag : Fin 6) (h : Fin OH) (g : Fin OG) : Cell ports.operandBits :=
  fresh (pgNative j f) b socket tag (h.castLE fits) (finProdFinEquiv (S.groupDigits age radix g))

theorem native_acquired_prefix
    (liveRows : ∀b s (h : Fin OH) g,tall b s (h.castLE fits) g=tokens b s h g)
    (liveHubs : ∀(h : Fin OH) g,hubs (h.castLE fits) g=flags (cap:=cap) h g)
    (liveRoles : ∀b (h : Fin OH) g,roles b (h.castLE fits) g=
      Reached.NodeCells.rolePage (N:=ports.nodes) cap arch.bit prior labels b h g)
    (oldCells : ∀j : Fin (vL).operands,∀f : Fin 3,∀b (h : Fin OH) y,
      (old (pgNative j f) b (h.castLE fits) y).val=((oldSource j.val f) b h (oldGroup y)).val)
    (j : Fin (vL).operands) (f : Fin 3) (l : Fin (vA).lows) :
    Values.Prefix fits
      ((rangeValues ticket arch tokens age radix nodeCounts (oldSource j.val f)
        (retainedBirth age radix ports device shape fits fresh j f) (l.cast low)).reindex
        (congrArg₂ (·*·) gs rs).symm bits.symm)
      (acquiredReferences age radix ports device fits low gs rs bits tall hubs roles old fresh (pgNative j f) l) :=by
  apply acquired_range_prefix <;> try assumption
  · intro q t b h y
    exact Fin.ext (oldCells q t b h y)
  · intro q t b s u h y
    simp only [retainedBirth,Equiv.apply_symm_apply]

/-- On the padded host suffix the descriptor reader prints no target at any donor.
Consequently every previous-state field, old or born, makes a zero W book. -/
theorem acquired_ghost_book
    (noTicket : ∀b s (h : Fin (vA).hosts) g,OH≤h.val→tall b s h g=none)
    (pg : DescentOperandStateBanks.Pages (vA).operands) (l : Fin (vA).lows)
    (h : Fin (vA).hosts) (g : Fin ((vA).groups*(vA).radix))
    (absent : OH≤h.val) (N : ℕ) :
    ((acquiredReferences (mb:=mb) age radix ports device fits low gs rs bits tall hubs roles old fresh pg l).book N h g)=0 :=by
  let v:=OrdinaryBooks.inputs old fresh electedGeometry pg (l.cast low)
  let group₀:=g.cast (congrArg₂ (·*·) gs rs)
  have ghost : v.book N h group₀=0:=by
    apply Values.book_no_hit
    intro j
    have missing:=fields_ghost (H:=OH)
      (large:=Gather.reaching (hostRotor (cap.vertex.trans (Fin.castLEEmb fits))
        (hostRoster (A) (cap.vertex.trans Fin.valEmbedding)))) (t':=tall) (hubs':=hubs)
      k (gainExponent 20 deg) shelf Q₀ h (oldGroup group₀) j
      (padded_donor_blank fits cap.vertex _ h absent) (fun x s u hu=>noTicket x s u _ hu)
    change DescentScalarVenueMask.fields _ _ _ _ _ _ _ _ _ j≠Packed.token (some (l.cast low))
    rw [missing]
    intro eqn
    have bad : some (l.cast low) = (none : Option (Fin Q₀)) := (Packed.token_back (some (l.cast low))).symm.trans
      ((congrArg (Packed.readToken Q₀) eqn.symm).trans (Packed.token_back none))
    cases bad
  apply Fin.ext
  exact (Values.reindex_book _ _ v N h g).trans (congrArg Fin.val ghost)

theorem acquired_ghost_column
    (noTicket : ∀b s (h : Fin (vA).hosts) g,OH≤h.val→tall b s h g=none)
    (pg : DescentOperandStateBanks.Pages (vL).operands) (b : Fin (vL).blocks)
    (h : Fin (vL).hosts) (g : Fin (vL).groups)
    (absent : OH≤(finProdFinEquiv.symm (h.cast shape.hosts) : Fin (vA).hosts×Fin (vA).lows).1.val) :
    previousValues vL vA shape.operands shape.blocks shape.hosts shape.groups
      (References.returnedValue vA (acquiredReferences (mb:=mb) age radix ports device fits low gs rs bits
        tall hubs roles old fresh) (vL).nodes) pg b h g=0:=by
  apply acquired_ghost_book (mb:=mb) <;> assumption

end AcquiredRows
variable (gather : ∀ (j : Fin device.resolver.operands) (f : Fin 3) (l : Fin device.vector.lows),
    Values.Prefix fits
      ((rangeValues ticket arch tokens age radix
        (fun x h g => DescentOrdinaryAtomFieldRAM.RoleCounts.count mb
          (Reached.NodeCells.rolePage (N:=ports.nodes) cap arch.bit prior labels x h g))
        (DatePorts.physicalRangeSource ports cap arch.bit room population mem j.val f)
        (birthAt j f) (l.cast low)).reindex (congrArg₂ (·*·) gs rs).symm bits.symm)
      (V ((DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j).cast
        (congrArg (7*·) shape.operands)) l))

local notation:max "hostCell" h:arg => (widen fits ((hostIndex ticket h).cast (congrArg (OH*·) low.symm))).cast shape.hosts.symm
local notation:max "wireBlock" b:arg => ((b).cast rs.symm).cast shape.blocks.symm
local notation:max "groupCell" g:arg => (g).cast (shape.groups.trans gs).symm

include gather prior in
/-- A padded destination digit in the real gathered W operand is zero, including the
unused suffix of a genuine occupied site. The prior raw words may take any values. -/
theorem range_values_vacant
    (active : ∀x,labels x≠0) (countWidth : ports.nodes<2^mb) (auth : stock)
    (h : Fin (Fintype.card target.V)) (g : Fin G₁) (b : Block k) (slot : Fin (vL).nodes)
    (vacant : ¬∃v,DescentPaidResidentCount.occupies target.placement (Equiv.refl _) target.vertex h g b v ∧
      slot.val<Fintype.card ((next).recipe v).Node)
    (j : Fin (vL).operands) (f : Fin 3) :
    (take slot ((physicalFields) (pg_ j f) (wireBlock b) (hostCell h) (groupCell g))).val=0:=by
  have count:=ancestral_counts (cap:=cap) arch ports room prior labels active countWidth
  have cell : ((physicalFields) (pg_ j f) (wireBlock b) (hostCell h) (groupCell g)).val=
      (DescentScalarBookReshape.book (oldInput age radix (rangeRaster ticket arch tokens nodeCounts
        (oldSource j.val f) (birthAt j f) (vL).nodes)) b (hostIndex ticket h) g).val:=by
    apply device.previous_range_column shape V fits (fun l=>sm_ j f l) low gs rs _ _ (pg_ j f) _ _ _ (gather j f)
    intro l h₀ g₀
    rw [Values.reindex_book,range_values_book]
  have blank:=field_at_missing ticket arch tokens age radix fits₀ prior nodeCounts count.1 count.2
    auth Nat.lt_two_pow_self (fun _ h₀ g₀=>rangeInput (cap:=cap) (oldSource j.val f) (birthAt j f) h₀ g₀)
    h g b slot vacant
  rw [take_digit,cell,bits]
  have selected:=congrArg Fin.val blank
  rw [←take_digit]
  exact selected

include gather in
/-- An absent native rank has zero span on every actual returned W page, on the
compact rectangle and on the entire padded host suffix. -/
theorem slot_absent_column (floor : ℕ)
    (nextRoom : DatePorts.RangeRoom (DatePorts.ordinary device floor) target next)
    (active : ∀x,labels x≠0) (countWidth : ports.nodes<2^mb) (auth : stock)
    (tall : Block k→Fin K→Fin (vA).hosts→Fin OG→Ticket walkCount raw)
    (hubs : Fin (vA).hosts→Fin OG→Cell 1)
    (roles : Block k→Fin (vA).hosts→Fin OG→Cell (roleBits*K₀))
    (old : DescentOperandStateBanks.Pages (vA).operands→Block k→Fin (vA).hosts→Fin (G₁*2^k)→Cell (ports.operandBits*K₀))
    (fresh : DescentOperandStateBanks.Pages (vA).operands→Block k→Fin (A).cap→Fin 6→Fin (vA).hosts→Fin (G₁*2^k)→Cell ports.operandBits)
    (original : V=acquiredReferences age radix ports device fits low gs rs bits tall hubs roles old fresh)
    (noTicket : ∀b s (h : Fin (vA).hosts) g,OH≤h.val→tall b s h g=none)
    (x : Fin (2^device.venue.k)) (slot : Fin (vL).nodes) (h : Fin (vL).hosts) (g : Fin device.venue.groups)
    (vacant : DatePorts.slotAt (DatePorts.ordinary device floor) target next (advance ticket arch prior)
      nextRoom x slot h g=none) (j : Fin (vL).operands) (f : Fin 3) :
    (take slot ((physicalFields) (pg_ j f) (wireBlock (x.cast (congrArg (2^·) nextRoom.radix.symm))) h
      (groupCell (g.cast nextRoom.groups.symm)))).val=0:=by
  let b:=x.cast (congrArg (2^·) nextRoom.radix.symm)
  let g₀:=g.cast nextRoom.groups.symm
  by_cases compact : h.val<Fintype.card target.V
  · let h₀ : Fin (Fintype.card target.V):=⟨h.val,compact⟩
    have absent:=DatePorts.slot_absent_range (DatePorts.ordinary device floor) target next (advance ticket arch prior)
      nextRoom x slot h g compact vacant
    have blank:=range_values_vacant ticket arch tokens age radix ports mem room population prior labels device shape
      fits low gs rs bits birthAt V gather active countWidth auth h₀ g₀ b slot absent j f
    have same : hostCell h₀=h:=Fin.ext rfl
    rwa [same] at blank
  · have positive : 0<(vA).lows:=by
      by_contra! zero
      have impossible:=(h.cast shape.hosts).isLt
      simp [Nat.eq_zero_of_le_zero zero] at impossible
    have tooFar : OH≤(finProdFinEquiv.symm (h.cast shape.hosts) : Fin (vA).hosts×Fin (vA).lows).1.val:=by
      change OH≤h.val/(vA).lows
      apply (Nat.le_div_iff_mul_le positive).2
      have hostCount : Fintype.card target.V = OH*Q₀ := by rw [ticket.hostCount]; ring
      rw [low,←hostCount]
      exact Nat.le_of_not_lt compact
    have blank:=acquired_ghost_column (cap:=cap) (mb:=mb) age radix ports device shape fits low gs rs bits
      tall hubs roles old fresh noTicket (pg_ j f) (wireBlock b) h (groupCell g₀) tooFar
    rw [original,blank,take_zero]
    rfl

include gather in
/-- The row used by the final operand writer is the returned W row arising from the
actual ticket, original population, old register and born operand values. -/
theorem range_values_written (x : NodeOrder.All next) (j : Fin (vL).operands) (f : Fin 3) :
    ((physicalFields) (pg_ j f) (block_ x) (host_ x) (group_ x)).val=
      (DescentScalarBookReshape.book (oldInput age radix
        (rangeRaster ticket arch tokens (nodeCounts) (oldSource j.val f) (birthAt j f) (vL).nodes))
        (target.placement.block x.1) (hostIndex ticket (target.vertex (target.placement.pos x.1).2))
        (target.placement.pos x.1).1).val :=by
  apply device.previous_range_column shape V fits (fun l=>sm_ j f l) low gs rs _ _ (pg_ j f) _ _ _ (gather j f)
  intro l h g
  rw [Values.reindex_book,range_values_book]

section Meanings
open DescentBundleHistory DescentTerminalSliceRuns
variable {p R : ℕ} (previous : WorldShape p R arch.bit) (hp : 0<p) (one : 1≤R)
    (pins : ∀v,p∣pinBits v) (unit : p∣T.z)
local notation "post" => WorldShape.follow hp T.unitPos unit n (ticket.quantum.symm ▸ ticket.cuts)
    (WorldShape.scanned he hp one pins T previous unit c)
local notation "used_" => fun a : (r).pairs=>(r).picked (a,0)
local notation "origin_"=> DescentOrdinaryLocalBirth.outgoingSlot A (cap.order.trans Fin.valEmbedding) S cap.valid (r).pick used_
local notation:max "bornAt_" j:arg f:arg pair:arg party:arg =>
    let site:=W.graph.src ((r).pick (pair,0))
    birthAt j f ((A).block site) (origin_ pair) party (cap.vertex ((A).pos site).2) ((A).pos site).1
variable (priorWords : ∀y : NodeOrder.All arch.bit,∀j : ℕ,∀f : Fin 3,
    j<(occurrences (previous.sites y.1) y.2).length ∨ f=2 →
    (DatePorts.rangeRegister ports cap arch.bit prior room.capacity room.hosts room.groups room.radix room.positive mem).word y j f =
      atSlot (previous.sites y.1) y.2 j f)
    (birthWords : ∀ (j : Fin device.resolver.operands) (f : Fin 3)
      (pair : (BitDescription.scannedRows he T).pairs) (party : Fin 6),
      let scanned := BitDescription.scannedRows he T
      let site := W.graph.src (scanned.pick (pair,0))
      let origin := DescentOrdinaryLocalBirth.outgoingSlot cap.placement (cap.order.trans Fin.valEmbedding)
        S cap.valid scanned.pick (fun a : scanned.pairs => scanned.picked (a,0))
      (birthAt j f (cap.placement.block site) (origin pair) party (cap.vertex (cap.placement.pos site).2)
        (cap.placement.pos site).1).val =
        if j.val<DescentFreshRoleFields.arity G p T.z (scanned.profile c pair) party then value whole f else 0)

set_option maxHeartbeats 650000 in
include gather priorWords birthWords in
/-- Every present origin, including an unfunded node, yields its true initial operand on
the actual transposed page.  Beyond the last input the count word is physically zero. -/
theorem slot_live_column (active : ∀x,labels x≠0) (countWidth : ports.nodes<2^mb) (auth : stock)
    (x : NodeOrder.All next) (j : Fin (vL).operands) (f : Fin 3)
    (rank : (advance ticket arch prior x.1 x.2).val<(vL).nodes)
    (needed : j.val<(occurrences ((post).sites x.1) x.2).length ∨ f=2) :
    (take ⟨(advance ticket arch prior x.1 x.2).val,rank⟩
      ((physicalFields) (pg_ j f) (block_ x) (host_ x) (group_ x))).val=
      atSlot ((post).sites x.1) x.2 j.val f:=by
  let rows:=rangeRaster ticket arch tokens (nodeCounts) (oldSource j.val f) (birthAt j f) (vL).nodes
  let column:=DescentScalarBookReshape.book (oldInput age radix rows) (target.placement.block x.1)
    (hostIndex ticket (target.vertex (target.placement.pos x.1).2)) (target.placement.pos x.1).1
  have stored:=range_values_written ticket arch tokens age radix ports mem room population prior labels device shape
    fits low gs rs bits birthAt V gather x j f
  have physical : (take ⟨(advance ticket arch prior x.1 x.2).val,rank⟩
      ((physicalFields) (pg_ j f) (block_ x) (host_ x) (group_ x))).val=
      (take ⟨(advance ticket arch prior x.1 x.2).val,rank⟩ column).val:=by
    rw [take_digit,take_digit]
    exact congr (congrArg₂ digit bits rfl) stored
  apply physical.trans
  rw [ordinary_slot_meaning ticket arch previous hp one pins unit x j.val f]
  cases source_ : roots ticket arch x with
  | inl saved =>
    simp only [Sum.elim_inl]
    have nodeFieldsEq :=ordinary_fields ticket arch previous hp one pins unit x
    simp only [source_,Sum.elim_inl] at nodeFieldsEq
    have oldNeeded : j.val<(occurrences (previous.sites saved.1) saved.2).length ∨ f=2 :=by
      rcases needed with valid | last
      · left
        have rowEq := (DescentRetainedRangeDigits.layout ((post).sites x.1) x.2).symm.trans
          ((congrArg (fun rows => repeatFields (List.flatten rows)) nodeFieldsEq).trans
            (DescentRetainedRangeDigits.layout (previous.sites saved.1) saved.2))
        exact Nat.lt_of_lt_of_eq valid (congrArg List.length rowEq)
      · exact Or.inr last
    have savedWord := issued_gathered_word ticket arch tokens age radix ports mem room population prior
      (birthAt j f) labels auth active countWidth x.1 x.2 saved source_ j.val f rank
    have savedValue : (oldRegister).word saved j.val f=atSlot (previous.sites saved.1) saved.2 j.val f :=
      priorWords saved j.val f oldNeeded
    exact Eq.trans savedWord savedValue
  | inr new_ =>
    obtain ⟨pair,party⟩:=new_
    simp only [Sum.elim_inr]
    have counts:=ancestral_counts (cap:=cap) arch ports room prior labels active countWidth
    have row:=range_at_born_node ticket arch tokens age radix fits₀ prior (nodeCounts) counts.1 counts.2
      (oldSource j.val f) (birthAt j f) auth x.1 x.2 pair party source_
      (show N₀<2^N₀ from Nat.lt_two_pow_self) rank
    have bornValue := birthWords j f pair party
    have unpacked := congrArg Fin.val row
    exact Eq.trans unpacked bornValue

include gather priorWords birthWords in
/-- Reading a physical receiver coordinate whose original reindexing found a node
returns exactly that node's mathematical descriptor. -/
theorem slot_present_column (floor : ℕ) (nextRoom : DatePorts.RangeRoom (DatePorts.ordinary device floor) target next)
    (active : ∀x,labels x≠0) (countWidth : ports.nodes<2^mb) (auth : stock)
    (x : Fin (2^device.venue.k)) (slot : Fin (vL).nodes) (h : Fin (vL).hosts) (g : Fin device.venue.groups)
    (y : NodeOrder.All next)
    (present : DatePorts.slotAt (DatePorts.ordinary device floor) target next (advance ticket arch prior)
      nextRoom x slot h g=some y) (j : Fin (vL).operands) (f : Fin 3)
    (needed : j.val<(occurrences ((post).sites y.1) y.2).length ∨ f=2) :
    (take slot ((physicalFields) (pg_ j f) (wireBlock (x.cast (congrArg (2^·) nextRoom.radix.symm))) h
      (groupCell (g.cast nextRoom.groups.symm)))).val=atSlot ((post).sites y.1) y.2 j.val f:=by
  obtain ⟨hx,hs,hh,hg⟩:=DatePorts.slotAt_coordinates (DatePorts.ordinary device floor) target next
    (advance ticket arch prior) nextRoom x slot h g y.1 y.2 present
  have live : (advance ticket arch prior y.1 y.2).val<(vL).nodes:=
    (advance ticket arch prior y.1 y.2).isLt.trans_le (nextRoom.capacity y.1)
  have idx : slot=⟨(advance ticket arch prior y.1 y.2).val,live⟩:=Fin.ext (congrArg Fin.val hs)
  have bx : wireBlock (x.cast (congrArg (2^·) nextRoom.radix.symm))=block_ y := by
    have valueEq := congrArg Fin.val hx
    exact Fin.ext valueEq
  have hy : h=host_ y:=Fin.ext (congrArg Fin.val hh)
  have gy : groupCell (g.cast nextRoom.groups.symm)=group_ y := by
    have valueEq := congrArg Fin.val hg
    exact Fin.ext valueEq
  rw [idx,bx,hy,gy]
  exact slot_live_column ticket arch tokens age radix ports mem room population prior labels device shape
    fits low gs rs bits birthAt V gather previous hp one pins unit priorWords birthWords active countWidth auth y j f live needed
include gather priorWords birthWords in
theorem native_span_values (floor : ℕ)
    (nextRoom : DatePorts.RangeRoom (DatePorts.ordinary device floor) target next)
    (active : ∀x,labels x≠0) (countWidth : ports.nodes<2^mb) (auth : stock)
    (tall : Block k→Fin K→Fin (vA).hosts→Fin OG→Ticket walkCount raw)
    (hubs : Fin (vA).hosts→Fin OG→Cell 1)
    (roles : Block k→Fin (vA).hosts→Fin OG→Cell (roleBits*K₀))
    (old : DescentOperandStateBanks.Pages (vA).operands→Block k→Fin (vA).hosts→Fin (G₁*2^k)→Cell (ports.operandBits*K₀))
    (fresh : DescentOperandStateBanks.Pages (vA).operands→Block k→Fin (A).cap→Fin 6→Fin (vA).hosts→Fin (G₁*2^k)→Cell ports.operandBits)
    (original : V=acquiredReferences age radix ports device fits low gs rs bits tall hubs roles old fresh)
    (noTicket : ∀b s (h : Fin (vA).hosts) g,OH≤h.val→tall b s h g=none)

    (x : Fin (2^device.venue.k)) (slot : Fin (vL).nodes) (h : Fin (vL).hosts) (g : Fin device.venue.groups)
    (j : Fin (vL).operands) :
    (take slot ((physicalFields) (pg_ j (2:Fin 3)) (wireBlock (x.cast (congrArg (2^·) nextRoom.radix.symm))) h
      (groupCell (g.cast nextRoom.groups.symm)))).val =
        (DatePorts.slotAt (DatePorts.ordinary device floor) target next (advance ticket arch prior)
          nextRoom x slot h g).elim 0 (fun y=>atSlot ((post).sites y.1) y.2 j.val 2):=by
  cases found : DatePorts.slotAt (DatePorts.ordinary device floor) target next (advance ticket arch prior)
      nextRoom x slot h g with
  | none =>
    exact slot_absent_column ticket arch tokens age radix ports mem room population prior labels device shape
      fits low gs rs bits birthAt V gather floor nextRoom active countWidth auth tall hubs roles old fresh original noTicket
      x slot h g found j 2
  | some y =>
    exact slot_present_column ticket arch tokens age radix ports mem room population prior labels device shape
      fits low gs rs bits birthAt V gather previous hp one pins unit priorWords birthWords floor nextRoom
      active countWidth auth x slot h g y found j 2 (Or.inr rfl)

end Meanings

include gather in
/-- Read the old operand on the genuine physical W output, and then read the adjacent
argument image after its complete native typed write. The result also covers unused
arguments and old nodes receiving no paid tally. -/
theorem ordinary_wire_copy (root : ℕ)
    (safe : device.finalChart.Early (device.finalSources root) (device.metaEnd root) w)
    (space : device.afterEnd root<2^w) (before : Memory w)
    («meta» : device.MetaWords) (keys : Fin (vL).jobs→DescentDatedPriorOperand.Source vL)
    (metaRead : ∀f x,Reads (device.nodeChart.bank (device.nodeBankBase root) f x) («meta» f x) (vL).lanes before)
    (wRead : ∀x j,Reads (previousBank vL (device.vectorOutput root) x j) ((physicalFields) j x) (vL).lanes before)
    (keyRead : ∀j,Reads (Banks.wordBank vL (device.normalizedEnd root) j)
      (fun h g=>DescentPackedOperand.word ((keys j).compiled h g)) (vL).lanes before)
    (rank : ∀x,Fintype.card ((next).recipe x).Node≤(vL).nodes)
    (lanes : 0<(vL).lanes) (wordFit : device.finalChart.field*(vL).nodes*(vL).lanes≤w)
    (longer : ports.argumentsPerNode≤(vL).operands) (active : ∀x,labels x≠0) (countWidth : ports.nodes<2^mb)
    (auth : stock) (x : NodeOrder.All next) (saved : NodeOrder.All arch.bit)
    (carried : roots ticket arch x=Sum.inl saved) (j : ℕ) (f : Fin 3) :
    (fromRAM (PriorResetArchive.ordinary device root) (vL) device.finalChart.field
      ((device.argumentsAfter root safe space).image before) lanes
      (fun y=>block_ y) (fun y=>host_ y) (fun y=>group_ y)
      (fun y=>(advance ticket arch prior y.1 y.2).castLE (rank y.1))).word x j f=(oldRegister).word saved j f :=by
  apply ordinary_written_copy ticket arch tokens age radix ports mem room population prior labels device root
    safe space before «meta» (fun x j=>(physicalFields) j x) keys metaRead wRead keyRead _ _ _ _ lanes
    wordFit bits longer (fun _=>rfl) active countWidth auth birthAt _ x saved carried j f
  intro y j₀ f₀
  exact range_values_written ticket arch tokens age radix ports mem room population prior labels device shape
    fits low gs rs bits birthAt V gather y j₀ f₀

section DatedRange
open DescentPacking.PackedMatch.Local.Stage
variable (root shelfAddr header : ℕ) (input : Dated.Operands) (count : Bank)
    (wires : device.signed.Input) (venueSource : StageVenueTail.Sources)
    (steps : PhysicalOrdinary.ResultSteps w) (bank : device.ResultRoom (device.stageStart root) venueSource w)
    (clock : DonorDate) (positive : 0<clock.exponent)
    (fit : PhysicalOrdinary.Room device root shelfAddr header input count wires steps clock)
    (dates : ℕ→DateCode w) (initial : Memory w)
local notation "actualFloor" => device.stageStart root
local notation "nextPorts" => DatePorts.ordinary device actualFloor
local notation "beforeWrite" => device.beforeArgumentWrite root shelfAddr header input count wires venueSource
  steps clock positive fit (DateCode.history dates initial i)
local notation "datedCounter" => clock.counter device.payload
  ((clock.schedule device.payload device.seats device.bitsPerField).rotationEnd input.roster actualFloor) header

include gather fits in
/-- Both sides are the live chronological memories. The complete original date writes
the W book and advances its counters before the next registered range is read. -/
theorem dated_wire_copy
    (issued : dates i=device.date root shelfAddr header input count wires venueSource steps bank clock positive)
    (atOld : mem=DateCode.history dates initial i)
    (kept : (datedCounter).endAddr≤device.finalChart.out (device.metaEnd actualFloor))
    (away : header<(datedCounter).endAddr)
    (newRoom : DatePorts.RangeRoom nextPorts target next)
    («meta» : device.MetaWords) (keys : Fin (vL).jobs→DescentDatedPriorOperand.Source vL)
    (metaRead : ∀f x,Reads (device.nodeChart.bank (device.nodeBankBase actualFloor) f x) («meta» f x) (vL).lanes beforeWrite)
    (wRead : ∀x j,Reads (previousBank vL (device.vectorOutput actualFloor) x j) ((physicalFields) j x) (vL).lanes beforeWrite)
    (keyRead : ∀j,Reads (Banks.wordBank vL (device.normalizedEnd actualFloor) j)
      (fun h g=>DescentPackedOperand.word ((keys j).compiled h g)) (vL).lanes beforeWrite)
    (wordFit : device.finalChart.field*(vL).nodes*(vL).lanes≤w)
    (longer : ports.argumentsPerNode≤(vL).operands) (active : ∀x,labels x≠0) (countWidth : ports.nodes<2^mb)
    (auth : stock) (x : NodeOrder.All next) (saved : NodeOrder.All arch.bit)
    (carried : roots ticket arch x=Sum.inl saved) (j : ℕ) (f : Fin 3) :
    (DatePorts.rangeRegister nextPorts target next (advance ticket arch prior)
      newRoom.capacity newRoom.hosts newRoom.groups newRoom.radix newRoom.positive
      (DateCode.history dates initial (i+1))).word x j f=
    (DatePorts.rangeRegister ports cap arch.bit prior room.capacity room.hosts room.groups room.radix room.positive
      (DateCode.history dates initial i)).word saved j f :=by
  subst mem
  have blockCount : 2^device.venue.k=(vL).blocks :=
    (congrArg (2^·) newRoom.radix.symm).trans (rs.symm.trans shape.blocks.symm)
  have groupCount : device.venue.groups=(vL).groups :=
    newRoom.groups.symm.trans (gs.symm.trans shape.groups.symm)
  have dated:=DatePorts.rangeRegister_at_ordinary device root shelfAddr header input count wires venueSource
    steps bank clock positive fit dates initial i nextPorts issued rfl blockCount groupCount kept away target next
    (advance ticket arch prior) newRoom.capacity newRoom.hosts newRoom.groups newRoom.radix newRoom.positive
  rw [dated]
  exact ordinary_wire_copy ticket arch tokens age radix ports _ room population prior labels device shape
    fits low gs rs bits birthAt V gather actualFloor bank.operands (by rw [device.after_end actualFloor bank.geometry]; exact bank.limit)
    beforeWrite «meta» keys metaRead wRead keyRead newRoom.capacity newRoom.positive wordFit longer active countWidth
    auth x saved carried j f

section Meanings
open DescentBundleHistory DescentTerminalSliceRuns
variable {p R : ℕ} (previous : WorldShape p R arch.bit) (hp : 0<p) (one : 1≤R)
    (pins : ∀v,p∣pinBits v) (unit : p∣T.z)
local notation "post" => WorldShape.follow hp T.unitPos unit n (ticket.quantum.symm ▸ ticket.cuts)
    (WorldShape.scanned he hp one pins T previous unit c)
local notation "used_" => fun a : (r).pairs=>(r).picked (a,0)
local notation "origin_"=> DescentOrdinaryLocalBirth.outgoingSlot A (cap.order.trans Fin.valEmbedding) S cap.valid (r).pick used_
local notation:max "bornAt_" j:arg f:arg pair:arg party:arg =>
    let site:=W.graph.src ((r).pick (pair,0))
    birthAt j f ((A).block site) (origin_ pair) party (cap.vertex ((A).pos site).2) ((A).pos site).1
variable (priorWords : ∀y : NodeOrder.All arch.bit,∀j : ℕ,∀f : Fin 3,
    j<(occurrences (previous.sites y.1) y.2).length ∨ f=2 →
    (DatePorts.rangeRegister ports cap arch.bit prior room.capacity room.hosts room.groups room.radix room.positive mem).word y j f =
      atSlot (previous.sites y.1) y.2 j f)
    (birthWords : ∀ (j : Fin device.resolver.operands) (f : Fin 3)
      (pair : (BitDescription.scannedRows he T).pairs) (party : Fin 6),
      let scanned := BitDescription.scannedRows he T
      let site := W.graph.src (scanned.pick (pair,0))
      let origin := DescentOrdinaryLocalBirth.outgoingSlot cap.placement (cap.order.trans Fin.valEmbedding)
        S cap.valid scanned.pick (fun a : scanned.pairs => scanned.picked (a,0))
      (birthAt j f (cap.placement.block site) (origin pair) party (cap.vertex (cap.placement.pos site).2)
        (cap.placement.pos site).1).val =
        if j.val<DescentFreshRoleFields.arity G p T.z (scanned.profile c pair) party then value whole f else 0)

set_option maxHeartbeats 480000 in
include gather priorWords birthWords in
theorem ordinary_slot_register
    (issued : dates i=device.date root shelfAddr header input count wires venueSource steps bank clock positive)
    (kept : (datedCounter).endAddr≤device.finalChart.out (device.metaEnd actualFloor))
    (away : header<(datedCounter).endAddr)
    (newRoom : DatePorts.RangeRoom nextPorts target next)
    («meta» : device.MetaWords) (keys : Fin (vL).jobs→DescentDatedPriorOperand.Source vL)
    (metaRead : ∀f x,Reads (device.nodeChart.bank (device.nodeBankBase actualFloor) f x) («meta» f x) (vL).lanes beforeWrite)
    (wRead : ∀x j,Reads (previousBank vL (device.vectorOutput actualFloor) x j) ((physicalFields) j x) (vL).lanes beforeWrite)
    (keyRead : ∀j,Reads (Banks.wordBank vL (device.normalizedEnd actualFloor) j)
      (fun h g=>DescentPackedOperand.word ((keys j).compiled h g)) (vL).lanes beforeWrite)
    (wordFit : device.finalChart.field*(vL).nodes*(vL).lanes≤w)
    (active : ∀x,labels x≠0) (countWidth : ports.nodes<2^mb) (auth : stock)
    (x : NodeOrder.All next) (j : Fin (vL).operands) (f : Fin 3)
    (needed : j.val<(occurrences ((post).sites x.1) x.2).length ∨ f=2) :
    (DatePorts.rangeRegister nextPorts target next (advance ticket arch prior)
      newRoom.capacity newRoom.hosts newRoom.groups newRoom.radix newRoom.positive
      (DateCode.history dates initial (i+1))).word x j.val f=
      atSlot ((post).sites x.1) x.2 j.val f:=by
  have blockCount : 2^device.venue.k=(vL).blocks :=
    (congrArg (2^·) newRoom.radix.symm).trans (rs.symm.trans shape.blocks.symm)
  have groupCount : device.venue.groups=(vL).groups :=
    newRoom.groups.symm.trans (gs.symm.trans shape.groups.symm)
  rw [DatePorts.rangeRegister_at_ordinary device root shelfAddr header input count wires venueSource
    steps bank clock positive fit dates initial i nextPorts issued rfl blockCount groupCount kept away target next
    (advance ticket arch prior) newRoom.capacity newRoom.hosts newRoom.groups newRoom.radix newRoom.positive]
  let number:=fun y : NodeOrder.All next=>(advance ticket arch prior y.1 y.2).castLE (newRoom.capacity y.1)
  have space : device.afterEnd actualFloor<2^w :=by
    rw [device.after_end actualFloor bank.geometry]
    exact bank.limit
  have written:=device.issued_range_at actualFloor bank.operands space beforeWrite «meta»
    (fun b idx=>(physicalFields) idx b) keys metaRead wRead keyRead (fun y=>block_ y)
    (fun y=>host_ y) (fun y=>group_ y) number newRoom.positive wordFit x j f
  change _=atSlot _ _ _ _
  apply Eq.trans written
  exact slot_live_column ticket arch tokens age radix ports _ room population prior labels device shape
    fits low gs rs bits birthAt V gather previous hp one pins unit priorWords birthWords active countWidth auth x j f
    (number x).isLt needed
end Meanings

end DatedRange
end PhysicalRange

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
