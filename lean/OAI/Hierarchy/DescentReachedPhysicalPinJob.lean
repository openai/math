import OAI.Hierarchy.DescentArchiveCellReads
import OAI.Hierarchy.DescentReachedPinOrigin
import OAI.Hierarchy.DescentReachedPrivateJob
import OAI.Hierarchy.DescentDatedPreviousPageValue
import OAI.Hierarchy.DescentIssuedOperandKey
import OAI.Hierarchy.DescentRegisterArchiveValues
import OAI.Hierarchy.DescentGatheredRangeWord
import OAI.Hierarchy.DescentReachedPublicPointer

namespace OAI
/-! The four previous header digits at the registered ordinary job of an original exterior pin. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedPriorOperand DescentOperandStateBanks DescentSIMDLookup
open DescentOrdinaryAtomFieldRAM.ScalarOperand Computability.BorderVNP.Crossing Computability.VPVNP.BurstRAM ProtocolRAM
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B) (pop:Fintype.card r.V≤ports.operandHosts)
    (m:Memory w)

def physicalHeaderSource (j:ℕ) (f:Fin 4) (b:DescentColonies.Block k) (h:Fin (Fintype.card r.V))
    (g:Fin (S.groupCount age)) : Cell (ports.operandBits*ports.nodes) :=
  if live:j<ports.argumentsPerNode then
    archivedCell ports.archive ports.rangeLayout ports.operandBits m room.positive
      (DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) ⟨j,live⟩)
      (b.cast (congrArg (2^·) room.radix)) (h.castLE pop) (g.cast room.groups)
  else 0

variable {p R s Z:ℕ} (sh:WorldShape p R B) (op:RotorSpec)
    (label:NodeOrder.All B→DescentPrimitivePalette.Label G s Z op)
    (ptr:NodeOrder.All B→ℕ→Pointer) (flags:Fin (2^ports.venue.k)→Fin ports.nodes→
      Fin ports.operandHosts→Fin ports.venue.groups→ℕ)
    (seen:ArchiveRead ports r B number room sh op label ptr flags m)

include seen in
theorem ArchiveRead.original_header (v:W.graph.Site) (u:(B.recipe v).Node) (j:Fin ports.argumentsPerNode)
    (f:Fin 4) (live:j.val<(occurrences (sh.sites v) u).length)
    (width:ports.operandBits*ports.nodes*ports.operandLanes≤w) :
    (take (((bounded B number v).trans (Fin.castLEEmb (maxNodes_le B room.capacity))) u)
      (physicalHeaderSource ports r B room pop m j.val f (r.placement.block v)
        (r.vertex (r.placement.pos v).2) (r.placement.pos v).1)).val=(ptr ⟨v,u⟩ j.val).header f :=by
  let b:=(r.placement.block v).cast (congrArg (2^·) room.radix)
  let pg:=DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) j
  obtain ⟨cells,observed,digits⟩:=seen.headers b j f
  have stored:=archivedCell_read ports.archive ports.rangeLayout ports.operandBits m room.positive pg b cells observed width
  let h := (r.vertex (r.placement.pos v).2).castLE pop
  let g := ((r.placement.pos v).1).cast room.groups
  have source : physicalHeaderSource ports r B room pop m j.val f (r.placement.block v)
      (r.vertex (r.placement.pos v).2) (r.placement.pos v).1 =
      archivedCell ports.archive ports.rangeLayout ports.operandBits m room.positive pg b h g :=
    dite_eq_left j.isLt
  have word := source.trans (congrFun (congrFun stored h) g)
  exact (congrArg (fun (cell : Cell (ports.operandBits*ports.nodes)) =>
    (take (((bounded B number v).trans (Fin.castLEEmb (maxNodes_le B room.capacity))) u) cell).val) word).trans
      (digits _ _ _ ⟨v,u⟩ (slotAt_original ports r B number room v u) live)
end
end Hierarchy.DescentSixParty.Chronology.DatePorts

namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentScalarBookReshape
noncomputable section
variable {D k K cap H Q J r a nb mb Q' J' r' a':ℕ}

def Values.transport (lo:Q'=Q) (groups:J'=J) (lanes:r'=r) (field:a'=a)
    (s:Fin Q→Values D k K cap H (J*r) a nb mb) :
    Fin Q'→Values D k K cap H (J'*r') a' nb mb :=by
  subst Q';subst J';subst r';subst a';exact s

theorem Values.transport_digit (lo:Q'=Q) (groups:J'=J) (lanes:r'=r) (field:a'=a)
    (s:Fin Q→Values D k K cap H (J*r) a nb mb) (n:ℕ) (u:Fin n) (b:Fin r)
    (h:Fin (H*Q)) (g:Fin J) :
    (take u (DescentScalarBookReshape.book
      (fun l x y=>(Values.transport lo groups lanes field s l).book n x y)
      (b.cast lanes.symm) (h.cast (congrArg (H*·) lo.symm)) (g.cast groups.symm))).val=
      (take u (DescentScalarBookReshape.book (fun l x y=>(s l).book n x y) b h g)).val :=by
  subst Q';subst J';subst r';subst a';rfl
end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedPriorOperand DescentSIMDLookup DescentOperandVectorArena DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentOperandStateBanks DescentOrdinaryRasterReturn
noncomputable section
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P) (shape:v.VectorShape)
    {D k K cap H nb mb:ℕ} (V:References.Rows v.vector D k K cap (v.resolver.size+2) nb mb)

def returnedBook : Books v.resolver:=fun x pg=>previousValues v.resolver v.vector shape.operands
    shape.blocks shape.hosts shape.groups (References.returnedValue v.vector V v.resolver.nodes) pg x

theorem returned_header_digit (pop:H≤v.vector.hosts)
    (small:Fin v.vector.lows→Values D k K cap H (v.vector.groups*v.vector.radix) (v.resolver.size+2) nb mb)
    (b:Fin v.vector.radix) (node:Fin v.resolver.nodes) (arg:Fin v.resolver.operands) (f:Fin 4)
    (h:Fin (H*v.vector.lows)) (g:Fin v.vector.groups)
    (resident:∀l,Values.Prefix pop (small l)
      (V ((DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) arg).cast (congrArg (7*·) shape.operands)) l)) :
    let job:=v.resolver.index (b.cast shape.blocks.symm,node,arg)
    (booksHeader (v.returnedBook shape V) job ((widen pop h).cast shape.hosts.symm) (g.cast shape.groups.symm) f).val=
      (take node (DescentScalarBookReshape.book (fun l x y=>(small l).book v.resolver.nodes x y) b h g)).val :=by
  intro job
  let group:=g.cast shape.groups.symm
  have matchJob:v.resolver.index.symm job=(b.cast shape.blocks.symm,node,arg):=v.resolver.index.symm_apply_apply _
  have words:=v.previous_header_at shape V pop small job f h group (by simpa only [matchJob] using resident)
  change (take ((v.resolver.index.symm job).2.1) (v.previousHeaderValue shape V job f _ group)).val=_
  have first := congrArg (fun cell => (take ((v.resolver.index.symm job).2.1) cell).val) words
  apply first.trans
  simp only [matchJob]
  rfl
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

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
set_option maxRecDepth 4096
set_option Elab.async false
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
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
local notation "bound" => DescentHaloWalkRAM.breadth deg*2^k

local notation "shelf"=>2^(packExponent 20 deg)+2
local notation "raw"=>2^(k+1)*shelf
local notation "walks₀"=>DescentHaloWalkRAM.breadth deg
local notation "K"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

open DescentPaidResidentCount
variable {mb : ℕ} (tokens : Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
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

open DescentOrdinaryAtomFieldRAM DescentRetainedRangeDigits DescentOrdinaryAtomFieldRAM.ScalarOperand DescentHaloWalkRAM


open DescentKernelHistory DescentBundleHistory DescentOperandStateBanks DescentDatedPriorOperand
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentPackedOperand
open PhysicalOrdinary DescentOrdinaryRasterReturn
variable {p R s Z:ℕ} (hp:0<p) (one:1≤R) (pin:∀e,p∣bits e)
    (sh:WorldShape p R arch.bit) (unit:p∣T.z)
local notation "uni" => fun _ : (r).pairs=>T.z
local notation "birthRoom" => fun _ : (r).pairs=>le_refl T.z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "M" => rawGraph he T c
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni birthRoom prof hp sh.sites sh.edges pin whole
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni birthRoom prof
local notation "source" x:arg => (names).symm (roots ticket arch x)

local notation "pitch₁" => (2^(k+1)-1)*shelf
local notation "OH₁" => Fintype.card cap.V
local notation "NG₁" => S.groupCount (i+1)
variable (pinCode:P→ℕ) (arity:ℕ) (op:RotorSpec) (labels:NodeOrder.All arch.bit→DescentPrimitivePalette.Label G s Z op)
    (flags:Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)
local notation "ptr₀" => Reached.argumentPointer cap arch.bit prior sh hp pinCode arity
variable (stored:DatePorts.ArchiveRead ports cap arch.bit prior room sh op labels (Reached.argumentPointer cap arch.bit prior sh hp pinCode arity) flags mem)
    (paid:∀v u,((sh.sites v).recipe hp).arity u≤ports.argumentsPerNode)
    (bitsFit:ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (birth:Fin 4→Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell ports.operandBits)
local notation "priorAt" n:arg f:arg => DatePorts.physicalHeaderSource ports cap arch.bit room population mem n f
local notation "rows₁" n:arg f:arg => rangeValues ticket arch tokens age radix priorCount (priorAt n f) (birth f)
local notation "block₁" x:arg => target.placement.block x
local notation "home₁" x:arg => hostIndex ticket (target.vertex (target.placement.pos x).2)
local notation "group₁" x:arg => (target.placement.pos x).1
local notation "args₁" x:arg => (((after).sites (x).1).recipe hp).arity (x).2
local notation "earlier_" x:arg j:arg => ((baseShape (source x).1).recipe hp).operand (source x).2 (sourceIndex ticket arch hp one pin sh unit x j)

include old_live old_empty s Z op labels flags stored paid bitsFit in
theorem gathered_old_header {newNodes wide:ℕ} (auth:stock) (stampFits:N₀<2^wide)
    (x:NodeOrder.All next) (arg:ℕ) (fits:(advance ticket arch prior x.1 x.2).val<newNodes)
    (donor:NodeOrder.All arch.bit) (carried:roots ticket arch x=.inl donor)
    (original:Fin (((sh.sites donor.1).recipe hp).arity donor.2)) (same:original.val=arg) (f:Fin 4) :
    (take ⟨(advance ticket arch prior x.1 x.2).val,fits⟩ (DescentScalarBookReshape.book
      (fun l h g=>((rows₁ arg f) l).book newNodes h g) (block₁ x.1) (home₁ x.1) (group₁ x.1))).val=
      (ptr₀ donor arg).header f :=by
  have index:arg<ports.argumentsPerNode:=by rw [←same];exact original.isLt.trans_le (paid _ _)
  have live:arg<(occurrences (sh.sites donor.1) donor.2).length:=by
    rw [DescentRetainedRangeDigits.length _ _ hp,←same];exact original.isLt
  have before:=DatePorts.ArchiveRead.original_header ports cap arch.bit prior room population mem sh op labels
    ptr₀ flags stored donor.1 donor.2 ⟨arg,index⟩ f live bitsFit
  have issued:=range_at_old_node ticket arch tokens age radix fits₀ prior priorCount old_live old_empty
    (priorAt arg f) (birth f) auth x.1 x.2 donor carried stampFits fits
  exact (congrArg Fin.val issued).trans before

private abbrev GatheredPhysicalPinStatement : Prop :=
  ∀ {newNodes wide:ℕ} (_auth:stock) (_stampFits:N₀<2^wide)
    (x:NodeOrder.All next) (j:Fin (args₁ x)) (fits:(advance ticket arch prior x.1 x.2).val<newNodes)
    (z:Attached (M) (source x).1) (chunk:ℕ) (len:(chunk+1)*p≤bits z.val)
    (_rawPin:earlier_ x j=.inl ⟨.inr z,chunk,len⟩) (f:Fin 4),
    (take ⟨(advance ticket arch prior x.1 x.2).val,fits⟩ (DescentScalarBookReshape.book
      (fun l h g=>((rows₁ j.val f) l).book newNodes h g) (block₁ x.1) (home₁ x.1) (group₁ x.1))).val=
      (Pointer.pin (pinCode z.val) chunk).header f

include old_live old_empty s Z arity op labels flags stored paid bitsFit in
theorem gathered_physical_pin :
    GatheredPhysicalPinStatement ticket arch tokens age radix ports mem room population prior priorCount hp one pin sh unit pinCode birth :=by
  intro newNodes wide auth stampFits x j fits z chunk len rawPin f
  obtain ⟨donor,a,carried,same,⟨⟨part,off,ok⟩,word,attached⟩,_⟩:=
    original_pin_source ticket arch hp one pin sh unit x j z chunk len rawPin
  obtain ⟨port,portID,portIs,offset⟩:=attached
  change part=.inr port at portIs
  change off=chunk at offset
  subst part;subst off
  have ptr:=Reached.argumentPointer_pin cap arch.bit prior sh hp pinCode arity donor.1 donor.2 a port chunk ok word
  have previous:=gathered_old_header (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
    (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior) (priorCount:=priorCount)
    (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (sh:=sh) (pinCode:=pinCode) (arity:=arity)
    (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid) (bitsFit:=bitsFit) (birth:=birth)
    auth stampFits x j.val fits donor carried a same f
  have slotEq : (ptr₀ donor j.val) = ptr₀ donor a.val :=
    congrArg (fun ix : ℕ => ptr₀ donor ix) same.symm
  have portEq : Pointer.pin (pinCode port.val) chunk = Pointer.pin (pinCode z.val) chunk :=
    congrArg (fun v : P => Pointer.pin (pinCode v) chunk) portID
  exact previous.trans (congrArg (fun pointer : Pointer => pointer.header f)
    (slotEq.trans (ptr.trans portEq)))

variable (v:PhysicalOrdinary F P) (shape:v.VectorShape)
    (lo:v.vector.lows=((2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))) (gs:v.vector.groups=S.groupCount (i+1)) (rad:v.vector.radix=2^k)
    (field:v.resolver.size+2=ports.operandBits) (hostFit:Fintype.card cap.V≤v.vector.hosts)
    (V:References.Rows v.vector cap.placement.degree k ports.nodes cap.placement.cap (v.resolver.size+2) (Packed.bits ((2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))) mb)
local notation:max "small₁" n:arg f:arg => Values.transport lo gs rad field (rows₁ n f)
local notation:max "physH" x:arg => ((home₁ x).cast (congrArg (OH*·) lo.symm))
local notation:max "physG" x:arg => ((group₁ x).cast gs.symm)
local notation:max "physB" x:arg => ((block₁ x).cast rad.symm)
local notation:max "physicalJob" x:arg fit:arg arg:arg =>
  v.resolver.index ((physB (x).1).cast shape.blocks.symm,⟨(advance ticket arch prior (x).1 (x).2).val,fit⟩,arg)
local notation:max "rh" x:arg => ((widen hostFit (physH x)).cast shape.hosts.symm)
local notation:max "rg" x:arg => ((physG x).cast shape.groups.symm)
local notation "book_" => v.returnedBook shape V

private abbrev RegisteredPinDigitsStatement : Prop :=
  ∀ {wide:ℕ} (auth:stock) (stampFits:N₀<2^wide)
    (x:NodeOrder.All next) (j:Fin (args₁ x))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (resident:∀(f : Fin 4) (l : Fin v.vector.lows),Values.Prefix hostFit ((small₁ j.val f) l)
      (V ((DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) ⟨j.val,written⟩).cast
        (congrArg (7*·) shape.operands)) l))
    (z:Attached (M) (source x).1) (chunk:ℕ) (len:(chunk+1)*p≤bits z.val)
    (rawPin:earlier_ x j=.inl ⟨.inr z,chunk,len⟩) (f:Fin 4),
    (booksHeader book_ (physicalJob x fits ⟨j.val,written⟩) (rh x.1) (rg x.1) f).val=
      (Pointer.pin (pinCode z.val) chunk).header f

include old_live old_empty s Z arity op labels flags stored paid bitsFit in
/-- An actual row of each of the four returned operand pages. The sole readback
from the gather is its prefix of six primitive inputs (walks, old words, births,
wanted names, venue names and counts), shared with the range-page pipeline. -/
theorem registered_pin_digits :
    RegisteredPinDigitsStatement ticket arch tokens age radix ports mem room population prior priorCount hp one pin sh unit pinCode birth v shape lo gs rad field hostFit V :=by
  intro wide auth stampFits x j fits written resident z chunk len rawPin f
  have actual:=v.returned_header_digit shape V hostFit (small₁ j.val f) (physB x.1)
    ⟨(advance ticket arch prior x.1 x.2).val,fits⟩ ⟨j.val,written⟩ f (physH x.1) (physG x.1) (resident f)
  have before:=gathered_physical_pin (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
    (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior) (priorCount:=priorCount)
    (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
    (pinCode:=pinCode) (arity:=arity) (op:=op) (labels:=labels) (flags:=flags) (stored:=stored)
    (paid:=paid) (bitsFit:=bitsFit) (birth:=birth) auth stampFits x j fits z chunk len rawPin f
  exact actual.trans ((Values.transport_digit lo gs rad field (rows₁ j.val f) v.resolver.nodes
    ⟨(advance ticket arch prior x.1 x.2).val,fits⟩ (block₁ x.1) (home₁ x.1) (group₁ x.1)).trans before)

/-- A rectangular slot at the actual previous date, in its archived node order and
with its actual allocated argument stride. -/
def previousNodeSlot (arityFit:∀v u,((sh.sites v).recipe hp).arity u≤arity) (v:W.graph.Site) :
    DescentLocalPrivateNames.Slot ((sh.sites v).recipe hp) ↪ Fin (ports.nodes*arity) where
  toFun a:=finProdFinEquiv ((prior v a.1).castLE (room.capacity v),a.2.castLE (arityFit v a.1))
  inj' :=by
    rintro ⟨u,j⟩ ⟨u',j'⟩ hit
    have pair:=finProdFinEquiv.injective hit
    have nodeValues := congrArg (fun a : Fin ports.nodes × Fin arity => a.1.val) pair
    have nodes : u = u' := (prior v).injective (Fin.ext nodeValues)
    subst u'
    have argValues := congrArg (fun a : Fin ports.nodes × Fin arity => a.2.val) pair
    have eqn : j = j' := Fin.ext argValues
    subst j'
    rfl

theorem previousNodeSlot_val (arityFit:∀v u,((sh.sites v).recipe hp).arity u≤arity)
    (v:W.graph.Site) (a:DescentLocalPrivateNames.Slot ((sh.sites v).recipe hp)) :
    (previousNodeSlot (arch:=arch) (ports:=ports) (room:=room) (prior:=prior) (hp:=hp) (sh:=sh) (arity:=arity) arityFit v a).val=(prior v a.1).val*arity+a.2.val :=by
  change (finProdFinEquiv ((prior v a.1).castLE (room.capacity v), a.2.castLE (arityFit v a.1))).val = _
  simp [finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]


local notation "atSlot₀" fit:arg => previousNodeSlot (arch:=arch) (ports:=ports) (room:=room) (prior:=prior) (hp:=hp) (sh:=sh) (arity:=arity) fit

private abbrev RegisteredPrivateDigitsStatement : Prop :=
  ∀ {wide:ℕ} (auth:stock) (stampFits:N₀<2^wide)
    (arityFit:∀v u,((sh.sites v).recipe hp).arity u≤arity)
    (x:NodeOrder.All next) (j:Fin (args₁ x))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (resident:∀(f : Fin 4) (l : Fin v.vector.lows),Values.Prefix hostFit ((small₁ j.val f) l)
      (V ((DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) ⟨j.val,written⟩).cast
        (congrArg (7*·) shape.operands)) l))
    (h:((baseShape (source x).1).recipe hp).UsedWord) (hidden:earlier_ x j=.inr h.val),
    ∃(donor:NodeOrder.All arch.bit)(slot:Fin (((sh.sites donor.1).recipe hp).arity donor.2))
      (word:((sh.sites donor.1).recipe hp).UsedWord)
      (inside:donor.1∈(reachedHalo ticket).member (currentLabel ticket arch x.1 x.2)),
      let «alias»:=(DescentLocalPrivateNames.firstAlias ((sh.sites donor.1).recipe hp) ((atSlot₀ arityFit) donor.1) word).val
      roots ticket arch x=.inl donor ∧ slot.val=j.val ∧
      ((sh.sites donor.1).recipe hp).operand donor.2 slot=.inr word.val ∧
      carriedLabel ticket arch hp one pin sh unit (atSlot₀ arityFit) (source x).1 h=
        Key.carried (((reachedHalo ticket).slot (currentLabel ticket arch x.1 x.2)) ⟨donor.1,inside⟩).val «alias» ∧
      ∀f,(booksHeader book_ (physicalJob x fits ⟨j.val,written⟩) (rh x.1) (rg x.1) f).val=
        (Pointer.privateWord «alias»).header f

set_option maxHeartbeats 600000 in
include old_live old_empty s Z pinCode op labels flags stored paid bitsFit in
/-- The same four native pages for a carried private word, read before the
donor retargeting ticket. Their ordinal uses the original row-major node/arg map. -/
theorem registered_private_digits :
    RegisteredPrivateDigitsStatement ticket arch tokens age radix ports mem room population prior priorCount hp one pin sh unit arity birth v shape lo gs rad field hostFit V :=by
  intro wide auth stampFits arityFit x j fits written resident h hidden
  obtain ⟨donor,slot,word,inside,carried,same,read,keyEq⟩:=
    private_job_origin ticket arch hp one pin sh unit (atSlot₀ arityFit) x j h hidden
  refine ⟨donor,slot,word,inside,carried,same,read,keyEq,?_⟩
  intro f
  have pointer:=Reached.argumentPointer_private cap arch.bit prior sh hp pinCode arity donor.1 donor.2 slot
    ((atSlot₀ arityFit) donor.1) (fun a=>(previousNodeSlot_val (arch:=arch) (ports:=ports) (room:=room) (prior:=prior) (hp:=hp) (sh:=sh) (arity:=arity) arityFit donor.1 a).symm)
    word read
  have before:=gathered_old_header (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
    (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior) (priorCount:=priorCount)
    (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (sh:=sh) (pinCode:=pinCode) (arity:=arity)
    (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid) (bitsFit:=bitsFit) (birth:=birth)
    auth stampFits x j.val fits donor carried slot same f
  have actual:=v.returned_header_digit shape V hostFit (small₁ j.val f) (physB x.1)
    ⟨(advance ticket arch prior x.1 x.2).val,fits⟩ ⟨j.val,written⟩ f (physH x.1) (physG x.1) (resident f)
  refine actual.trans ((Values.transport_digit lo gs rad field (rows₁ j.val f) v.resolver.nodes
    ⟨(advance ticket arch prior x.1 x.2).val,fits⟩ (block₁ x.1) (home₁ x.1) (group₁ x.1)).trans (before.trans ?_))
  have slotEq : (ptr₀ donor j.val) = ptr₀ donor slot.val :=
    congrArg (fun idx : ℕ => ptr₀ donor idx) same.symm
  exact congrArg (fun t : Pointer => t.header f) (slotEq.trans pointer)

variable (typed:BookPointers (v.returnedBook shape V))
    (digits:Fin v.resolver.jobs→Fin v.resolver.hosts→Fin v.resolver.groups→Fin 8→ℕ)
    (grain:Cell (v.resolver.size+2))
local notation "sides_" => fun j h g=>DescentDatedPublicGrain.withGrain grain
  (DescentDatedOperandCoordinates.Ticket.recordedSide v.resolver.size (digits j h g))
local notation "roles_" => fun j f h g=>DescentDatedOperandCoordinates.Ticket.recordedRole v.resolver.size (digits j h g) f
variable (room₁ : ∀ j h g,
  11 * (DescentDatedOperandCoordinates.Ticket.recordedRole v.resolver.size (digits j h g) 1).val +
    (DescentDatedOperandCoordinates.Ticket.recordedRole v.resolver.size (digits j h g) 2).val < 2^(v.resolver.size+2))
local notation "src₁" => ofBooks book_ typed sides_ roles_ room₁

private abbrev RegisteredPinJobStatement : Prop :=
  ∀ {wide:ℕ} (auth:stock) (stampFits:N₀<2^wide)
    (x:NodeOrder.All next) (j:Fin (args₁ x))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (resident:∀(f : Fin 4) (l : Fin v.vector.lows),Values.Prefix hostFit ((small₁ j.val f) l)
      (V ((DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) ⟨j.val,written⟩).cast
        (congrArg (7*·) shape.operands)) l))
    (z:Attached (M) (source x).1) (chunk:ℕ) (len:(chunk+1)*p≤bits z.val)
    (rawPin:earlier_ x j=.inl ⟨.inr z,chunk,len⟩),
    resolve (((src₁) (physicalJob x fits ⟨j.val,written⟩)).compiled (rh x.1) (rg x.1))=
      .pin (pinCode z.val) chunk

include old_live old_empty s Z arity op labels flags stored paid bitsFit in
/-- The public-pin arm of InputResponse at the actual block, node, host, group
and operand job. All eight routing digits may vary on this arm. -/
theorem registered_pin_job :
    RegisteredPinJobStatement ticket arch tokens age radix ports mem room population prior priorCount hp one pin sh unit pinCode birth v shape lo gs rad field hostFit V typed digits grain room₁ :=by
  intro wide auth stampFits x j fits written resident z chunk len rawPin
  apply DescentDatedPriorOperand.source_pin v.resolver book_ typed digits grain room₁
  exact registered_pin_digits (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
    (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior) (priorCount:=priorCount)
    (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
    (pinCode:=pinCode) (arity:=arity) (op:=op) (labels:=labels) (flags:=flags) (stored:=stored)
    (paid:=paid) (bitsFit:=bitsFit) (birth:=birth) (v:=v) (shape:=shape) (lo:=lo) (gs:=gs)
    (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V) auth stampFits x j fits written resident z chunk len rawPin

private abbrev RegisteredFinalPinStatement : Prop :=
  ∀ {wide:ℕ} (auth:stock) (stampFits:N₀<2^wide)
    (x:NodeOrder.All next) (j:Fin (args₁ x))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (resident:∀(f : Fin 4) (l : Fin v.vector.lows),Values.Prefix hostFit ((small₁ j.val f) l)
      (V ((DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) ⟨j.val,written⟩).cast
        (congrArg (7*·) shape.operands)) l))
    (z:Attached n.result.graph x.1) (chunk:ℕ) (len:(chunk+1)*p≤bits z.val)
    (found:(((after).sites x.1).recipe hp).operand x.2 j=.inl ⟨.inr z,chunk,len⟩),
    resolve (((src₁) (physicalJob x fits ⟨j.val,written⟩)).compiled (rh x.1) (rg x.1))=
      .pin (pinCode z.val) chunk

include old_live old_empty s Z arity op labels flags stored paid bitsFit in
theorem registered_final_pin :
    RegisteredFinalPinStatement ticket arch tokens age radix ports mem room population prior priorCount hp one pin sh unit pinCode birth v shape lo gs rad field hostFit V typed digits grain room₁ :=by
  intro wide auth stampFits x j fits written resident z chunk len found
  obtain ⟨a,full,same,pinOrigin⟩:=final_pin_source ticket arch hp one pin sh unit x j z chunk len found
  have read:=registered_pin_job (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
    (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior) (priorCount:=priorCount)
    (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
    (pinCode:=pinCode) (arity:=arity) (op:=op) (labels:=labels) (flags:=flags) (stored:=stored)
    (paid:=paid) (bitsFit:=bitsFit) (birth:=birth) (v:=v) (shape:=shape) (lo:=lo) (gs:=gs)
    (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V) (typed:=typed) (digits:=digits) (grain:=grain) (room₁:=room₁)
    auth stampFits x j fits written resident a chunk full pinOrigin
  simpa only [same] using read

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
