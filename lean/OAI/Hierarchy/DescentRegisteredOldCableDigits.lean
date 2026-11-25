import OAI.Hierarchy.DescentReachedPhysicalPinJob
import OAI.Hierarchy.DescentReachedSignedPublicPointer

namespace OAI
/-! The four saved header digits of an old, possibly redirected, cable on a registered physical job. -/
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

include old_live old_empty s Z arity op labels flags stored paid bitsFit in
theorem registered_old_cable_digits {wide:ℕ} (auth:stock) (stampFits:N₀<2^wide)
    (x:NodeOrder.All next) (j:Fin (args₁ x))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (resident:∀f l,Values.Prefix hostFit (small₁ j.val f l)
      (V ((DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) ⟨j.val,written⟩).cast
        (congrArg (7*·) shape.operands)) l))
    (donor:NodeOrder.All arch.bit) (carried:roots ticket arch x=.inl donor)
    (a:Fin (((sh.sites donor.1).recipe hp).arity donor.2)) (same:a.val=j.val)
    (edge:Incident W.graph donor.1) (chunk:ℕ) (len:(chunk+1)*p≤W.graph.width edge.val)
    (sourceCable:((sh.sites donor.1).recipe hp).operand donor.2 a=.inl ⟨.inl edge,chunk,len⟩)
    (f:Fin 4) :
    (booksHeader book_ (physicalJob x fits ⟨j.val,written⟩) (rh x.1) (rg x.1) f).val=
      (Reached.firstCable cap hp donor.1 edge chunk len).header f :=by
  have ptr:=Reached.argumentPointer_cable cap arch.bit prior sh hp pinCode arity donor.1 donor.2 a edge chunk len sourceCable
  have actual:=v.returned_header_digit shape V hostFit (small₁ j.val f) (physB x.1)
    ⟨(advance ticket arch prior x.1 x.2).val,fits⟩ ⟨j.val,written⟩ f (physH x.1) (physG x.1) (resident f)
  have before:=gathered_old_header (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
    (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior) (priorCount:=priorCount)
    (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (sh:=sh) (pinCode:=pinCode) (arity:=arity)
    (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid) (bitsFit:=bitsFit) (birth:=birth)
    auth stampFits x j.val fits donor carried a same f
  have slotEq : (ptr₀ donor j.val) = ptr₀ donor a.val := congrArg (fun ix : ℕ => ptr₀ donor ix) same.symm
  exact actual.trans ((Values.transport_digit lo gs rad field (rows₁ j.val f) v.resolver.nodes
    ⟨(advance ticket arch prior x.1 x.2).val,fits⟩ (block₁ x.1) (home₁ x.1) (group₁ x.1)).trans
      (before.trans (congrArg (fun a:Pointer=>a.header f) (slotEq.trans ptr))))

include old_live old_empty s Z arity op labels flags stored paid bitsFit in
theorem registered_old_cable_header {wide:ℕ} (auth:stock) (stampFits:N₀<2^wide)
    (x:NodeOrder.All next) (j:Fin (args₁ x))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (resident:∀f l,Values.Prefix hostFit (small₁ j.val f l)
      (V ((DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) ⟨j.val,written⟩).cast
        (congrArg (7*·) shape.operands)) l))
    (donor:NodeOrder.All arch.bit) (carried:roots ticket arch x=.inl donor)
    (a:Fin (((sh.sites donor.1).recipe hp).arity donor.2)) (same:a.val=j.val)
    (edge:Incident W.graph donor.1) (chunk:ℕ) (len:(chunk+1)*p≤W.graph.width edge.val)
    (sourceCable:((sh.sites donor.1).recipe hp).operand donor.2 a=.inl ⟨.inl edge,chunk,len⟩)
    (live:0<(A).grainCount edge.val) :
    let side:=decide (W.graph.src edge.val≠donor.1)
    let cableNames₀:=DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank
      ((Function.Embedding.refl (Fin (S.groupCount i))).trans Fin.valEmbedding) (cap.vertex.trans Fin.valEmbedding))
    let first:=DescentPackedOperand.Public.endpoint A (cap.order.trans Fin.valEmbedding) S cap.valid cableNames₀ side ⟨edge.val,⟨0,live⟩⟩
    ∀f,(booksHeader book_ (physicalJob x fits ⟨j.val,written⟩) (rh x.1) (rg x.1) f).val=
      (Pointer.cable first.neighbor.val first.wire.val chunk).header f :=by
  intro side cableNames₀ first f
  have read:=registered_old_cable_digits (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
    (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior) (priorCount:=priorCount)
    (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
    (pinCode:=pinCode) (arity:=arity) (op:=op) (labels:=labels) (flags:=flags) (stored:=stored)
    (paid:=paid) (bitsFit:=bitsFit) (birth:=birth) (v:=v) (shape:=shape) (lo:=lo) (gs:=gs)
    (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V)
    auth stampFits x j fits written resident donor carried a same edge chunk len sourceCable f
  exact read.trans (congrArg (fun w:Pointer=>w.header f)
    (Reached.firstCable_endpoint cap hp donor.1 edge chunk len live))

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
