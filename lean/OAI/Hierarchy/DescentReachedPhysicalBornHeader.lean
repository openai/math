import OAI.Hierarchy.DescentReachedPhysicalPinJob
import OAI.Hierarchy.DescentReachedBornCable
import OAI.Hierarchy.DescentOrdinaryBornHeader

namespace OAI
/-! Four original birth header fields at the actual dated operand book. -/
namespace Hierarchy.DescentOrdinaryBorn
open DescentSIMDLookup DescentOperandStateBanks DescentRawCablePanel
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

private theorem publicSourceHeaders (B : Spec) (z profile arg size : ℕ) (party : Fin 6)
    (item : Mouth) (live : mouth B z profile party arg = some item) (fits : item.chunk < 2^(size+2))
    {loc nam donorBits : ℕ} (donor : Donor loc nam donorBits) (first : donor.first = true)
    (supply : ∀ s, (donor.supplyUnits s).val = (profileDigits B.capacity profile s).val + B.supplyOffset)
    (stored localField : Fin 4 → ℕ) (column : ∀ f, stored f = localField f)
    (source : ∀ f : Fin 4, localField f = (component (size+2)
      (pointerAt B.demand B.grain z donor party arg) (f.castLE (by decide : 4≤7))).val) :
    (∀ f : Fin 4, stored f = (Pointer.cable 0 0 item.chunk).header f) ∧
    stored 0 = (field B (size+2) 0 arg z profile party).val := by
  have fieldRead (f : Fin 4) : stored f = (field B (size+2) (f.castLE (by decide : 4≤7)) arg z profile party).val :=
    (column f).trans ((source f).trans (congrArg Fin.val
      (component_first B z profile arg (size+2) party donor first supply (f.castLE (by decide : 4≤7)))))
  refine ⟨?_,fieldRead 0⟩
  intro f
  have tagFit : 1<2^(size+2) := (by decide : 1<2^2).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_left 2 size))
  rw [fieldRead]
  fin_cases f <;> simp [field, live, Pointer.fields, Pointer.header, Fin.val_natCast,
    Nat.mod_eq_of_lt tagFit, Nat.mod_eq_of_lt fits]


end
end Hierarchy.DescentOrdinaryBorn

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


open DescentKernelHistory DescentBundleHistory DescentOperandStateBanks DescentDatedPriorOperand
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentPackedOperand
open PhysicalOrdinary DescentOrdinaryRasterReturn
variable {p R s Z:ℕ} (hp:0<p) (one:1≤R) (pin:∀e,p∣pinBits e)
    (sh:WorldShape p R arch.bit) (unit:p∣T.z)
local notation "uni" => fun _ : (r).pairs=>T.z
local notation "birthRoom" => fun _ : (r).pairs=>le_refl T.z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "M" => rawGraph he T c
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni birthRoom prof hp sh.sites sh.edges pin whole
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni birthRoom prof
local notation:max "source" x:arg => (names).symm (roots ticket arch x)

local notation "pitch₁" => (2^(k+1)-1)*shelf
local notation "OH₁" => Fintype.card cap.V
local notation "NG₁" => S.groupCount (i+1)
variable (birth : Fin 4 → Block k → Fin cap.placement.cap → Fin 6 → Fin (Fintype.card cap.V) → Fin (S.groupCount i) → Cell ports.operandBits)
local notation:max "priorAt" n:arg f:arg => DatePorts.physicalHeaderSource ports cap arch.bit room population mem n f
local notation:max "rows₁" n:arg f:arg => rangeValues ticket arch tokens age radix priorCount (priorAt n f) (birth f)
local notation:max "block₁" x:arg => target.placement.block x
local notation:max "home₁" x:arg => hostIndex ticket (target.vertex (target.placement.pos x).2)
local notation:max "group₁" x:arg => (target.placement.pos x).1
local notation:max "args₁" x:arg => (((after).sites (x).1).recipe hp).arity (x).2
local notation:max "earlier_" x:arg j:arg => ((baseShape (source x).1).recipe hp).operand (source x).2 (sourceIndex ticket arch hp one pin sh unit x j)

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


open DescentOrdinaryBorn
local notation:max "home0" i:arg => W.graph.src ((r).pick (i,0))
local notation:max "seat0" i:arg => outgoingSlot A (cap.order.trans Fin.valEmbedding) S cap.valid (r).pick (fun t:(r).pairs=>(r).picked (t,0)) i
local notation:max "localBorn" i:arg party:arg f:arg => birth f ((A).block (home0 i)) (seat0 i) party
  (cap.vertex ((A).pos (home0 i)).2) ((A).pos (home0 i)).1

local notation:max "profCode" i:arg => (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (prof i)).val
include old_live old_empty in
/-- The returned book on a newborn job reads the original bank at exactly
the first picked cable's outgoing slot and original actor coordinates. -/
theorem registered_born_column {wide:ℕ} (auth:stock) (stampFits:N₀<2^wide)
    (x:NodeOrder.All next) (j:Fin (args₁ x)) (i:(r).pairs) (party:Fin 6)
    (fresh:roots ticket arch x=.inr (i,party))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (resident:∀(f : Fin 4) (l : Fin v.vector.lows),Values.Prefix hostFit (small₁ j.val f l)
      (V ((DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) ⟨j.val,written⟩).cast
        (congrArg (7*·) shape.operands)) l)) (f:Fin 4) :
    (booksHeader book_ (physicalJob x fits ⟨j.val,written⟩) (rh x.1) (rg x.1) f).val=
      (localBorn i party f).val :=by
  have actual:=v.returned_header_digit shape V hostFit (small₁ j.val f) (physB x.1)
    ⟨(advance ticket arch prior x.1 x.2).val,fits⟩ ⟨j.val,written⟩ f (physH x.1) (physG x.1) (resident f)
  have picked:=range_at_born_node ticket arch tokens age radix fits₀ prior priorCount old_live old_empty
    (priorAt j.val f) (birth f) auth x.1 x.2 i party fresh stampFits fits
  exact actual.trans ((Values.transport_digit lo gs rad field (rows₁ j.val f) v.resolver.nodes
    ⟨(advance ticket arch prior x.1 x.2).val,fits⟩ (block₁ x.1) (home₁ x.1) (group₁ x.1)).trans
      (congrArg Fin.val picked))


include old_live old_empty in
theorem registered_born_headers {wide:ℕ} (auth:stock) (stampFits:N₀<2^wide)
    (x:NodeOrder.All next) (j:Fin (args₁ x)) (i:(r).pairs) (party:Fin 6)
    (fresh:roots ticket arch x=.inr (i,party))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (resident:∀(f : Fin 4) (l : Fin v.vector.lows),Values.Prefix hostFit (small₁ j.val f l)
      (V ((DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) ⟨j.val,written⟩).cast
        (congrArg (7*·) shape.operands)) l))
    (mouth_:Mouth) (hit:mouth (actual G p) T.z (profCode i) party j.val=some mouth_)
    (chunkFit:mouth_.chunk<2^(v.resolver.size+2))
    {loc nam donorBits:ℕ} (donor:DescentRawCablePanel.Donor loc nam donorBits)
    (first:donor.first=true) (supply:∀s,(donor.supplyUnits s).val=((prof i).val s).val+G.k)
    («source»:∀f:Fin 4,(localBorn i party f).val=(component (v.resolver.size+2)
      (pointerAt G.b p T.z donor party j.val) (f.castLE (by decide : 4≤7))).val)
    :
    (∀f:Fin 4,(booksHeader book_ (physicalJob x fits ⟨j.val,written⟩) (rh x.1) (rg x.1) f).val=
      (Pointer.cable 0 0 mouth_.chunk).header f) ∧
    (booksHeader book_ (physicalJob x fits ⟨j.val,written⟩) (rh x.1) (rg x.1) 0).val=
      (DescentOrdinaryBorn.field (actual G p) (v.resolver.size+2) 0 j.val T.z (profCode i) party).val :=by
  have supplied:∀s,(donor.supplyUnits s).val=
      (profileDigits (actual G p).capacity (profCode i) s).val+(actual G p).supplyOffset:=by
    intro s
    simpa only [actual,profile_read] using supply s
  have column (f : Fin 4) := registered_born_column (ticket:=ticket) (arch:=arch) (tokens:=tokens) (old_live:=old_live)
      (old_empty:=old_empty) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
      (mem:=mem) (ports:=ports) (room:=room) (population:=population) (prior:=prior) (priorCount:=priorCount)
      (age:=age) (radix:=radix) (birth:=birth) (v:=v) (shape:=shape) (lo:=lo) (gs:=gs) (rad:=rad)
      (field:=field) (hostFit:=hostFit) (V:=V) auth stampFits x j i party fresh fits written resident f
  exact DescentOrdinaryBorn.publicSourceHeaders (actual G p) T.z (profCode i) j.val v.resolver.size party
    mouth_ hit chunkFit donor first supplied
    (fun f => (booksHeader book_ (physicalJob x fits ⟨j.val,written⟩) (rh x.1) (rg x.1) f).val)
    (fun f => (localBorn i party f).val) column «source»

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
