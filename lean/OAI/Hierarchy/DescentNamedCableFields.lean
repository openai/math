import OAI.Hierarchy.DescentTerminalCableSourceFrame
import OAI.Hierarchy.DescentTerminalCableWidthReport

namespace OAI
/-! The named chronology's retained socket roster, signed wings and frozen width tables feed the physical cable pass. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage
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
open ThreeFlat.Routing
local notation "retained" => S.groupWidth k tail S.length+k
local notation "O" => leafOrder X G S b hp base width
local notation "placement" => b.target.placement
local notation "native" => b.target.order.trans Fin.valEmbedding
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount S.length)) (b.target.vertex.trans Fin.valEmbedding))
local notation "pinRank" v => (densePinEquiv X G S b hp base v).toEmbedding.trans Fin.valEmbedding
local notation "operand" v => leafOperands X G S b hp base v
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



open DescentTerminalPreflightSpace DescentPackedColony DescentTerminalHeaderGroups
open DescentTerminalDenseHeaderBoot DescentTerminalWidthRowsRAM DescentPacking.PackedMatch.Local.Stage

/-- The paid endpoint book and fixed three-socket program use the same sorted
peer at every physical socket, even when the true host has fewer neighbors. -/
def fixedRoster {H d e : ℕ} (dims:d=e) (raw:Fin H→Fin d→Option (Fin H)) : Fin H→Fin e→Option (Fin H) :=
  fun h j=>indexed raw h (j.cast dims.symm)

theorem fixedRoster_sorted {H d e : ℕ} (dims:d=e) (raw:Fin H→Fin d→Option (Fin H)) :
    Sorted (fixedRoster dims raw) := by
  subst e
  exact sorted_mounted raw

theorem fixedRoster_present {H d e : ℕ} (dims:d=e) (raw:Fin H→Fin d→Option (Fin H)) (u:Fin H) :
    present (fixedRoster dims raw) u=present (indexed raw) u := by
  subst e
  rfl

private theorem cableOnDimensions {d cap M short rows w pBits argc : ℕ}
    (hd:(placement).degree=d) (hc:(placement).cap=cap) (R:Rasters d (2^k) cap)
    (sockets:Counter.Sockets) (pos:0<M) (whole:S.groupCount S.length≤M) (groupPos:0<S.groupCount S.length)
    (raw:Fin H0→Fin (placement).degree→Option (Fin H0)) (m current:Memory w) (lower:ℕ)
    (held:∀a<lower,current a=m a)
    (real:Rasters.Inputs (p:=p) (bw:=pBits) (argc:=argc) placement hosts S b.target.valid b.target.order
      raw (presented hd hc R) m)
    (q:ℕ) (hq:0<q) (rom:ℕ) (out:Fin 4→Bank)
    (good:(⟨sockets,H0,d,short,G.b,rows,R.wing,pos⟩:Counter.Rack (2^k) cap (S.groupCount S.length) M).Fits w)
    (hostsFit:H0<2^w) (degreeFit:d<2^short) (wingWidth:DescentSignedCableCodec.width d cap*M≤ short)
    (peerRoom:H0*d≤ sockets.roster.size) (peerEnd:sockets.roster.base+sockets.roster.size≤lower)
    (wingEnd:∀u j,(R.wing u j).base+(R.wing u j).size≤lower)
    (roster:∀(h:Fin H0)(j:Fin d),m (sockets.roster.base+(h.val*d+j.val))=(target (fixedRoster hd raw h j):Computability.VPVNP.BurstRAM.Word w))
    (live:(stream net b.target.home b.target.order outs nodeRank ins q hp (H0*H0)).length≤rows)
    (romEnd:rom+extent q p≤lower) (earlier:lower≤ sockets.origin)
    (tables:∀j<extent q p,m (rom+j)=back w q p j) :
    let machine:Counter.Rack (2^k) cap (S.groupCount S.length) M:=⟨sockets,H0,d,short,G.b,rows,R.wing,pos⟩
    let R₀:=fixedRoster hd raw
    let final:=machine.final q p current
    DescentTerminalDenseHeaderRAM.Reads (layout q p rom machine.printer.output (out 0) (out 1) (out 2) (out 3))
      (padded (n:=rows) (stream net b.target.home b.target.order outs nodeRank ins q hp (H0*H0))) final ∧
    ∀j:Fin (H0*d),machine.printer.prefix.read final (j.val:Computability.VPVNP.BurstRAM.Word w)=
      ((passed q p (slotCount (p:=p) R₀ net b.target.home) (j.val+1)).length:Computability.VPVNP.BurstRAM.Word w) := by
  subst d;subst cap
  obtain ⟨pitch,cover,_,read⟩:=real.wings
  have banks (u) (j) : H0≤(R.wing u j).size:=real.bankRoom u j
  have one:=covered_chunks groupPos whole
  have old (u) (j) : Reads (R.wing u j) (fun h g=>DescentSignedCableCodec.encode
      (Prepare.signed placement native S b.target.valid (Function.Embedding.refl _) hosts u j h g)) M current := by
    have prev:=covered_pitch (R.wing u j) _ m groupPos cover whole (read u j)
    intro t
    have address : (row H0 (S.groupCount S.length) M t).val<H0 :=
      (row H0 (S.groupCount S.length) M t).isLt.trans_le (by rw [one,Nat.mul_one])
    have stop : (R.wing u j).base+(row H0 (S.groupCount S.length) M t).val<lower :=
      (Nat.add_lt_add_left (address.trans_le (banks u j)) _).trans_le (wingEnd u j)
    exact (held _ stop).trans (prev t)
  have peers (h:Fin H0) (j:Fin (placement).degree) : current (sockets.roster.base+(h.val*(placement).degree+j.val))=
      (target (indexed raw h j):Computability.VPVNP.BurstRAM.Word w) := by
    have inside : h.val*(placement).degree+j.val<H0*(placement).degree :=
      (Nat.add_lt_add_left j.isLt _).trans_le (by simpa [Nat.succ_mul] using Nat.mul_le_mul_right (placement).degree h.isLt)
    have stop := (Nat.add_lt_add_left (inside.trans_le peerRoom) sockets.roster.base).trans_le peerEnd
    exact (held _ stop).trans (roster h j)
  have divide (z : Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))) : p∣s*1:=by
    rw [Nat.mul_one]
    unfold AtomSchedule.firstWidth AtomSchedule.grainAt
    exact (dvd_mul_right p _).trans (dvd_mul_right _ _)
  exact Counter.cable_fields placement native S b.target.valid (Function.Embedding.refl _) hosts raw sockets current
    R.wing pos G.b q rows b.target.order outs nodeRank ins real.near hp hq
    (by rw [b.target.grain,Nat.mul_comm]) divide good hostsFit degreeFit wingWidth peerRoom peers
    (fun u j=>by simpa only [one,Nat.mul_one] using banks u j) old
    (by simpa only [one,Nat.mul_one] using hostsFit.le) live rom (out 0) (out 1) (out 2) (out 3)
    (romEnd.trans earlier) (fun j hj=>(held _ ((Nat.add_lt_add_left hj rom).trans_le romEnd)).trans (tables j hj))

section BinSize
variable (q drift:ℕ) (op:RotorSpec) (headerRows paidRows bin:ℕ)
local notation "fmt" => ({geometryFormat G S k g p tail q drift op headerRows paidRows with binSize:=bin}:PreflightFormat)
local notation "spec" => preflightSpec X G S k g p tail fmt
variable (origin:ℕ) (peer:Bank) (old:Fin (2^k) → Fin (2*((capCalendar G.b S.rounds g S.height).prod*256)) → Bank)
local notation "rack" => (spec).rasters origin peer old
local notation "eqs" => preflight_caps (tail:=tail) X G S b fmt
local notation "measuredRack" => presented (eqs).1 (eqs).2.1 rack
local notation "table₀" => decodeBook S G base radix p q (spec).degree (spec).cap (spec).printBits (by change 3+1≤4; decide)
local notation "cpu₀" => (spec).issuedBook origin peer old


local notation "sockets" => (spec).sockets origin peer
local notation "machine" => (spec).cables origin peer old

/-- The concrete cable writer reads the same earlier signed pages as the six-book
printer. The all-socket roster supplies the sentinel for each absent neighbor.
The input memory is the physical primitive snapshot before the six static weights. -/
theorem fixed_cable_fields_width {w:ℕ} (primitive:Memory w) (control:ℕ→ℕ)
    (raw:Fin H0→Fin (placement).degree→Option (Fin H0))
    (original:Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=Nat.clog 2 (q+1))
      placement hosts S b.target.valid b.target.order raw measuredRack primitive)
    (paid act:Fin (2^k)→Bank) (total modulo homes:Bank) (boundary:ℕ)
    (prior:(spec).Before origin paid act old peer total modulo homes boundary)
    (space:(spec).maskBase origin<2^w) (hq:0<q)
    (peerRows:H0*(spec).degree≤peer.size)
    (peerData:∀(h:Fin H0)(j:Fin (spec).degree),primitive (peer.base+(h.val*(spec).degree+j.val))=
      (target (fixedRoster (eqs).1 raw h j):Computability.VPVNP.BurstRAM.Word w))
    (live:(stream net b.target.home b.target.order outs nodeRank ins q hp (H0*H0)).length≤headerRows)
    (rom:ℕ) (out:Fin 4→Bank) (source:rom+extent q p≤(spec).cohortEnd origin)
    (tables:∀j<extent q p,primitive (rom+j)=back w q p j) :
    let current:=(spec).cableInput origin peer old table₀ control primitive
    let final:=(machine).final q p current
    DescentTerminalDenseHeaderRAM.Reads
      (layout q p rom (machine).printer.output (out 0) (out 1) (out 2) (out 3))
      (padded (n:=headerRows) (stream net b.target.home b.target.order outs nodeRank ins q hp (H0*H0))) final ∧
      ∀j:Fin (H0*(spec).degree),(machine).printer.prefix.read final (j.val:Computability.VPVNP.BurstRAM.Word w)=
        ((passed q p (slotCount (p:=p) (fixedRoster (eqs).1 raw) net b.target.home) (j.val+1)).length:Computability.VPVNP.BurstRAM.Word w) := by
  have lanes:=(preflight_grains X G S b hp base fmt).2
  have positive:(0<(spec).groups):=by rw [←lanes];exact (spec).signedPositive
  have nonempty:0<(spec).strips:=by change 0<3+_;omega
  obtain ⟨ec,ew,wb,bf,fc,_,_,_,_⟩:=(spec).layers origin
  have before : (spec).cohortEnd origin≤(spec).weights origin:=ec.trans ew
  have upper : (spec).weights origin≤((spec).controls origin).finish := wb.trans (bf.trans fc)
  have low:=(spec).cable_input_low origin peer old table₀ control primitive space nonempty prior.roster prior.oldCables
  have cut:=(spec).census_end origin
  have hCap:H0≤((spec).census origin).size:=Nat.le_pow_clog (by decide) _
  have hFit:H0<2^w:=by
    have lim:=((spec).all_lower origin space).1
    exact hCap.trans_lt ((Nat.le_add_left ..).trans_lt (cut.trans_lt lim))
  have dfit:3<2^(spec).cableCellBits:=by
    have lo:2≤(spec).cableCellBits:=by change 2≤2+_; exact Nat.le_add_right ..
    exact (show 3<2^2 by decide).trans_le (Nat.pow_le_pow_right (by decide) lo)
  have wide:DescentSignedCableCodec.width (spec).degree (spec).cap*(spec).signedLanes≤(spec).cableCellBits:=by
    rw [lanes,Nat.mul_comm]
    exact Nat.le_add_left ..
  exact cableOnDimensions X G S b hp base width (eqs).1 (eqs).2.1 rack sockets (spec).signedPositive
    (by change (spec).groups≤(spec).signedLanes;exact lanes.ge) positive raw primitive
    ((spec).cableInput origin peer old table₀ control primitive) ((spec).weights origin) low original
    q hq rom out ((spec).fits_cables origin space paid act old peer total modulo homes boundary prior)
    hFit dfit wide peerRows (prior.roster.trans before) (fun u j=>(prior.oldCables u j).trans before)
    peerData live (source.trans before) upper tables

end BinSize

variable (q drift:ℕ) (op:RotorSpec) (headerRows paidRows:ℕ)
local notation "fmt" => geometryFormat G S k g p tail q drift op headerRows paidRows
local notation "spec" => preflightSpec X G S k g p tail fmt
variable (origin:ℕ) (peer:Bank) (old:Fin (2^k) → Fin (2*((capCalendar G.b S.rounds g S.height).prod*256)) → Bank)
local notation "rack" => (spec).rasters origin peer old
local notation "eqs" => preflight_caps (tail:=tail) X G S b fmt
local notation "measuredRack" => presented (eqs).1 (eqs).2.1 rack
local notation "table₀" => decodeBook S G base radix p q (spec).degree (spec).cap (spec).printBits (by change 3+1≤4; decide)
local notation "cpu₀" => (spec).issuedBook origin peer old


local notation "sockets" => (spec).sockets origin peer
local notation "machine" => (spec).cables origin peer old

/-- The concrete cable writer reads the same earlier signed pages as the six-book
printer. The all-socket roster supplies the sentinel for each absent neighbor.
The input memory is the physical primitive snapshot before the six static weights. -/
theorem fixed_cable_fields {w:ℕ} (primitive:Memory w) (control:ℕ→ℕ)
    (raw:Fin H0→Fin (placement).degree→Option (Fin H0))
    (original:Rasters.Inputs (p:=p) (bw:=(spec).printBits) (argc:=Nat.clog 2 (q+1))
      placement hosts S b.target.valid b.target.order raw measuredRack primitive)
    (paid act:Fin (2^k)→Bank) (total modulo homes:Bank) (boundary:ℕ)
    (prior:(spec).Before origin paid act old peer total modulo homes boundary)
    (space:(spec).maskBase origin<2^w) (hq:0<q)
    (peerRows:H0*(spec).degree≤peer.size)
    (peerData:∀(h:Fin H0)(j:Fin (spec).degree),primitive (peer.base+(h.val*(spec).degree+j.val))=
      (target (fixedRoster (eqs).1 raw h j):Computability.VPVNP.BurstRAM.Word w))
    (live:(stream net b.target.home b.target.order outs nodeRank ins q hp (H0*H0)).length≤headerRows)
    (rom:ℕ) (out:Fin 4→Bank) (source:rom+extent q p≤(spec).cohortEnd origin)
    (tables:∀j<extent q p,primitive (rom+j)=back w q p j) :
    let current:=(spec).cableInput origin peer old table₀ control primitive
    let final:=(machine).final q p current
    DescentTerminalDenseHeaderRAM.Reads
      (layout q p rom (machine).printer.output (out 0) (out 1) (out 2) (out 3))
      (padded (n:=headerRows) (stream net b.target.home b.target.order outs nodeRank ins q hp (H0*H0))) final ∧
      ∀j:Fin (H0*(spec).degree),(machine).printer.prefix.read final (j.val:Computability.VPVNP.BurstRAM.Word w)=
        ((passed q p (slotCount (p:=p) (fixedRoster (eqs).1 raw) net b.target.home) (j.val+1)).length:Computability.VPVNP.BurstRAM.Word w) := by
  exact fixed_cable_fields_width X G S b hp base width q drift op headerRows paidRows
    (NativeBranch.binLimit (k:=k) S) origin peer old primitive control raw original paid act
    total modulo homes boundary prior space hq peerRows peerData live rom out source tables

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
