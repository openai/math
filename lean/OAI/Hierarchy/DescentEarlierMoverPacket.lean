import OAI.Hierarchy.DescentEarlierRootPlacement
import OAI.Hierarchy.DescentCalendarMoverWindow
import OAI.Hierarchy.DescentDatedCanonicalBirthRegisters

namespace OAI
/-! # The packed prior-home selection observed by the primitive mover -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentGL DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentPaidResidentCount.Reset DescentSIMDLookup DescentPackedZip DescentContactDonorFront
open DescentGroupPeerOrder DescentResetLocalRoster DescentResetStemKey DescentStageEdgeReceipt
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames.Stage DescentIssuedFallbackPanel
open DescentSixParty.Chronology DescentPackedWalsh DescentResetGates DescentResetHostSize
open DescentPackedZip DescentFallbackPeriod.Projected.Receiver DescentPlainTerminal.Suffix
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 10000
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (M nextM field metaBits : ℕ) (calendar : List ℕ)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "H" => S.hostSize i
local notation "pad" => input.valid.host
local notation "idt" => input.vertex.trans (Fin.castLEEmb pad)
local notation "tall" => B.frame.host.symm.toEmbedding.trans idt
local notation "named" => (Z).rawHostRank T tall
local notation "J" => 2^cc
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-cc
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "pitch" => H*shelf
local notation "span_" => H*chunks J M
local notation "full" => (A).wire*((A).z*G.b)*cap
variable {bw N K R hm l tiny t bit : ℕ}
  (rc : Receiver deg cap N (Z).n r cc H (S.groupCount i) K R M hm l tiny field Ht bw)
  (E : EstimatorArena) (stencil : StencilBook) (source : StencilBook.Sources)
  (base split hubWidth : ℕ) (ports : Ports deg) (oldId oldHub : Bank)
  (fee total portPitch groupDigits batches factor : ℕ)
  (primitive : CanonicalTag (2^(Z).n)→Cell bit) (page : RootPage r (2^(Z).n))
local notation "layer" => DescentRecordedRotorLayers.width f cap
local notation "book" => rc.issuedBook E stencil source base split hubWidth ports oldId (.lit cap)
  f fee full total portPitch (Z).graph (Z).width C groupDigits batches layer factor primitive page
local notation "src" => rc.atlasSources E stencil source base split hubWidth ports oldId (.lit cap)
  f fee full total portPitch (Z).graph (Z).width C groupDigits batches layer factor primitive page
local notation "raw" => rc.issuedSources E stencil source base split hubWidth ports oldId (.lit cap) f fee full total portPitch
local notation "pairs" => fun table head=>Recorded.reservationFields E head ports H portPitch cc (E.dim-cc)
  table (Nat.clog 2 (E.dim+2)) total (.lookup oldId .row)
local notation "pg" => DescentOperandRootPull.matrixPage r (Z).n
variable (space : rc.PreparedFits book) (measured : Memory bw) (hdr : OriginalHeader B pad rc book measured)
  (x : OriginalArrays B pad field) {nbits : ℕ}
local notation "done" => rc.preparedImage book space measured
local notation "middle" => rc.preparedMid book space measured
local notation "entry" => RootPacket B rc book space measured hdr src x nbits t
local notation "body" => calendar_sender_matrix B M field rc book space measured hdr x
local notation "L" => 2^r
local notation "roof" => rc.headerEnd book
local notation "arena" => RootTemplates.arena roof H J M r (Z).n deg


local notation "m" => S.groupWidth k tail i+k
variable (move : DescentRetainedHomeMover.Layout)
local notation "old" => move.transfer
variable (hostAxis : (old).hosts=H) (dimAxis : (old).high+(old).low=m)
    (cutAxis : (old).cut=cc) (degreeAxis : move.degree=deg)
    (loadAxis : move.cap=cap) (fieldAxis : move.rootField=field)
local notation "observed" => moverWindow B rc book space measured hdr x move hostAxis dimAxis cutAxis
  degreeAxis loadAxis fieldAxis

/-- The complete original gathered packet supplies the earlier primitive mover, with its actual
source host, elected row, lane pitch and (possibly different) packed word type. -/
theorem RootPacket.earlier_mover (issued : entry) (area : (src).OperandRoom H J M bw roof)
    (price : M*max (field*DescentRotorWindowArchive.count deg L cap)
      (DescentRotorWindowArchive.output (Z).n L cap)≤bw/2) (bus : move.rootLanes=M) :
    Source (rc.gatheredOperand book pg) observed move.rootLanes done:=by
  have formed:=RootPacket.earlier_placement B M field rc E stencil source base split hubWidth ports oldId
    fee total portPitch groupDigits batches factor primitive page space measured hdr x issued area price
  have slots : (old).donors=L :=
    (congrArg (fun x:ℕ=>2^x) (congrArg₂ Nat.sub dimAxis cutAxis)).trans
      (congrArg (fun x:ℕ=>2^(x-cc)) B.keyWidth).symm
  have schema : move.control.rootWidth=field*DescentRotorWindowArchive.count deg L cap :=by
    apply congrArg₂ Nat.mul fieldAxis
    change DescentRotorWindowArchive.count move.degree (old).donors move.cap=_
    exact (congrArg₂ (fun n c => DescentRotorWindowArchive.count n (old).donors c) degreeAxis loadAxis).trans
      (congrArg (fun j => DescentRotorWindowArchive.count deg j cap) slots)
  apply DescentDatedAddressBook.PhysicalReset.FinalInputs.source_axes _ _ hostAxis
    (congrArg (fun x:ℕ=>2^x) cutAxis) schema bus _ _ formed.1
  intro h g
  rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
