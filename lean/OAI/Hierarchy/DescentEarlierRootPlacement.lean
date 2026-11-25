import OAI.Hierarchy.DescentCalendarMatrixOrigins
import OAI.Hierarchy.DescentPreparedFinalGather
import OAI.Hierarchy.DescentReservedMatrixRow
import OAI.Hierarchy.DescentIssuedRootWork
import OAI.Hierarchy.DescentOperandPreparedPackets

namespace OAI
/-! # The original matrix payload and signed source rows in the completed root memory -/
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
set_option maxHeartbeats 1000000
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

/-- At completed roots the gathered matrix and every physical signed bank came from this root packet. -/
theorem RootPacket.earlier_placement (issued : entry) (area : (src).OperandRoom H J M bw roof)
    (price : M*max (field*DescentRotorWindowArchive.count deg L cap) (DescentRotorWindowArchive.output (Z).n L cap)≤bw/2) :
    Source (rc.gatheredOperand book pg) (fun v hi=>encode field (DescentRotorWindowArchive.count deg L cap)
      (body v hi)) M done ∧
    ∀j lo,Reads ((src).signed lo j)
      (fun v hi=>((DescentSignedCableCodec.encode (originalCable B x v hi lo j)).val:Cell field)) M done :=by
  have reads (j : Fin (DescentRotorWindowArchive.count deg L cap)) :
      (((book).table pg).2.reads j)=(src).matrixRow H j :=by
    exact (raw).reserved_matrix_reads (field:=field) (Z).graph (Z).width f Ht C groupDigits batches layer primitive
      H factor hubWidth source.roster source.hubs rc.projectionEnd J M stencil.n pairs page false
      (DescentOperandRootPull.defaultRoot r) j
  have early (i) : (((book).table pg).2.reads i).Fits bw roof := (reads i).symm ▸ (src).matrix_fit area i
  constructor
  · refine rc.gathered_source_from_final book space measured pg (fun v hi j=>body v hi j) ?_ price early ?_
    · intro i
      exact ProtocolRAMGeneratedWrite.fits_mono _ ((Nat.le_add_right ..).trans (Nat.le_add_right ..)) (early i)
    · intro i
      exact (congrArg (fun term : Expr => Source term (fun v hi => body v hi i) M done) (reads i)).mpr (issued.matrix i)
  · intro s q
    exact Chooser.reads_before ((src).signed q s) _ middle done (issued.signed s q) (rc.before_header book space measured)
      (area.ports q s) (Nat.le_pow_clog (by decide) _)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
