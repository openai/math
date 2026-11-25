import OAI.Hierarchy.DescentEarlierRootPlacement
import OAI.Hierarchy.DescentNamedRootReindex
import OAI.Hierarchy.DescentResetPeerGoodInputs

namespace OAI
/-! # Transporting the completed root reads along the jointly reindexed receiver -/
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
local notation "shelf" => (roster (Z).graph r Ht).card
local notation "pitch" => H*shelf
local notation "span_" => H*chunks J M
local notation "full" => (A).wire*((A).z*G.b)*cap
variable {bw N K R hm l tiny t bit : ℕ}
  (machine : DescentFallbackPeriod.Projected.Receiver.IndexedRoots (((input.placement)).degree) (((input.placement)).cap) N ((B.reset)).n (((B.reset)).k-(((B.terminals)).commonDepth)) (((B.terminals)).commonDepth) (S.hostSize i) (S.groupCount i) K R M hm l tiny field (GroupStage.depthBound D n f g) bw)
local notation "rc₁" => machine.receiver
variable (E : EstimatorArena) (stencil : StencilBook) (source : StencilBook.Sources)
  (base split hubWidth : ℕ) (ports : Ports (((input.placement)).degree)) (oldId oldHub : Bank)
  (fee total portPitch groupDigits batches factor : ℕ)
  (primitive : CanonicalTag (2^((B.reset)).n)→Cell bit) (page : RootPage (((B.reset)).k-(((B.terminals)).commonDepth)) (2^((B.reset)).n))
local notation "layer₁" => DescentRecordedRotorLayers.width f cap
local notation "book₁" => (rc₁).issuedBook E stencil source base split hubWidth ports oldId (.lit cap)
  f fee full total portPitch (Z).graph (Z).width C groupDigits batches layer₁ factor primitive page
local notation "src₁" => (rc₁).atlasSources E stencil source base split hubWidth ports oldId (.lit cap)
  f fee full total portPitch (Z).graph (Z).width C groupDigits batches layer₁ factor primitive page

variable (measured : Memory bw) (hdr : OriginalHeader B (input.valid.host) ((machine.receiver)) machine.book measured)
  (x : OriginalArrays B (input.valid.host) field) {nbits : ℕ}
local notation "finish₁" => (rc₁).preparedImage machine.book machine.prepared measured
local notation "body₁" => calendar_sender_matrix B M field (rc₁) machine.book machine.prepared measured hdr x
theorem indexed_earlier_placement (bookEq : machine.book=book₁) (sourceEq : machine.sources=src₁)
    (issued : RootPacket B (rc₁) machine.book machine.prepared measured hdr machine.sources x nbits t)
    (area : machine.sources.OperandRoom H J M bw ((rc₁).headerEnd machine.book))
    (price : M*max (field*DescentRotorWindowArchive.count deg (2^r) cap)
      (DescentRotorWindowArchive.output (Z).n (2^r) cap)≤bw/2) :
    Source ((rc₁).gatheredOperand machine.book (DescentOperandRootPull.matrixPage r (Z).n))
      (fun v hi=>encode field (DescentRotorWindowArchive.count deg (2^r) cap) (body₁ v hi)) M finish₁ ∧
    ∀j lo,Source (.lookup (machine.sources.signed lo j) .row)
      (fun v hi=>((DescentSignedCableCodec.encode (originalCable B x v hi lo j)).val:Cell field)) M finish₁ :=by
  rcases machine with ⟨a,b,space,s⟩
  dsimp only at bookEq sourceEq
  subst b
  subst s
  obtain ⟨matrix,signed⟩:=RootPacket.earlier_placement B M field a E stencil source base split hubWidth ports oldId
    fee total portPitch groupDigits batches factor primitive page space measured hdr x issued area price
  refine ⟨matrix,?_⟩
  intro j lo
  exact source_column _ _ (area.ports lo j) _ _ (Nat.le_pow_clog (by decide) _) (signed j lo)
local notation "mid₁" => (rc₁).preparedMid machine.book machine.prepared measured
local notation "rack₁" => Expr.lookup oldId .row
local notation "head₁" => stencil.header base
local notation "roof₁" => (rc₁).headerEnd machine.book

theorem indexed_root_controls (bookEq : machine.book=book₁) (sourceEq : machine.sources=src₁)
    (pop : ℕ) (level : Fin H→ℕ) (eqH : stencil.hosts=H) (extent : H<2^bw) (actualHosts : pop≤H)
    (chart : (head₁).chart.Resident mid₁) (addresses : (head₁).depth.Fits bw roof₁)
    (physical : source.levels.Fits bw roof₁)
    (range : ∀v : Fin H,v.val<pop → v.val*(stencil.m+1)<source.levels.size)
    (stored : ∀v : Fin H,v.val<pop → mid₁ (source.levels.base+v.val*(stencil.m+1))=(level v:Word bw))
    (common : ∀v : Fin H,v.val<pop → cc≤level v ∧ level v<2^bw)
    (short : ∀v : Fin H,v.val<pop → level v-cc+1<2^field)
    (counted : ∀j : Row H J M,source.count.eval mid₁ ((row H J M j).val:Word bw)=(pop:Word bw))
    (owner : ∀j : Row H J M,(rack₁).eval mid₁ ((row H J M j).val:Word bw)=(j.1.val:Word bw))
    (prior : cap<2^field) :
    Source machine.sources.priorCap (fun (_ : Fin H) (_ : Fin J)=>(cap:Cell field)) M mid₁ ∧
    Source machine.sources.relativeDepth (fun (v : Fin H) (_ : Fin J)=>
      (DescentFallbackPeriod.Projected.Receiver.depthDigit cc pop level v:Cell field)) M mid₁ :=by
  rcases machine with ⟨a,b,space,s⟩
  dsimp only at bookEq sourceEq
  subst b
  subst s
  exact a.good_header_controls E stencil source base split hubWidth ports oldId cap f fee full total portPitch
    (Z).graph (Z).width C groupDigits batches layer₁ factor primitive page space measured pop level eqH extent
    actualHosts counted owner chart addresses physical range stored common short prior

end
end Hierarchy.DescentSixParty.ClosedReset.Window

namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver.IndexedRoots
open DescentOperandRootPull
variable {D cap N n r c H G K R M hm lb tiny field Ht w D' cap' n' r' c' H' G' Ht' : ℕ}
    (x : IndexedRoots D cap N n r c H G K R M hm lb tiny field Ht w)
    (degree : D=D') (capacity : cap=cap') (dimension : n=n') (residual : r=r')
    (depth : c=c') (hosts : H=H') (groups : G=G') (height : Ht=Ht')
local notation "y" => x.reindex degree capacity dimension residual depth hosts groups height
theorem placement_banks :
    (y).receiver.gatheredOperand (y).book (matrixPage r' n')=x.receiver.gatheredOperand x.book (matrixPage r n) ∧
    ∀lo:Fin (2^r), ∀j:Fin (2*cap),
      (y).sources.signed (lo.cast (congrArg (2^·) residual)) (j.cast (congrArg (2*·) capacity))=x.sources.signed lo j :=by
  subst_vars
  exact ⟨rfl,fun _ _=>rfl⟩
end Hierarchy.DescentFallbackPeriod.Projected.Receiver.IndexedRoots

end OAI
