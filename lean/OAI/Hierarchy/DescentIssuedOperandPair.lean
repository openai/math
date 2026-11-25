import OAI.Hierarchy.DescentIssuedMatrixPacket
import OAI.Hierarchy.DescentPreparedOperandPairRead

namespace OAI
/-! # Retile the two reached root packets on the same published parent directory -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetHostSize
open DescentSixParty DescentSixParty.Chronology DescentResetGates DescentPackedWalsh DescentPlainTerminal.Suffix
open DescentGL DescentColonies DescentCompiler DescentIssuedFallbackPanel DescentSharedLeafLookup
open DescentGLPacked DescentGLPacked.BankImage DescentGLPacked.BankImage.SignedFields
open DescentSharedCableNames.Stage DescentGroupPeerOrder DescentStageEdgeReceipt DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {gate : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
    {input : Reached W gate q ε S k i z D wire hist} {ctl : ResetRates gate S k D n h C f g cut tail}
    {reset : ClosedReset input ctl} (accepted : reset.Recorded p) (E : EstimatorArena)
    {h₀ l G K R M t field Ht bit w : ℕ}
local notation "A" => input.placement
local notation "HH" => S.hostSize i
local notation "cc" => reset.terminals.commonDepth
local notation "rr" => h₀+l-cc
local notation "L" => 2^rr
local notation "levels" => Nat.clog 2 (E.dim+2)
local notation "total" => E.dim+S.censusBits p
local notation "fee" => quota S.rounds
local notation "full" => wire*(z*gate.b)*(A).cap
local notation "oldHost" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "next" => PackedFlow.Padded.roster (D:=(A).degree) (A) (ClosedReset.Recorded.oldName input) input.valid.host
local notation "paid" => ClosedReset.Recorded.paddedValue (b:=field) cc (E.dim-cc) next
  (ClosedReset.Recorded.oldDepth reset) (ClosedReset.Recorded.oldWidth reset)
variable (a : Receiver input.placement.degree input.placement.cap (2^k) n
      (h₀ + l - reset.terminals.commonDepth) reset.terminals.commonDepth (S.hostSize i) G K R M h₀ l t field Ht w)
    (st : StencilBook) (old : StencilBook.Sources) (base split width : ℕ)
    (peers : Ports input.placement.degree) (oldId : Bank) (priorCap : Expr) (pitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet groupsBits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage (h₀ + l - reset.terminals.commonDepth) (2^n))
local notation "B" => a.issuedBook E st old base split width peers oldId priorCap f fee full total pitch
  board packet C groupsBits batches layerBits factor primitive bookPage
local notation "src" => a.issuedSources E st old base split width peers oldId priorCap f fee full total pitch
local notation "fallback" => DescentOperandRootPull.fallbackPage rr n
local notation "pg" => DescentOperandRootPull.matrixPage rr n
local notation "header" => (B).rankHeader a.projectionEnd HH (2^cc) M bookPage
local notation "aux" => (B).auxAt a.projectionEnd HH (2^cc) M
local notation "order" => fun x y : Fin L=>st.orderExpr old base split width x.val y.val
local notation "amt" => fun table hdr=>ClosedReset.Recorded.reservationFields E hdr peers HH pitch cc (E.dim-cc)
  table levels total (.lookup oldId .row)


local notation "ranked" => fun s m v j=>(DescentSharedBookScan.ranks (a:=rr) (Y:=2^n) (D:=(A).degree)
  ((B).common a.projectionEnd HH) (2^Ht) (Ht+2) (a.preparedMid B s m) v j).val
local notation "physical" => fun ptr receivers groups after =>
  DescentOperandRootPull.preparedPair a (B) ptr receivers groups (2^k) after

include accepted in
/-- Both packed input vectors were issued by the same previous signed/stencil run.
All matrix entries, fallback ranks and old endpoint words refer to the same host ordinals. -/
theorem issued_operand_pair (dim : E.dim=reset.reset.k) (sizeDim : h₀+l=E.dim) (ports : D≤pitch)
    (space : a.PreparedFits B) (mem : Memory w)
    (trace : ClosedReset.Recorded.StencilReservationWords (reset:=reset) E dim pitch ports mem)
    (safe : E.Fits w) (before : E.endAddress≤a.origin)
    (depthFit : E.depthRows.Fits w (a.headerEnd B))
    (contactFit : (ClosedReset.Recorded.firstContactBank E).Fits w (a.headerEnd B))
    (wordBits : E.precision≤w) (indexBits : levels+total≤w) (outBits : n<w)
    (hw : 0<wire) (budget : 0<full)
    (census : (A).wire*((A).z*gate.b)*(A).cap<2^(S.censusBits p))
    (rankRoom : HH<2^w) (depthRoom : cc<2^w) (extent : 2^(E.dim-cc)<2^w)
    (fieldRoom : max (max (E.dim-cc) (2^n)) (2^(E.dim-cc))<2^field)
    (groups : Fin (S.groupCount i)≃Fin G) (native : W.graph.Edge↪ℕ)
    (μ : DescentGL.Layout (h₀+l)) (sizes : 2^(h₀+l)=G*2^k) (pack : 2^l=M*2^k)
    (sm : cc≤h₀+l) (lowSlots : M*L=2^l)
    (previous : ∀j x,Reads (a.old j x) (fun v b=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed (A) native S input.valid groups.toEmbedding oldHost x j v b)) (R*M) mem)
    (saved : mem a.saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (priorKey : a.saved.Fits w a.origin) (stencilFit : a.stencil.Fits w a.origin)
    (stencilRows : HH*chunks (2^cc) M≤a.stencil.size)
    (code : input.V→Block cc→Fin L→Cell t)
    (stencil : PackedFlow.Padded.Published (h:=h₀) (l:=l) M t a.stencil.base oldHost code mem)
    (oldOrder : st.OldOrder old base split width cc μ mem)
    (stHosts : HH=st.hosts) (stLanes : M=st.M) (stBits : 0<st.n) (oldEnd : st.endAddress base≤a.origin)
    (addressable : ∀x,Accessible peers ((src).tagged x) HH (2^cc) M w (a.headerEnd B))
    (roster : Mounted peers next (a.preparedMid B space mem) (2^cc) M)
    (oldIDs : Accessible peers oldId HH (2^cc) M w (a.headerEnd B))
    (ids : ∀z : Row HH (2^cc) M,(Expr.lookup oldId .row).eval (a.preparedMid B space mem)
      ((row _ _ _ z).val:Word w)=(z.1.val:Word w))
    (localFit : ∀x,((src).here x).Fits w (a.headerEnd B) ∧ HH*chunks (2^cc) M≤((src).here x).size)
    (markFit : ∀x j,((src).signed x j).Fits w (a.headerEnd B) ∧ HH*chunks (2^cc) M≤((src).signed x j).size)
    (operandFit : ∀j,(((B).table pg).2.reads j).Fits w
      ((RootTemplates.arena (a.headerEnd B) HH (2^cc) M rr n (A).degree).middle (rootIndex rr (2^n) pg).val))
    (packed : M*max (field*(DescentRotorWindowArchive.count (A).degree L (A).cap))
      (DescentRotorWindowArchive.output n L (A).cap)≤w/2)
    (shortRanks : Ht+2<w) (rankFields : Ht+2≤field)
    (fallbackFit : ∀j,(((B).table fallback).2.reads j).Fits w
      ((RootTemplates.arena (a.headerEnd B) HH (2^cc) M rr n (A).degree).middle (rootIndex rr (2^n) fallback).val))
    (fallbackPacked : M*max (field*inputCount (A).degree L (A).cap n rr) ((B).table fallback).2.outputBits≤w/2)
    (start ptr receivers targetGroups targetLanes : ℕ) (after : Memory w) (ds : targetGroups*2^k=2^cc)
    (kept : ∀z,z<a.preparedEnd B → after z=a.preparedImage B space mem z)
    (low : a.preparedEnd B≤ start) (owner : Fin receivers→Fin HH) (oldLanes : 0<M) (hNew : 0<targetLanes)
    (directory : DescentResetStemKeyReindex.Directory ptr owner after)
    (dirFit : ptr+DescentDyadicSpan.span receivers≤ start)
    (room : (physical ptr receivers targetGroups targetLanes).endAddress start<2^w) :
    let device:=physical ptr receivers targetGroups targetLanes
    ∃(values : Fin HH→Block cc→Fin L→Cell t)
      (marks : Fin HH→Block cc→Fin L→Fin (2*(A).cap)→Option (Live (A).degree (A).cap)),
      (device.program start w).Exec after (device.image start after) (device.time start w) ∧
      CheapCode (device.program start w) ∧
      (∀j x,(device.src start false j x).Fits w (device.endAddress start) ∧
        Source (device.src start false j x)
          (fun v hi=>inputs (field:=field) (fun u b i=>(values u b i).val) next marks (ranked space mem)
            (owner v) (Fin.cast ds (finProdFinEquiv (hi,x))) (number.symm j)) targetLanes (device.image start after)) ∧
      (∀j x,(device.src start true j x).Fits w (device.endAddress start) ∧
        Source (device.src start true j x)
          (fun v hi=>RootSources.paddedRow (fun u b i=>(values u b i).val) next marks (ranked space mem)
            (fun _=>matrixBefore μ sm) paid (owner v) (Fin.cast ds (finProdFinEquiv (hi,x))) j)
          targetLanes (device.image start after)) ∧
      (∀z,z<start ∨ device.endAddress start≤z → device.image start after z=after z) ∧
      (∀v hi x,values (oldHost v) hi x=code v hi x) ∧
      ∀v hi x j,marks (oldHost v) hi x j=signedPanel (A) native S input.valid
        (Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) ((oldHost).trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups sizes) μ sm v hi x) j := by
  intro device
  obtain ⟨values,marks,matrix,atVertex,atCable,other,_originalRows⟩:=
    issued_matrix_packet accepted E a st old base split width peers oldId priorCap pitch board packet groupsBits
      batches layerBits factor primitive bookPage dim sizeDim ports space mem trace safe before depthFit contactFit
      wordBits indexBits outBits hw budget census rankRoom depthRoom extent fieldRoom groups native μ sizes pack sm
      lowSlots previous saved priorKey stencilFit stencilRows code stencil oldOrder stHosts stLanes stBits oldEnd
      (ranked space mem) addressable roster oldIDs ids localFit markFit operandFit packed
  have fromFallback:=other shortRanks rankFields fallbackFit fallbackPacked
  let oldShape:=fun v hi j=>(values v hi j).val
  let fall:=fun v hi j=>inputs (field:=field) oldShape next marks (ranked space mem) v hi (number.symm j)
  let mat:=RootSources.paddedRow oldShape next marks (ranked space mem) (fun _=>matrixBefore μ sm) paid
  obtain ⟨run,text,left,right,frame⟩:=
    DescentOperandRootPull.prepared_pair_read a B start ptr receivers targetGroups (2^k) targetLanes
      space mem after ds fall mat fromFallback matrix kept low owner oldLanes hNew (Nat.two_pow_pos _)
      directory dirFit room
  exact ⟨values,marks,run,text,left,right,frame,atVertex,atCable⟩

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
