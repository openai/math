import OAI.Hierarchy.DescentIssuedCalendarPacket

namespace OAI
/-! # Consuming the original fixed packet from the reindexed public catalog -/
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
    {h₀ l K R M t field bit w nbits : ℕ}
local notation "Ht" => GroupStage.depthBound D n f g
local notation "G" => S.groupCount i
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
variable (machine : IndexedRoots ((input.placement)).degree ((input.placement)).cap (2^k) n (h₀+l-(reset.terminals.commonDepth)) (reset.terminals.commonDepth) (S.hostSize i) (S.groupCount i) K R M h₀ l t field (GroupStage.depthBound D n f g) w)
local notation "rc" => machine.receiver
variable     (st : StencilBook) (old : StencilBook.Sources) (base split width : ℕ)
    (peers : Ports ((input.placement)).degree) (oldId : Bank) (priorCap : Expr) (pitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet groupsBits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage (h₀+l-(reset.terminals.commonDepth)) (2^n))
local notation "B" => (rc).issuedBook E st old base split width peers oldId priorCap f fee full total pitch
  board packet C groupsBits batches layerBits factor primitive bookPage
local notation "src" => (rc).issuedSources E st old base split width peers oldId priorCap f fee full total pitch
local notation "fallback" => DescentOperandRootPull.fallbackPage rr n
local notation "pg" => DescentOperandRootPull.matrixPage rr n
local notation "header" => (B).rankHeader (rc).projectionEnd HH (2^cc) M bookPage
local notation "aux" => (B).auxAt (rc).projectionEnd HH (2^cc) M
local notation "order" => fun x y : Fin L=>st.orderExpr old base split width x.val y.val
local notation "amt" => fun table hdr=>ClosedReset.Recorded.reservationFields E hdr peers HH pitch cc (E.dim-cc)
  table levels total (.lookup oldId .row)

local notation "native" => input.order.trans Fin.valEmbedding
local notation "groups" => Equiv.refl (Fin (S.groupCount i))
local notation "scene" => (rc).atlasSources E st old base split width peers oldId priorCap f fee full total pitch
  board packet C groupsBits batches layerBits factor primitive bookPage
local notation "output" wid => machine.reindex rfl rfl reset.dimension.symm (congrArg (fun u=>u-cc) wid) rfl rfl rfl rfl
open DescentPaidResidentCount.Reset

include accepted in
theorem indexed_calendar_packet (bookEq : machine.book=B) (srcEq : machine.sources=scene)
    (dim : E.dim=reset.reset.k) (sizeDim : h₀+l=E.dim) (ports : D≤pitch)
    (mem : Memory w)
    (trace : ClosedReset.Recorded.StencilReservationWords (reset:=reset) E dim pitch ports mem)
    (safe : E.Fits w) (before : E.endAddress≤(rc).origin)
    (depthFit : E.depthRows.Fits w ((rc).headerEnd machine.book))
    (contactFit : (ClosedReset.Recorded.firstContactBank E).Fits w ((rc).headerEnd machine.book))
    (wordBits : E.precision≤w) (indexBits : levels+total≤w) (outBits : n<w)
    (hw : 0<wire) (budget : 0<full)
    (census : (A).wire*((A).z*gate.b)*(A).cap<2^(S.censusBits p))
    (rankRoom : HH<2^w) (depthRoom : cc<2^w) (extent : 2^(E.dim-cc)<2^w)
    (fieldRoom : max (max (E.dim-cc) (2^n)) (2^(E.dim-cc))<2^field)
    (μ : DescentGL.Layout (h₀+l)) (sizes : 2^(h₀+l)=G*2^k) (pack : 2^l=M*2^k)
    (sm : cc≤h₀+l) (lowSlots : M*L=2^l)
    (previous : ∀j x,Reads ((rc).old j x) (fun v b=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed (A) native S input.valid (groups).toEmbedding oldHost x j v b)) (R*M) mem)
    (saved : mem (rc).saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (priorKey : (rc).saved.Fits w (rc).origin) (stencilFit : (rc).stencil.base+HH*chunks (2^cc) M≤(rc).origin)
    (stencilRows : HH*chunks (2^cc) M≤(rc).stencil.size)
    (stencil : PackedFlow.Padded.Published (h:=h₀) (l:=l) M t (rc).stencil.base oldHost
        (ClosedReset.Recorded.realPanel (reset:=reset) ((sizeDim.trans dim).trans reset.keyWidth) μ nbits t) mem)
    (oldOrder : st.OldOrder old base split width cc μ mem)
    (stHosts : HH=st.hosts) (stLanes : M=st.M) (stBits : 0<st.n) (oldEnd : st.endAddress base≤(rc).origin)
    (roster : Mounted peers next ((rc).preparedMid machine.book machine.prepared mem) (2^cc) M)
    (oldIDs : Accessible peers oldId HH (2^cc) M w ((rc).headerEnd machine.book))
    (ids : ∀z : Row HH (2^cc) M,(Expr.lookup oldId .row).eval ((rc).preparedMid machine.book machine.prepared mem)
      ((row _ _ _ z).val:Word w)=(z.1.val:Word w))
    («header» : OriginalHeader reset input.valid.host (output (sizeDim.trans dim)).receiver
      (output (sizeDim.trans dim)).book mem)
    (area : machine.sources.OperandRoom HH (2^cc) M w ((rc).headerEnd machine.book))
    (won : HEq μ reset.frame.basis) (wider : t<field)
    (level : S.groupWidth k tail i+k-cc<2^nbits) (one : 1<2^nbits)
    (mass : 2^(S.groupWidth k tail i+k-cc)*((A).wire*((A).z*gate.b)*(A).cap)<2^nbits)
    (codes : 2*DescentFallbackShapeTable.rows (S.groupWidth k tail i+k-cc) (2^(reset.reset.n))≤2^t)
    (active : 0<(A).wire*((A).z*gate.b)*(A).cap)
    (quotaPaid : 0<quota S.rounds) (degreePaid : 0<32*Nat.clog 2 (2*(A).degree)) :
    let im₀:=output (sizeDim.trans dim)
    ∃x : OriginalArrays reset input.valid.host field,
      ClosedReset.Window.RootPacket reset im₀.receiver im₀.book im₀.prepared mem «header» im₀.sources x nbits t :=by
  rcases machine with ⟨a,b,space,s⟩
  dsimp only at bookEq srcEq
  subst b; subst s
  exact issued_calendar_packet accepted E a st old base split width peers oldId priorCap pitch board
    packet groupsBits batches layerBits factor primitive bookPage dim sizeDim ports space mem trace safe before
    depthFit contactFit wordBits indexBits outBits hw budget census rankRoom depthRoom extent fieldRoom μ sizes
    pack sm lowSlots previous saved priorKey stencilFit stencilRows stencil oldOrder stHosts stLanes stBits oldEnd
    roster oldIDs ids «header» area won wider level one mass codes active quotaPaid degreePaid

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
