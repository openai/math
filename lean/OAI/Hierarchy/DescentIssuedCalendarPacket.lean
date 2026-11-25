import OAI.Hierarchy.DescentCalendarMatrixWidth
import OAI.Hierarchy.DescentCalendarMatrixDigits

namespace OAI
/-! # The measured matrix and original root packet on the same physical receiver -/
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
set_option hygiene false

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
variable (a : Receiver (A).degree (A).cap (2^k) n rr cc HH G K R M h₀ l t field Ht w)
    (st : StencilBook) (old : StencilBook.Sources) (base split width : ℕ)
    (peers : Ports (A).degree) (oldId : Bank) (priorCap : Expr) (pitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet groupsBits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage rr (2^n))
local notation "B" => a.issuedBook E st old base split width peers oldId priorCap f fee full total pitch
  board packet C groupsBits batches layerBits factor primitive bookPage
local notation "src" => a.issuedSources E st old base split width peers oldId priorCap f fee full total pitch
local notation "fallback" => DescentOperandRootPull.fallbackPage rr n
local notation "pg" => DescentOperandRootPull.matrixPage rr n
local notation "rankHeader₀" => (B).rankHeader a.projectionEnd HH (2^cc) M bookPage
local notation "aux" => (B).auxAt a.projectionEnd HH (2^cc) M
local notation "order" => fun x y : Fin L=>st.orderExpr old base split width x.val y.val
local notation "amt" => fun table hdr=>ClosedReset.Recorded.reservationFields E hdr peers HH pitch cc (E.dim-cc)
  table levels total (.lookup oldId .row)

local notation "native" => input.order.trans Fin.valEmbedding
local notation "groups" => Equiv.refl (Fin (S.groupCount i))
local notation "scene" => a.atlasSources E st old base split width peers oldId priorCap f fee full total pitch
  board packet C groupsBits batches layerBits factor primitive bookPage
local notation "staged" sp => IndexedRoots.mk a B sp scene
local notation "im" sp "atWidth" wid => (staged sp).reindex rfl rfl reset.dimension.symm
  (congrArg (fun u=>u-cc) wid) rfl rfl rfl rfl
local notation "ranked" sp "atMemory" mm => fun v j=>(DescentSharedBookScan.ranks (a:=rr) (Y:=2^n) (D:=(A).degree)
  ((B).common a.projectionEnd HH) (2^Ht) (Ht+2) (a.preparedMid B sp mm) v j).val
open DescentPaidResidentCount.Reset

include accepted in
/-- Read the original local and signed arrays from the same prepared book as the issued matrix. -/
theorem issued_calendar_packet (dim : E.dim=reset.reset.k) (sizeDim : h₀+l=E.dim) (ports : D≤pitch)
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
    (μ : DescentGL.Layout (h₀+l)) (sizes : 2^(h₀+l)=G*2^k) (pack : 2^l=M*2^k)
    (sm : cc≤h₀+l) (lowSlots : M*L=2^l)
    (previous : ∀j x,Reads (a.old j x) (fun v b=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed (A) native S input.valid (groups).toEmbedding oldHost x j v b)) (R*M) mem)
    (saved : mem a.saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (priorKey : a.saved.Fits w a.origin) (stencilFit : a.stencil.base+HH*chunks (2^cc) M≤a.origin)
    (stencilRows : HH*chunks (2^cc) M≤a.stencil.size)
    (stencil : PackedFlow.Padded.Published (h:=h₀) (l:=l) M t a.stencil.base oldHost
        (ClosedReset.Recorded.realPanel (reset:=reset) ((sizeDim.trans dim).trans reset.keyWidth) μ nbits t) mem)
    (oldOrder : st.OldOrder old base split width cc μ mem)
    (stHosts : HH=st.hosts) (stLanes : M=st.M) (stBits : 0<st.n) (oldEnd : st.endAddress base≤a.origin)
    (roster : Mounted peers next (a.preparedMid B space mem) (2^cc) M)
    (oldIDs : Accessible peers oldId HH (2^cc) M w (a.headerEnd B))
    (ids : ∀cell : Row HH (2^cc) M,(Expr.lookup oldId .row).eval (a.preparedMid B space mem)
      ((row _ _ _ cell).val:Word w)=(cell.1.val:Word w))
    (header : OriginalHeader reset input.valid.host (im space atWidth (sizeDim.trans dim)).receiver
      (im space atWidth (sizeDim.trans dim)).book mem)
    (area : (scene).OperandRoom HH (2^cc) M w (a.headerEnd B))
    (won : HEq μ reset.frame.basis) (wider : t<field)
    (level : S.groupWidth k tail i+k-cc<2^nbits) (one : 1<2^nbits)
    (mass : 2^(S.groupWidth k tail i+k-cc)*((A).wire*((A).z*gate.b)*(A).cap)<2^nbits)
    (codes : 2*DescentFallbackShapeTable.rows (S.groupWidth k tail i+k-cc) (2^(reset.reset.n))≤2^t)
    (active : 0<(A).wire*((A).z*gate.b)*(A).cap)
    (quotaPaid : 0<quota S.rounds) (degreePaid : 0<32*Nat.clog 2 (2*(A).degree)) :
    let im₀:=im space atWidth (sizeDim.trans dim)
    ∃x : OriginalArrays reset input.valid.host field,
      ClosedReset.Window.RootPacket reset im₀.receiver im₀.book im₀.prepared mem header im₀.sources x nbits t :=by
  let measure:=ClosedReset.Recorded.realPanel (reset:=reset) ((sizeDim.trans dim).trans reset.keyWidth) μ nbits t
  obtain ⟨values,marks,atVertex,atCable,assembled,here,tagged,signed⟩:=
    issued_window_words accepted E a st old base split width peers oldId priorCap pitch board
      packet groupsBits batches layerBits factor primitive bookPage dim sizeDim ports space mem
      trace safe before depthFit contactFit wordBits indexBits outBits hw budget census rankRoom depthRoom extent
      fieldRoom groups native μ sizes pack sm lowSlots previous saved priorKey stencilFit stencilRows
      measure stencil oldOrder stHosts stLanes stBits oldEnd (ranked space atMemory mem) area.remoteShape roster oldIDs ids
      (fun x=>⟨area.localShape x,Nat.le_pow_clog (by decide) _⟩)
      (fun x j=>⟨area.ports x j,Nat.le_pow_clog (by decide) _⟩)
  apply ClosedReset.Window.matrix_packet_at_width reset (staged space) (sizeDim.trans dim) reset.dimension.symm mem
    header accepted wider level one mass codes active quotaPaid degreePaid μ won sm values marks atVertex
  · intro v hi x j
    rw [←PackedFlow.calendar_digits S ctl.base ctl.radix ((sizeDim.trans dim).trans reset.keyWidth) sizes]
    exact atCable v hi x j
  · exact area
  · exact fun _ _=>Nat.le_pow_clog (by decide) _
  · simpa only [←sizeDim] using assembled
  · exact signed
  · exact roster
  · exact here
  · exact tagged

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
