import OAI.Hierarchy.DescentReservedMatrixRow
import OAI.Hierarchy.DescentOperandPreparedPackets
import OAI.Hierarchy.DescentRecordedRootBook
import OAI.Hierarchy.DescentPreparedReservations

namespace OAI
/-! # The funded matrix packet in the original good-root gather -/
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

/-- The original signed comparison uses the cyclic exchange's inverse GL coordinates. -/
def matrixBefore {d c : ℕ} (μ : DescentGL.Layout d) (small : c≤d) (g : Block c) (i j : Block (d-c)) : Bool :=
  decide ((rearrange μ).symm (DescentIssuedFallbackPanel.join small g i)<(rearrange μ).symm (DescentIssuedFallbackPanel.join small g j))

private theorem saved_order {w H M c m : ℕ} (st : StencilBook) (old : StencilBook.Sources)
    (base split width : ℕ) (μ : DescentGL.Layout m) (small : c≤ m) (mem : Memory w)
    (state : st.OldOrder old base split width c μ mem) (hosts : H=st.hosts) (lanes : M=st.M)
    (i j : Block (m-c)) :
    Source (st.orderExpr old base split width i.val j.val)
      (fun (_:Fin H) (b:Block c)=>if matrixBefore μ small b i j then (1:Cell st.n) else 0) M mem := by
  subst H
  subst M
  simpa only [matrixBefore,decide_eq_true_eq] using state.read small i j

private theorem widen_bit {a field : ℕ} (ha : 0<a) (b : Bool) :
    DescentRootOrderCast.widen (b:=field) (if b then (1:Cell a) else 0)=(b.toNat:Cell field) := by
  have big : 1<2^a:=Nat.one_lt_two_pow ha.ne'
  cases b <;> simp [DescentRootOrderCast.widen,Nat.mod_eq_of_lt big]

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

include accepted in
/-- The original matrices and local and signed window reads on the root prefix. -/
theorem issued_window_words (dim : E.dim=reset.reset.k) (sizeDim : h₀+l=E.dim) (ports : D≤pitch)
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
    (priorKey : a.saved.Fits w a.origin) (stencilFit : a.stencil.base+HH*chunks (2^cc) M≤a.origin)
    (stencilRows : HH*chunks (2^cc) M≤a.stencil.size)
    (code : input.V→Block cc→Fin L→Cell t)
    (stencil : PackedFlow.Padded.Published (h:=h₀) (l:=l) M t a.stencil.base oldHost code mem)
    (oldOrder : st.OldOrder old base split width cc μ mem)
    (stHosts : HH=st.hosts) (stLanes : M=st.M) (stBits : 0<st.n) (oldEnd : st.endAddress base≤a.origin)
    (rank : Fin HH→Fin (DescentSharedBookScan.width rr (2^n) (A).degree)→ℕ)
    (addressable : ∀x,Accessible peers ((src).tagged x) HH (2^cc) M w (a.headerEnd B))
    (roster : Mounted peers next (a.preparedMid B space mem) (2^cc) M)
    (oldIDs : Accessible peers oldId HH (2^cc) M w (a.headerEnd B))
    (ids : ∀z : Row HH (2^cc) M,(Expr.lookup oldId .row).eval (a.preparedMid B space mem)
      ((row _ _ _ z).val:Word w)=(z.1.val:Word w))
    (localFit : ∀x,((src).here x).Fits w (a.headerEnd B) ∧ HH*chunks (2^cc) M≤((src).here x).size)
    (markFit : ∀x j,((src).signed x j).Fits w (a.headerEnd B) ∧ HH*chunks (2^cc) M≤((src).signed x j).size) :
    ∃(values : Fin HH→Block cc→Fin L→Cell t)
      (marks : Fin HH→Block cc→Fin L→Fin (2*(A).cap)→Option (Live (A).degree (A).cap)),
      (∀v hi x,values (oldHost v) hi x=code v hi x) ∧
      (∀v hi x j,marks (oldHost v) hi x j=signedPanel (A) native S input.valid
        (Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) ((oldHost).trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups sizes) μ sm v hi x) j) ∧
      (∀j,Source ((a.atlasSources E st old base split width peers oldId priorCap f fee full total pitch
        board packet C groupsBits batches layerBits factor primitive bookPage).matrixRow HH j)
        (fun v hi=>RootSources.paddedRow (fun u g x=>(values u g x).val) next marks rank
          (fun _=>matrixBefore μ sm) paid v hi j) M (a.preparedMid B space mem)) ∧
      (∀x,Reads ((src).here x) (fun v hi=>((values v hi x).val:Cell field)) M (a.preparedMid B space mem)) ∧
      (∀x,Reads ((src).tagged x) (fun v hi=>((values v hi x).val+1:Cell field)) M (a.preparedMid B space mem)) ∧
      ∀j x,Reads ((src).signed x j) (fun v hi=>((DescentSignedCableCodec.encode (marks v hi x j)).val:Cell field))
        M (a.preparedMid B space mem) := by
  let mid:=a.preparedMid B space mem
  let castOrder:=fun x y : Fin L=>Expr.lookup (DescentRootOrderCast.bank ((B).castAt a.projectionEnd HH (2^cc) M) st.n M) (order x y)
  have compare (x y : Fin L) : Source (castOrder x y) (fun (_:Fin HH) hi=>
      ((matrixBefore μ sm hi x y).toNat:Cell field)) M mid := by
    have read:=saved_order st old base split width μ sm mem oldOrder stHosts stLanes x y
    have narrow:=a.prepared_comparison B space bookPage mem (show (B).originalBits=some st.n from rfl)
      (order x y) (ProtocolRAMGeneratedWrite.fits_mono _ oldEnd (oldOrder.fits x y)) _ read
    simpa only [widen_bit stBits] using narrow
  have reservations (q j : Fin (A).degree) (u : Fin 6) : Source
      (amt aux header q j u) (fun v (_:Block cc)=>paid v q j u) M mid :=
    accepted.prepared_reservation_sources (E:=E) dim pitch ports a B space bookPage mem trace safe before
      rfl rfl depthFit contactFit wordBits indexBits outBits hw budget census peers oldId (.lookup oldId .row)
      oldIDs roster ids rankRoom depthRoom extent fieldRoom q j u (by rw [sizeDim])
  obtain ⟨values,marks,here,tagged,signed,atVertex,atCable⟩:=
    prepared_mid_window_read_rows (A) native S input.valid groups oldHost a B space μ sizes pack sm lowSlots
      mem previous saved priorKey stencilFit stencilRows code stencil
  let chosen:=a.rootSources peers castOrder (amt aux header) (src).priorCap (src).relativeDepth
  have assembled:=chosen.matrix_sources (fun v hi x=>(values v hi x).val) next marks rank
    (fun _=>matrixBefore μ sm) paid (a.headerEnd B) mid addressable roster localFit markFit
    here (fun x => by
      have h : Reads (chosen.tagged x) (fun v hi => ((values v hi x).val : Cell field) + 1) M mid := tagged x
      simpa only [Nat.cast_add, Nat.cast_one] using h)
    (fun x j=>signed j x) compare reservations
  exact ⟨values,marks,atVertex,atCable,assembled,here,tagged,signed⟩

include accepted in
/-- The saved matrix input includes the actual old socket order, funded peer reservation
words, the signed old cables, and the previous local and adjacent shape words. -/
theorem issued_matrix_packet (dim : E.dim=reset.reset.k) (sizeDim : h₀+l=E.dim) (ports : D≤pitch)
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
    (rank : Fin HH→Fin (DescentSharedBookScan.width rr (2^n) (A).degree)→ℕ)
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
      (DescentRotorWindowArchive.output n L (A).cap)≤w/2) :
    ∃(values : Fin HH→Block cc→Fin L→Cell t)
      (marks : Fin HH→Block cc→Fin L→Fin (2*(A).cap)→Option (Live (A).degree (A).cap)),
      Source (a.gatheredOperand B pg) (fun v b=>encode field _ (RootSources.paddedRow
        (fun u hi x=>(values u hi x).val) next marks rank (fun _=>matrixBefore μ sm) paid v b)) M
        (a.preparedImage B space mem) ∧
      (∀v hi x,values (oldHost v) hi x=code v hi x) ∧
      (∀v hi x j,marks (oldHost v) hi x j=signedPanel (A) native S input.valid
        (Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) ((oldHost).trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups sizes) μ sm v hi x) j) ∧
      (Ht+2<w → Ht+2≤field →
        (∀j,(((B).table fallback).2.reads j).Fits w
          ((RootTemplates.arena (a.headerEnd B) HH (2^cc) M rr n (A).degree).middle
            (rootIndex rr (2^n) fallback).val)) →
        M*max (field*inputCount (A).degree L (A).cap n rr) ((B).table fallback).2.outputBits≤w/2 →
        let ranked:=fun v j=>(DescentSharedBookScan.ranks (a:=rr) (Y:=2^n) (D:=(A).degree)
          ((B).common a.projectionEnd HH) (2^Ht) (Ht+2) (a.preparedMid B space mem) v j).val
        Source (a.gatheredOperand B fallback)
          (fun v hi=>encodePacket (inputs (field:=field) (fun u b x=>(values u b x).val) next marks ranked v hi))
          M (a.preparedImage B space mem)) ∧
      (∀j,Source ((a.atlasSources E st old base split width peers oldId priorCap f fee full total pitch
        board packet C groupsBits batches layerBits factor primitive bookPage).matrixRow HH j)
        (fun v hi=>RootSources.paddedRow (fun u g x=>(values u g x).val) next marks rank
          (fun _=>matrixBefore μ sm) paid v hi j) M (a.preparedMid B space mem)) ∧
      (∀x,Reads ((src).here x) (fun v hi=>((values v hi x).val:Cell field)) M (a.preparedMid B space mem)) ∧
      (∀x,Reads ((src).tagged x) (fun v hi=>((values v hi x).val+1:Cell field)) M (a.preparedMid B space mem)) ∧
      ∀j x,Reads ((src).signed x j) (fun v hi=>((DescentSignedCableCodec.encode (marks v hi x j)).val:Cell field))
        M (a.preparedMid B space mem) := by
  let mid:=a.preparedMid B space mem
  obtain ⟨values,marks,atVertex,atCable,assembled,here,tagged,signed⟩:=
    issued_window_words accepted E a st old base split width peers oldId priorCap pitch board packet
      groupsBits batches layerBits factor primitive bookPage dim sizeDim ports space mem trace safe before depthFit
      contactFit wordBits indexBits outBits hw budget census rankRoom depthRoom extent fieldRoom groups native
      μ sizes pack sm lowSlots previous saved priorKey ((Nat.add_le_add_left stencilRows _).trans stencilFit.2.2) stencilRows code stencil oldOrder stHosts stLanes
      stBits oldEnd rank addressable roster oldIDs ids localFit markFit
  refine ⟨values,marks,?_,atVertex,atCable,?_,assembled,here,tagged,signed⟩
  swap
  · intro low wide operands packedFallback ranked
    exact a.issued_fallback_packet E st old base split width peers oldId priorCap
      f fee full total pitch board packet C groupsBits batches layerBits factor primitive bookPage
      space mem false (DescentOperandRootPull.defaultRoot rr,none) (fun v hi x=>(values v hi x).val)
      next marks low wide addressable roster localFit markFit here (fun x => by simpa only [Nat.cast_add,Nat.cast_one] using tagged x)
      (fun x j=>signed j x) operands packedFallback
  apply a.gathered_source B space mem pg _ operandFit packed
  intro j
  have actual:=(src).reserved_matrix_reads (field:=field) board packet f Ht C groupsBits batches layerBits primitive
    HH factor width old.roster old.hubs a.projectionEnd (2^cc) M st.n (amt) bookPage false
    (DescentOperandRootPull.defaultRoot rr) j
  change Source (((B).good false (DescentOperandRootPull.defaultRoot rr) (.inl false)).2.reads j) _ M mid
  exact (congrArg (fun opcode : Expr => Source opcode
    (fun v hi => RootSources.paddedRow (fun u g x => (values u g x).val) next marks rank
      (fun _ => matrixBefore μ sm) paid v hi j) M mid) actual).mpr (assembled j)

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
