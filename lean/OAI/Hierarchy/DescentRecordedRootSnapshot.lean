import OAI.Hierarchy.DescentFundedRootObservation
import OAI.Hierarchy.DescentPreparedFallbackWord
import OAI.Hierarchy.DescentRecordedStencilCell
import OAI.Hierarchy.DescentPreparedWindowRead

namespace OAI
/-! # The closed reset's original padded fallback chart on its actual prepared RAM -/
namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentCompiler DescentSIMDLookup DescentGL DescentColonies DescentFallbackPeriod.Projected
open DescentPacking.PackedMatch.Local.Stage DescentIssuedFallbackPanel DescentSharedCableNames.Stage
open DescentSharedBookScan DescentPlainTerminal DescentPlainTerminal.Suffix DescentRelativeContacts
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentRosterOrder DescentFallbackShapeTable
open DescentFallbackRankRAM DescentMixedRouter DescentPackedZip
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail H field p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset cap ctl) (pad : Fintype.card cap.V≤H)
set_option quotPrecheck false
local notation "A" => cap.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "oldKey" => B.order.trans Fin.valEmbedding
local notation "groupKey" => Fin.valEmbedding (n:=S.groupCount i)
local notation "host" => cap.vertex.trans (Fin.castLEEmb pad)
local notation "names" => cableNames k (groupRank groupKey ((host).trans Fin.valEmbedding))
local notation "dep" => GroupStage.depthBound D n f g
local notation "cc" => (T).commonDepth
local notation "dim" => S.groupWidth k tail i+k
local notation "r" => ((Z).k-cc)
local notation "L" => 2^(dim-cc)
local notation "fit" => B.frame.enough.trans (Nat.sub_le ..)
local notation "here" => donor digits B.frame.basis fit
local notation "Y" => 2^(Z).n
local notation "short₀" => fun (t : (Z).Fallback) => (shortName cc ((T).code t)).2
local notation "near₀" => hostRoster A ((host).trans Fin.valEmbedding)
local notation "factor" => 32*Nat.clog 2 (2*(A).degree)
local notation "full" => (A).wire*((A).z*G.b)*(A).cap
local notation "shapeAt" => ClosedReset.Recorded.originalCell (reset:=B)
variable {N K Rep M hm lowBits tiny w : ℕ}
variable (a : Receiver cap.placement.degree cap.placement.cap N B.reset.n (B.reset.k-B.terminals.commonDepth) B.terminals.commonDepth H (S.groupCount i) K Rep M hm lowBits tiny field (GroupStage.depthBound D n f g) w)
    (book : RootBook B.reset.n (B.reset.k-B.terminals.commonDepth) cap.placement.degree (2^(B.reset.k-B.terminals.commonDepth)) cap.placement.cap field) (space : a.PreparedFits book) (mem : Memory w)
local notation "chart" => book.common a.projectionEnd H
local notation "before" => a.preparedMid book space mem

/-- Bounds on actual old banks, and the fixed four numerical parameters of the
same root catalog. Both old masks are read before any root work is performed. -/
structure OriginalHeader : Prop where
  degree : book.fallbackDegree=factor
  hubBits : book.hubBits=g
  loadBits : book.loadBits=f
  list : book.shapes=2^dep
  peerRoom : book.previousNeighbors.Fits w a.origin
  hubRoom : book.previousHubs.Fits w a.origin
  peerSlots : H*(A).degree≤book.previousNeighbors.size
  hubSlots : H≤book.previousHubs.size
  hosts : H<2^w
  ports : (A).degree+1<2^w
  old : ∀u (j : Fin (A).degree),mem (book.previousNeighbors.base+((host u).val*(A).degree+j.val))=
    (hostDigit host (near₀ u j):Word w)
  hubs : ∀u,mem (book.previousHubs.base+(host u).val)=(((A).hub u).toNat:Word w)
  word : 0<w
  height : dep+2≤w
  available : ∀t : (Z).Fallback,∀k z,z∈DescentFallbackLeafScan.localShape r factor g f (short₀ t) k→shapeNumber z+1<2^w
  encoded : ∀t : (Z).Fallback,shapeNumber (short₀ t)<2^w
  signedBits : DescentSignedCableCodec.width (A).degree (A).cap≤field
  rankBits : dep+2≤field

/-- The returned old-window arrays share the true sender's numeric vertex ID in
every real cell. Padded rows retain their original emitted values. -/
structure OriginalArrays (field : ℕ) where
  word : Host (Fin (S.groupCount i)) cap.V k→ℕ
  stencil : Fin H→Block cc→Fin L→ℕ
  marks : Fin H→Block cc→Fin L→Fin (2*(A).cap)→Option (Live (A).degree (A).cap)
  peers : Fin H→Fin (A).degree→Option (Fin H)
  peerRead : ∀u j,peers (host u) j=(near₀ u j).map host
  fits : ∀u,word u+1<2^field
  onWire : ∀s (e : Grain A),word (home A (endSite A s e))=ClosedReset.Window.signedStemWord B s (home A (endSite A s e))
  localRead : ∀v hi lo,stencil (host v) hi lo=word (here v hi lo)
  markRead : ∀v hi lo j,marks (host v) hi lo j=signedPanel A oldKey S cap.valid names (here v hi lo) j
  shape : ∀v hi lo,word (here v hi lo)/2=Stencil.shapeCode (dim-cc) Y
    (fieldsRelative cc (shapeAt v ((rearrange B.frame.basis).symm (join fit hi lo))))

def root_snapshot (hdr : OriginalHeader B pad a book mem) (x : OriginalArrays B pad field) :
    PaddedSnapshot B pad field :=by
  have build:=(a.prepared_shared book space mem (false,.inr (⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩,none)))
  have lim:=book.limits a.projectionEnd H (2^cc) M
  have top : a.origin≤a.headerEnd book:=a.origin_le_projection.trans (lim.1.trans (lim.2.1.trans lim.2.2))
  have widen {b : Bank} (f : b.Fits w a.origin) : b.Fits w (a.headerEnd book):=⟨f.1,f.2.1,f.2.2.trans top⟩
  have common:=a.prepared_room book space le_rfl space.literals (widen hdr.peerRoom) (widen hdr.hubRoom)
    hdr.peerSlots hdr.hubSlots hdr.hosts hdr.ports
  have original (b : Bank) (bankFit : b.Fits w a.origin) (j : ℕ) (valid : j<b.size) :
      before (b.base+j)=mem (b.base+j) :=
    a.prepared_lower book space mem _ ((Nat.add_lt_add_left valid _).trans_le bankFit.2.2)
  have rows:B.frame.Roster («Z»:=B.reset) («T»:=B.terminals) (pos:=_) (ix:=_) (hub:=_) (g:=g) ((host).trans Fin.valEmbedding) (A).near (Z).n f full (A).wire (quota S.rounds)
      (fun v u j=>((A).resetFlow digits v u j:ℝ)) (A).degree ((A).resetLoad digits) := by
    have ids : (host).trans Fin.valEmbedding = cap.vertex.trans Fin.valEmbedding := by
      ext v
      rfl
    rw [ids]
    simpa only [PackedFlow.mutual_near A] using ClosedReset.Recorded.old_roster (reset:=B)
  refine ⟨(Z).n,f,full,(A).wire,quota S.rounds,(A).resetLoad digits,(fun v u j=>((A).resetFlow digits v u j:ℝ)),rows,
    w,chart,before,a.headerEnd book,build.1,common,?_,x.peers,x.peerRead,?_,?_,hdr.word,hdr.height,
    hdr.available,hdr.encoded,x.word,x.fits,?_,hdr.signedBits,hdr.rankBits,?_,x.stencil,x.marks,x.localRead,x.markRead⟩
  · simpa only [hdr.degree,hdr.hubBits,hdr.loadBits,hdr.list] using build.2.1
  · intro u j
    have inside : (host u).val*(A).degree+j.val<H*(A).degree :=by
      simpa only [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (host u,j)).isLt
    exact (original _ hdr.peerRoom _ (inside.trans_le hdr.peerSlots)).trans (hdr.old u j)
  · intro u
    exact (original _ hdr.hubRoom _ ((host u).isLt.trans_le hdr.hubSlots)).trans (hdr.hubs u)
  · exact x.onWire
  · intro v hi lo
    simpa only [ClosedReset.Recorded.originalCell,PackedFlow.mutual_near A] using x.shape v hi lo

theorem root_snapshot_input (hdr : OriginalHeader B pad a book mem) (x : OriginalArrays B pad field)
    (v : Fin H) (hi : Block cc) :
    (root_snapshot B pad a book space mem hdr x).packed v hi =
      DescentFallbackPeriod.encodePacket (DescentFallbackPeriod.inputs (field:=field) x.stencil x.peers x.marks
        (fun h j=>(ranks (a:=r) («Y»:=Y) (D:=(A).degree) chart (2^dep) (dep+2) before h j).val) v hi) :=rfl

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
