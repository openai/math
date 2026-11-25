import OAI.Hierarchy.DescentCalendarRootProfile

namespace OAI
/-! # Reading both dated private pages from the original numerical stencil and signed ports -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentPaidResidentCount.Reset DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentFallbackPeriod.Projected.Receiver DescentResetHostSize DescentSharedBookScan
open DescentDatedAddressBook CandidateFront DescentResetGates DescentPlainTerminal.Suffix
open DescentSixParty.Chronology DescentPackedWalsh ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
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
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "r" => (Z).k-cc
local notation "Ht" => GroupStage.depthBound D n f g
local notation "J" => 2^cc
local notation "layer" => DescentRecordedRotorLayers.width f cap
variable (paid : input.placement.cap=(calendar.take i).prod*256) {w N K R hm lb tiny bit t : ℕ}
    (a : Receiver input.placement.degree input.placement.cap N B.reset.n (B.reset.k-B.terminals.commonDepth) B.terminals.commonDepth (S.hostSize i) (S.groupCount i) K R M hm lb tiny field (GroupStage.depthBound D n f g) w)
    (E : EstimatorArena) (stencil : StencilBook) (old : StencilBook.Sources)
    (base split hubWidth : ℕ) (ports : Ports input.placement.degree) (oldId : Bank)
    (fee full total pitch groupDigits batches factor : ℕ)
    (primitive : CanonicalTag (2^B.reset.n)→Cell bit) (page : RootPage (B.reset.k-B.terminals.commonDepth) (2^B.reset.n))
local notation "book" => a.issuedBook E stencil old base split hubWidth ports oldId (.lit cap)
  f fee full total pitch (Z).graph (Z).width C groupDigits batches layer factor primitive page
local notation "src" => a.issuedSources E stencil old base split hubWidth ports oldId (.lit cap)
  f fee full total pitch
local notation "head_" => stencil.header base
local notation "catalog_" => RootTemplates.arena (a.headerEnd book) H J M r (Z).n deg
local notation "ceiling" => a.headerEnd book
variable (space : a.PreparedFits (a.issuedBook E stencil old base split hubWidth ports oldId (.lit input.placement.cap) f fee full total pitch B.reset.graph B.reset.width C groupDigits batches (DescentRecordedRotorLayers.width f input.placement.cap) factor primitive page)) (mem before : Memory w) (x : OriginalArrays B input.valid.host field)
    (levels : Fin (S.hostSize i)→ℕ)
local notation "mid" => a.preparedMid book space mem
local notation "vals" => calendarRootWord (t:=t) B x M nextM metaBits calendar paid a book space mem levels
local notation "ownShape" => fun v b j=>(originalColumn (t:=t) B x v b j).val
local notation "contact" => originalCable B x
local notation "count_" => Fintype.card input.V
local notation "slots_" => H*chunks J M

/-- Both original private terms are run by the dated root program. The later
actor bitmap can preserve them through the published low-address frame. -/
theorem calendar_issued_root_pages
    (positive : 0 < M) (physicalHosts : stencil.hosts=H) (extent : H < 2^w)
    (counted : ∀p : Row H J M,old.count.eval mid ((row H J M p).val:Word w)=(count_:Word w))
    (owner : ∀p : Row H J M,(Expr.lookup oldId .row).eval mid ((row H J M p).val:Word w)=(p.1.val:Word w))
    (chart : (head_).chart.Resident mid) (addresses : (head_).depth.Fits w ceiling)
    (priorDepths : old.levels.Fits w ceiling)
    (range : ∀v : Fin H,v.val < count_ → v.val*(stencil.m+1) < old.levels.size)
    (observed : ∀v : Fin H,v.val < count_ → mid (old.levels.base+v.val*(stencil.m+1))=(levels v:Word w))
    (common : ∀v : Fin H,v.val < count_ → cc ≤ levels v ∧ levels v < 2^w)
    (short : ∀v : Fin H,v.val < count_ → levels v-cc+1 < 2^field) (capFits : cap < 2^field)
    (low : Ht+2 < w) (height : Ht+2 ≤ field)
    (reach : ∀j,Accessible ports ((src).tagged j) H J M w ceiling)
    (mounted : Mounted ports x.peers mid J M)
    (markRoom : ∀j,((src).here j).Fits w ceiling ∧ slots_ ≤ ((src).here j).size)
    (wireRoom : ∀j p,((src).signed j p).Fits w ceiling ∧ slots_ ≤ ((src).signed j p).size)
    (localRead : ∀j,Reads ((src).here j) (fun v b=>((ownShape v b j):Cell field)) M mid)
    (tagged : ∀j,Reads ((src).tagged j) (fun v b=>(((ownShape v b j)+1:ℕ):Cell field)) M mid)
    (signedRead : ∀j p,Reads ((src).signed j p)
      (fun v b=>((DescentSignedCableCodec.encode (contact v b j p)).val:Cell field)) M mid)
    (fits : ∀s root j,let pg:=privatePage («r»:=r) (n:=(Z).n) s root
      ;((((book).table pg).2).reads j).Fits w ((catalog_).middle (rootIndex r (2^(Z).n) pg).val))
    (widths : ∀s root,let pg:=privatePage («r»:=r) (n:=(Z).n) s root
      ;M*max (((book).table pg).2.field*((book).table pg).1) ((book).table pg).2.outputBits ≤ w/2)
    (room : a.preparedEnd book < 2^w)
    (keep : ∀address,address < a.preparedEnd book → before address=a.preparedImage book space mem address) :
    ∀s root,Reads (a.privatePageBank book s root) (vals s root) M before := by
  have issued:=a.prepared_peer_pages E stencil old base split hubWidth ports oldId cap f fee full total pitch
    (Z).graph (Z).width C groupDigits batches layer factor primitive page space mem count_ levels ownShape
    x.peers contact positive physicalHosts extent pad counted owner chart addresses priorDepths range observed
    common short capFits low height reach mounted markRoom wireRoom localRead tagged signedRead fits widths
  exact calendar_private_readback B x M nextM metaBits calendar paid a book space mem levels before room keep issued

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
