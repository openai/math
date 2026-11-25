import OAI.Hierarchy.DescentResetPeerGoodInputs

namespace OAI
/-! # The two private reset pages from the same original numerical inputs -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetHostSize
open DescentSixParty.Chronology DescentSixParty DescentResetGates DescentPackedWalsh DescentPlainTerminal.Suffix
open DescentRotorRootPresence DescentSharedLeafLookup DescentRotorPeerIssue
open DescentSharedBookScan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (publicCap f fee full total portPitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n))
local notation "L" => 2^r
local notation "J" => 2^c
local notation "B" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId (.lit publicCap)
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
local notation "src" => a.issuedSources E stencil old stencilBase splitBank hubWidth peers oldId (.lit publicCap)
  f fee full total portPitch
local notation "head" => stencil.header stencilBase
variable (space : a.PreparedFits (a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId (.lit publicCap)
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage)) (mem : Memory w)
local notation "mid" => a.preparedMid B space mem
local notation "ceiling" => a.headerEnd B
local notation "rack" => Expr.lookup oldId .row
local notation "far" => (head).levelAt old.levels rack
local notation "dep" => Expr.branch .lt rack old.count
  (.op .add (.op .sub (Cutoff.level (.lit c) far) (.lit c)) (.lit 1)) (.lit 0)


local notation "rows_" => H*chunks J M
local notation "catalog_" => RootTemplates.arena (a.headerEnd B) H J M r n D
local notation "rank_" => fun v j=>(ranks (a:=r) (Y:=2^n) (D:=D)
  ((B).common a.projectionEnd H) (2^Ht) (Ht+2) mid v j).val

/-- Both private header families are read from the original prepared image. The
same old shape strip supplies the good-root flag, the fallback root test and
all remote shape requests. -/
theorem prepared_peer_pages (count : ℕ) (levels : Fin H→ℕ)
    (shapeWord : Fin H→Fin J→Fin L→ℕ) (peer : Fin H→Fin D→Option (Fin H))
    (wire : Fin H→Fin J→Fin L→Fin (2*cap)→Option (DescentSharedCableNames.Stage.Live D cap))
    (positive : 0 < M) (eqH : stencil.hosts=H) (extent : H < 2^w) (actualHosts : count ≤ H)
    (counted : ∀p : Row H J M,old.count.eval mid ((row H J M p).val:Word w)=(count:Word w))
    (owner : ∀p : Row H J M,(rack).eval mid ((row H J M p).val:Word w)=(p.1.val:Word w))
    (chart : (head).chart.Resident mid) (addresses : (head).depth.Fits w ceiling)
    (physical : old.levels.Fits w ceiling)
    (range : ∀v : Fin H,v.val < count → v.val*(stencil.m+1) < old.levels.size)
    (stored : ∀v : Fin H,v.val < count → mid (old.levels.base+v.val*(stencil.m+1))=(levels v:Word w))
    (common : ∀v : Fin H,v.val < count → c ≤ levels v ∧ levels v < 2^w)
    (tiny : ∀v : Fin H,v.val < count → levels v-c+1 < 2^field) (capRoom : publicCap < 2^field)
    (low : Ht+2 < w) (height : Ht+2 ≤ field)
    (reachable : ∀i,Accessible peers ((src).tagged i) H J M w ceiling)
    (roster : Mounted peers peer mid J M)
    (markFit : ∀i,((src).here i).Fits w ceiling ∧ rows_ ≤ ((src).here i).size)
    (wireFit : ∀i j,((src).signed i j).Fits w ceiling ∧ rows_ ≤ ((src).signed i j).size)
    (localWords : ∀i,Reads ((src).here i) (fun v g=>(shapeWord v g i:Cell field)) M mid)
    (tags : ∀i,Reads ((src).tagged i) (fun v g=>((shapeWord v g i+1:ℕ):Cell field)) M mid)
    (signed : ∀i j,Reads ((src).signed i j) (fun v g=>((DescentSignedCableCodec.encode (wire v g i j)).val:Cell field)) M mid)
    (fits : ∀side root j,let pg:=privatePage (r:=r) (n:=n) side root
      ;((((B).table pg).2).reads j).Fits w ((catalog_).middle (rootIndex r (2^n) pg).val))
    (widths : ∀side root,let pg:=privatePage (r:=r) (n:=n) side root
      ;M*max (((B).table pg).2.field*((B).table pg).1) ((B).table pg).2.outputBits ≤ w/2) :
    let headers:=goodInput c field publicCap count levels (fun v g i=>(shapeWord v g i:Cell field))
    let packets:=fun (_ : Bool) (_ : Code r×Option (Fin (2^n))) v g=>
      (inputs shapeWord peer wire rank_ v g : Packet D L cap n r field)
    ∀s t,Reads (a.privatePageBank B s t)
      (privatePageValue (Ht:=Ht) (board:=board) (packet:=packet) (f:=f) (C:=C) (layerBits:=layerBits)
        headers packets s t) M (a.preparedImage B space mem) := by
  intro headers packets
  apply a.issued_private_words E stencil old stencilBase splitBank hubWidth peers oldId (.lit publicCap)
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage space mem positive
    headers packets fits widths
  · exact a.good_header_inputs E stencil old stencilBase splitBank hubWidth peers oldId publicCap
      f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage space mem
      count levels (fun v g i=>(shapeWord v g i:Cell field)) eqH extent actualHosts counted owner
      chart addresses physical range stored common tiny capRoom markFit localWords
  · intro s root
    exact a.issued_fallback_operands E stencil old stencilBase splitBank hubWidth peers oldId (.lit publicCap)
      f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage space mem
      s root shapeWord peer wire low height reachable roster markFit wireFit localWords tags signed

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
