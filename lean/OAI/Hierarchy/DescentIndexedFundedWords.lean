import OAI.Hierarchy.DescentPreparedFallbackWord
import OAI.Hierarchy.DescentIndexedRootState
import OAI.Hierarchy.DescentFundedJobCalendar
import OAI.Hierarchy.DescentNamedPrivatePageRooms

namespace OAI
/-! # Original gathered root words retain their addresses through receiver reindexing -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver

namespace IndexedRoots
variable {D cap N n r c H G K R M hm lb tiny field Ht w : ℕ}
  {D' cap' n' r' c' H' G' Ht' : ℕ}
variable (x : IndexedRoots D cap N n r c H G K R M hm lb tiny field Ht w)
  (degree : D=D') (capacity : cap=cap') (dimension : n=n') (residual : r=r')
  (depth : c=c') (hosts : H=H') (groups : G=G') (height : Ht=Ht')



open DescentSharedBookScan DescentSIMDLookup DescentPackedColony DescentResetHostSize DescentPackedZip
open scoped Classical Fin.CommRing
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
local notation "J" => 2^c
local notation "L" => 2^r
local notation "a" => x.receiver
local notation "B" => x.book
local notation "space" => x.prepared
local notation "cols" => x.sources
local notation "src" m:arg => (a).preparedMid B space m

def FallbackWords : Prop :=
  ∀(mem : Memory w) (s : Bool) (root : Code r×Option (Fin (2^n)))
    (here : Fin H→Fin J→Fin L→ℕ) (peer : Fin H→Fin D→Option (Fin H))
    (marks : Fin H→Fin J→Fin L→Fin (2*cap)→Option (DescentSharedCableNames.Stage.Live D cap)),
    Ht+2<w → Ht+2≤field → (cols).OperandRoom H J M w ((a).headerEnd B) →
    Mounted (cols).peers peer (src mem) J M →
    (∀i,H*chunks J M≤((cols).here i).size) → (∀i j,H*chunks J M≤((cols).signed i j).size) →
    (∀i,Reads ((cols).here i) (fun v g=>(here v g i:Cell field)) M (src mem)) →
    (∀i,Reads ((cols).tagged i) (fun v g=>((here v g i+1:ℕ):Cell field)) M (src mem)) →
    (∀i j,Reads ((cols).signed i j) (fun v g=>((DescentSignedCableCodec.encode (marks v g i j)).val:Cell field)) M (src mem)) →
    x.PageRooms →
    let rank:=fun v j=>(ranks («a»:=r) (Y:=2^n) (D:=D) ((B).common (a).projectionEnd H) (2^Ht) (Ht+2) (src mem) v j).val
    Source ((a).gatheredOperand B (s,.inr root)) (fun h g=>encodePacket
      (inputs (field:=field) here peer marks rank h g)) M ((a).preparedImage B space mem)

theorem reindex_words (ok : x.FallbackWords) :
    (x.reindex degree capacity dimension residual depth hosts groups height).FallbackWords:=by
  subst_vars;exact ok

theorem reindex_root_room (old : x.sources.OperandRoom H J M w (x.receiver.headerEnd x.book)) :
    let y:=x.reindex degree capacity dimension residual depth hosts groups height
    y.sources.OperandRoom H' (2^c') M w (y.receiver.headerEnd y.book):=by
  subst_vars;exact old

theorem reindex_span (colsFit :
    (∀i,H*chunks J M≤((cols).here i).size) ∧ ∀i j,H*chunks J M≤((cols).signed i j).size) :
    let y:=x.reindex degree capacity dimension residual depth hosts groups height
    (∀i,H'*chunks (2^c') M≤(y.sources.here i).size) ∧ ∀i j,H'*chunks (2^c') M≤(y.sources.signed i j).size:=by
  subst_vars;exact colsFit

open DescentFundedCensus DescentSixParty.ClosedReset.Window
theorem reindex_funded_bank
    (dst : DescentFundedCensus.Ports r n) (physical : ∀s t,dst.bank s t=(a).gatheredOperand B (s,.inr t)) :
    let y:=x.reindex degree capacity dimension residual depth hosts groups height
    ∀s t,(fundedPorts residual.symm dimension.symm dst).bank s t=y.receiver.gatheredOperand y.book (s,.inr t):=by
  subst_vars;exact physical

end
end IndexedRoots
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentPlainTerminal.Suffix DescentPackedColony DescentPackedZip DescentSharedBookScan
open DescentSixParty.Chronology DescentSixParty DescentResetHostSize DescentResetGates DescentPackedWalsh
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (priorCapacity : Expr) (f fee full total portPitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n))
local notation "L" => 2^r
local notation "groups" => 2^c
local notation "B" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
local notation "prev" => a.issuedSources E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch
local notation "pt" => fun table hdr=>ClosedReset.Recorded.reservationFields E hdr peers H portPitch c (E.dim-c) table
  (Nat.clog 2 (E.dim+2)) total (.lookup oldId .row)

local notation "cols" => a.atlasSources E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
theorem issued_fallback_words (space : a.PreparedFits B) :
    (IndexedRoots.mk a B space cols).FallbackWords:=by
  intro mem s root here peer marks low wide room roster localSpan markSpan own tagged signs pages
  exact a.issued_fallback_word E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
    space mem s root here peer marks low wide room.remoteShape roster
    (fun i=>⟨room.localShape i,localSpan i⟩) (fun i j=>⟨room.ports i j,markSpan i j⟩) own tagged signs
    (pages (s,.inr root)).1 (pages (s,.inr root)).2

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
