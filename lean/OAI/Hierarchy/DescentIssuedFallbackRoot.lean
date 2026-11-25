import OAI.Hierarchy.DescentRecordedRootBook
import OAI.Hierarchy.DescentPreparedFallbackRanks

namespace OAI
/-! # The official root book consumes the actual remapped previous signed rows -/
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
local notation "pt" => fun table hdr=> ClosedReset.Recorded.reservationFields E hdr peers H portPitch c (E.dim-c) table
  (Nat.clog 2 (E.dim+2)) total (.lookup oldId .row)
variable (space : a.PreparedFits (a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage)) (mem : Memory w) (s : Bool) (root : Code r×Option (Fin (2^n)))
local notation "pg" => ((s,.inr root):RootPage r (2^n))
local notation "src" => a.preparedMid B space mem
local notation "dst" => a.rootInputState B space mem pg

/-- Each numerical operand actually printed by the book is read from an earlier signed,
stencil or scalar-rank page; the donor roster includes all padded and missing neighbors. -/
theorem issued_fallback_operands (here : Fin H→Fin groups→Fin L→ℕ)
    (peer : Fin H→Fin D→Option (Fin H))
    (marks : Fin H→Fin groups→Fin L→Fin (2*cap)→Option (DescentSharedCableNames.Stage.Live D cap))
    (low : Ht+2< w) (wide : Ht+2≤ field)
    (reachable : ∀i,Accessible peers ((prev).tagged i) H groups M w (a.headerEnd B))
    (roster : Mounted peers peer src groups M)
    (localFit : ∀i,((prev).here i).Fits w (a.headerEnd B) ∧ H*chunks groups M≤((prev).here i).size)
    (signedFit : ∀i j,((prev).signed i j).Fits w (a.headerEnd B) ∧ H*chunks groups M≤((prev).signed i j).size)
    (own : ∀i,Reads ((prev).here i) (fun v g=>(here v g i:Cell field)) M src)
    (tagged : ∀i,Reads ((prev).tagged i) (fun v g=>((here v g i+1:ℕ):Cell field)) M src)
    (signs : ∀i j,Reads ((prev).signed i j) (fun v g=>((DescentSignedCableCodec.encode (marks v g i j)).val:Cell field)) M src) :
    let rank:=fun v j=>(ranks (a:=r) (Y:=2^n) (D:=D) ((B).common a.projectionEnd H) (2^Ht) (Ht+2) src v j).val
    ∀j,Source (((B).exceptional s root).reads j)
      (fun h g=> inputs (field:=field) here peer marks rank h g (DescentFallbackPeriod.number.symm j)) M dst := by
  have seen:=a.fallback_operands B space mem s root prev here peer marks low wide reachable roster localFit signedFit own tagged signs
  intro rank j
  have pin:=(prev).reserved_fallback_reads (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    H factor hubWidth old.roster old.hubs a.projectionEnd groups M stencil.n pt bookPage s root j
  exact (congrArg (fun e => Source e
    (fun h g => inputs (field:=field) here peer marks rank h g (DescentFallbackPeriod.number.symm j)) M dst) pin).mpr
    (seen (DescentFallbackPeriod.number.symm j))

/-- The packed fallback input itself is retained in its native middle bank, with all
home shapes, reciprocal donor shapes, signed faces and scalar book ranks. -/
theorem issued_fallback_packet (here : Fin H→Fin groups→Fin L→ℕ)
    (peer : Fin H→Fin D→Option (Fin H))
    (marks : Fin H→Fin groups→Fin L→Fin (2*cap)→Option (DescentSharedCableNames.Stage.Live D cap))
    (low : Ht+2< w) (wide : Ht+2≤ field)
    (reachable : ∀i,Accessible peers ((prev).tagged i) H groups M w (a.headerEnd B))
    (roster : Mounted peers peer src groups M)
    (localFit : ∀i,((prev).here i).Fits w (a.headerEnd B) ∧ H*chunks groups M≤((prev).here i).size)
    (signedFit : ∀i j,((prev).signed i j).Fits w (a.headerEnd B) ∧ H*chunks groups M≤((prev).signed i j).size)
    (own : ∀i,Reads ((prev).here i) (fun v g=>(here v g i:Cell field)) M src)
    (tagged : ∀i,Reads ((prev).tagged i) (fun v g=>((here v g i+1:ℕ):Cell field)) M src)
    (signs : ∀i j,Reads ((prev).signed i j) (fun v g=>((DescentSignedCableCodec.encode (marks v g i j)).val:Cell field)) M src)
    (prior : ∀j,(((B).exceptional s root).reads j).Fits w
      ((RootTemplates.arena (a.headerEnd B) H groups M r n D).middle (rootIndex r (2^n) pg).val))
    (packed : M*max (field*inputCount D L cap n r) (((B).exceptional s root).outputBits)≤ w/2) :
    let rank:=fun v j=>(ranks (a:=r) (Y:=2^n) (D:=D) ((B).common a.projectionEnd H) (2^Ht) (Ht+2) src v j).val
    Source (a.gatheredOperand B pg) (fun h g=> encodePacket (inputs here peer marks rank h g : Packet D L cap n r field))
      M (a.preparedImage B space mem) := by
  intro rank
  apply a.gathered_source B space mem pg (fun h g j=> inputs here peer marks rank h g (number.symm j)) prior packed
  exact a.issued_fallback_operands E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
    space mem s root here peer marks low wide reachable roster localFit signedFit own tagged signs

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
