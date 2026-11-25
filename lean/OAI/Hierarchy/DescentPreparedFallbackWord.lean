import OAI.Hierarchy.DescentPreparedRootInputs
import OAI.Hierarchy.DescentIssuedFallbackRoot

namespace OAI
/-! # The actual intermediate operand of each mounted exceptional root -/
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
variable (space : a.PreparedFits (a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage)) (mem : Memory w) (s : Bool) (root : Code r×Option (Fin (2^n)))
local notation "pg" => ((s,.inr root):RootPage r (2^n))
local notation "src" => a.preparedMid B space mem
local notation "dst" => a.rootInputState B space mem pg

local notation "rid" => (rootIndex r (2^n) pg).val
local notation "arena" => RootTemplates.arena (a.headerEnd B) H groups M r n D
local notation "bank" => (B).exceptional s root

/-- Read the saved original input of this exact physical fallback root on the completed
memory. Its signed window, peer chart and measured ranks are read from the preceding
mounted scalar memory; the computed root load never occurs as an input. -/
theorem issued_fallback_word (here : Fin H→Fin groups→Fin L→ℕ)
    (peer : Fin H→Fin D→Option (Fin H))
    (marks : Fin H→Fin groups→Fin L→Fin (2*cap)→Option (DescentSharedCableNames.Stage.Live D cap))
    (low : Ht+2<w) (wide : Ht+2≤field)
    (reachable : ∀i,Accessible peers ((prev).tagged i) H groups M w (a.headerEnd B))
    (roster : Mounted peers peer src groups M)
    (localFit : ∀i,((prev).here i).Fits w (a.headerEnd B) ∧ H*chunks groups M≤((prev).here i).size)
    (signedFit : ∀i j,((prev).signed i j).Fits w (a.headerEnd B) ∧ H*chunks groups M≤((prev).signed i j).size)
    (own : ∀i,Reads ((prev).here i) (fun v g=>(here v g i:Cell field)) M src)
    (tagged : ∀i,Reads ((prev).tagged i) (fun v g=>((here v g i+1:ℕ):Cell field)) M src)
    (signs : ∀i j,Reads ((prev).signed i j) (fun v g=>((DescentSignedCableCodec.encode (marks v g i j)).val:Cell field)) M src)
    (prior : ∀j,((bank).reads j).Fits w ((arena).middle rid))
    (packed : M*max ((bank).field*inputCount D L cap n r) (bank).outputBits≤w/2) :
    let rank:=fun (v : Fin H) (j : Fin (DescentSharedBookScan.width r (2^n) D)) => (ranks (a:=r) (Y:=2^n) (D:=D) ((B).common a.projectionEnd H) (2^Ht) (Ht+2) src v j).val
    Source (a.gatheredOperand B pg) (fun h g=>encodePacket (inputs here peer marks rank h g : Packet D L cap n r field)) M
      (a.preparedImage B space mem) :=by
  exact a.issued_fallback_packet E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
    space mem s root here peer marks low wide reachable roster localFit signedFit own tagged signs prior packed

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
