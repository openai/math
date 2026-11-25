import OAI.Hierarchy.DescentRecordedRootSnapshot
import OAI.Hierarchy.DescentResetPeerObservedFallback

namespace OAI
/-! # Structural neighbor roots from the preceding physically prepared receiver -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames
open DescentCompiler DescentColonies DescentGL DescentFallbackPeriod DescentSIMDLookup DescentResetHostSize
open DescentPaidResidentCount.Reset DescentFallbackPeriod.Projected
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail H a : ℕ}
    {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (pad : Fintype.card input.V ≤ H)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "r" => (Z).k-cc
local notation "depth" => GroupStage.depthBound D n f g
local notation "L" => 2^(S.groupWidth k tail i+k-cc)
local notation "cap" => input.placement.cap
local notation "D₀" => input.placement.degree
local notation "vertex" => input.vertex.trans (Fin.castLEEmb pad)
local notation "tall" => B.frame.host.symm.toEmbedding.trans vertex
local notation "arr" => privatePanelAt B (private_count_eq B)
variable {hw N K Rep M hm l tiny : ℕ}
  (receiver : Receiver input.placement.degree input.placement.cap N B.reset.n (B.reset.k-B.terminals.commonDepth) B.terminals.commonDepth H (S.groupCount i) K Rep M hm l tiny a (GroupStage.depthBound D n f g) hw)
  (book : RootBook B.reset.n (B.reset.k-B.terminals.commonDepth) input.placement.degree (2^(B.reset.k-B.terminals.commonDepth)) input.placement.cap a) (space : receiver.PreparedFits book)
  (mem : Computability.VPVNP.BurstRAM.Memory hw)
  (orig : OriginalHeader B pad receiver book mem) (x : OriginalArrays B pad a)
local notation "snap" => root_snapshot B pad receiver book space mem orig x
open DescentDenseHostOrder DescentPackedPrivateMenu DescentFallbackPeriod.Projected.Receiver
local notation "full" => input.placement.wire*(input.placement.z*G.b)*cap
local notation "digit" => fieldBits (Z).graph r depth (2^r*(2*cap)) (DescentRecordedRotorLayers.width f cap) C (Z).width
local notation "host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "slots_" => Fin L×Fin (2*cap)
local notation "actor" => (Z).sparseActor T tall
local notation "rank_" => fun h j=>(DescentSharedBookScan.ranks (a:=r) (Y:=2^(Z).n) (D:=D₀)
    (book.common receiver.projectionEnd H) (2^depth) (depth+2) (receiver.preparedMid book space mem) h j).val

include orig in
/-- All private record claims and all key decisions are consequences of the actual
preceding rank/signed snapshot. The stem pass supplies only its own original keys. -/
theorem prepared_peer_origins {nbits t keyBits p : ℕ} (recorded : B.Recorded p) (μ : Layout (Z).k)
    (levels : Fin H→ℕ) (stencil : Fin H→Block cc→Block r→Cell t)
    (cables : Fin H→Block cc→Block r→Fin (2*cap)→Option (DescentSharedCableNames.Stage.Live D₀ cap))
    (unit : 0 < (Z).unit) (keys : Fin (stemsCount B)→Fin H→Block cc→Cell keyBits)
    (stem : ∀(u : host) s (j : slots_),(keys (stemAxis B (s,j)) (((Z).hostFields T tall u.1.2).1) (peerLane B u)).val=
      DescentResetStemKey.code ((oldStemAt B u s j).map (stemTicket B s)))
    (won : HEq μ B.frame.basis) (residual : r < 2^nbits) (one : 1 < 2^nbits)
    (bound : 2^r*full < 2^nbits) (fit : 2*DescentFallbackShapeTable.rows r (2^(Z).n) ≤ 2^t)
    (active : 0 < full) (quotaPositive : 0 < quota S.rounds) (degreePositive : 0 < 32*Nat.clog 2 (2*D₀))
    (levelRead : ∀v,levels (vertex v)=(Z).placement.b (B.frame.host v))
    (stamped : ∀v hi lo,stencil (vertex v) hi lo=Recorded.realPanel (reset:=B) B.keyWidth μ nbits t v hi lo)
    (precision : t ≤ a) (depthFits : r+1 < 2^a) (capFits : cap < 2^a)
    (shapeRead : ∀v hi lo,(stencil v hi (Fin.cast (by rw [B.keyWidth]) lo)).val=x.stencil v hi lo)
    (wireRead : ∀v hi lo j,cables v hi (Fin.cast (by rw [B.keyWidth]) lo) j=x.marks v hi lo j) :
    let headers:=goodInput cc a cap (Fintype.card input.V) levels (fun v hi j=>((stencil v hi j).val:Cell a))
    let packets:=fun (_:Bool) (_:Code r×Option (Fin (2^(Z).n))) v hi=>
      (inputs (fun v hi j=>(stencil v hi j).val) x.peers cables rank_ v hi : Packet D₀ (2^r) cap (Z).n r a)
    let values:=privatePageValue (Ht:=depth) (board:=(Z).graph) (packet:=(Z).width) (f:=f) (C:=C)
      (layerBits:=DescentRecordedRotorLayers.width f cap) headers packets
    PeerOrigins B pad (⟨keys,actor,values⟩ : PriorPeerWords B H digit keyBits) unit arr := by
  exact snapshot_peer_origins B pad snap recorded μ levels stencil cables unit keys stem won residual one
    bound fit active quotaPositive degreePositive levelRead stamped precision depthFits capFits shapeRead wireRead

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
