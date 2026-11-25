import OAI.Hierarchy.DescentResetPeerRecordedFlag
import OAI.Hierarchy.DescentResetPeerRootOrigins

namespace OAI
/-! # The recorded reset inputs determine all four structural neighbor families -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames
open DescentCompiler DescentColonies DescentPackedPrivateMenu DescentDenseHostOrder DescentIssuedFallbackPanel
open DescentGL DescentRotorRootPresence DescentResetHostSize DescentSIMDLookup DescentFallbackPeriod
open DescentFallbackPeriod.Projected.Receiver DescentResetPeerUnionRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {pinBits : P→ℕ} {W : MarkedWorld F d P pinBits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (recorded : B.Recorded p)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "r" => (Z).k-cc
local notation "height" => GroupStage.depthBound D n f g
local notation "cap" => input.placement.cap
local notation "degree_" => input.placement.degree
local notation "full" => input.placement.wire*(input.placement.z*G.b)*cap
local notation "leaf" => 2^r*(2*cap)
local notation "layer" => DescentRecordedRotorLayers.width f cap
local notation "digit" => fieldBits (Z).graph r height leaf layer C (Z).width
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "arr" => privatePanelAt B (private_count_eq B)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Slot" => Fin (2^(S.groupWidth k tail i+k-cc))×Fin (2*cap)
variable {H nbits t a keyBits : ℕ} (pad : Fintype.card input.V ≤ H) (μ : Layout B.reset.k)
local notation "tall" => (vertex).trans (Fin.castLEEmb pad)
local notation "owner" => input.vertex.trans (Fin.castLEEmb pad)
local notation "named" => (Z).rawHostRank T tall
variable (levels : Fin H→ℕ)
    (stencil : Fin H→Block B.terminals.commonDepth→Block (B.reset.k-B.terminals.commonDepth)→Cell t)
    (peers : Fin H→Fin input.placement.degree→Option (Fin H))
    (wires : Fin H→Block B.terminals.commonDepth→Block (B.reset.k-B.terminals.commonDepth)→Fin (2*input.placement.cap)→
      Option (DescentSharedCableNames.Stage.Live input.placement.degree input.placement.cap))
    (rank : Fin H→Fin (DescentSharedBookScan.width (B.reset.k-B.terminals.commonDepth) (2^B.reset.n) input.placement.degree)→ℕ)
local notation "head" => goodInput cc a cap (Fintype.card input.V) levels (fun v g j=>((stencil v g j).val:Cell a))
local notation "seen_" => fun v hi=>(inputs (fun v g j=>(stencil v g j).val) peers wires rank v hi : Packet degree_ (2^r) cap (Z).n r a)
local notation "tree" => fun (_ : Bool) (_ : Code r×Option (Fin (2^(Z).n)))=>seen_
local notation "word" => privatePageValue (Ht:=height) (board:=(Z).graph) (packet:=(Z).width)
    (C:=C) (layerBits:=layer) (f:=f) head tree

include recorded in
theorem recorded_peer_origins (unit : 0 < (Z).unit)
    (keys : Fin (stemsCount B)→Fin H→Block cc→Cell keyBits)
    (stem : ∀(u : Host) s (j : Slot),(keys (stemAxis B (s,j)) (((Z).hostFields T tall u.1.2).1) (peerLane B u)).val=
      DescentResetStemKey.code ((oldStemAt B u s j).map (stemTicket B s)))
    (won : HEq μ B.frame.basis) (residual : r < 2^nbits) (one : 1 < 2^nbits)
    (amount : 2^r*full < 2^nbits) (shape : 2*DescentFallbackShapeTable.rows r (2^(Z).n) ≤ 2^t)
    (active : 0 < full) (quotaPos : 0 < quota S.rounds) (degreePos : 0 < 32*Nat.clog 2 (2*degree_))
    (attained : ∀v,levels (owner v)=(Z).placement.b (B.frame.host v))
    (stamped : ∀v hi lo,stencil (owner v) hi lo=Recorded.realPanel (reset:=B) B.keyWidth μ nbits t v hi lo)
    (precision : t ≤ a) (depthBits : r+1 < 2^a) (capBits : cap < 2^a)
    (occupied : ∀s b,DescentFallbackPeriod.key (Ht:=height) (l:=(Z).layerBits) s
      ((Z).fallLabel T b,((T).code b).2.2) (seen_ (tall ((Z).rootVertex T (.inr b))) ((Z).rootBlock T (.inr b)))=
      (Z).fallbackKey T s b (arr s b))
    (empty : ∀s ticket v hi,(Z).atRoot T tall (tall v,hi,.inr ticket)=none →
      DescentFallbackPeriod.key (Ht:=height) (l:=(Z).layerBits) s ticket (seen_ (tall v) hi)=none) :
    PeerOrigins B pad (⟨keys,(Z).sparseActor T tall,word⟩ : PriorPeerWords B H digit keyBits) unit arr := by
  have heads (v : (Z).V) (hi : Block cc) (root : Code r) :=
    recorded.private_good_inputs pad μ won residual one amount shape active quotaPos degreePos levels stencil
      attained stamped precision depthBits capBits (B.frame.host.symm v) hi root
  simp only [Equiv.apply_symm_apply] at heads
  exact issued_page_origins B pad recorded head tree keys ((Z).sparseActor T tall) unit stem (fun _ _=>rfl)
    (fun v hi t=>(heads v hi t).1) (fun v hi t=>(heads v hi t).2.1) (fun v hi t=>(heads v hi t).2.2)
    occupied (fun s ticket v hi absent=>empty s ticket v hi
      (((Z).empty_root_reindex T vertex (Fin.castLEEmb pad) (vertex v) hi (.inr ticket)).2 absent))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
