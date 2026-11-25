import OAI.Hierarchy.DescentPrivatePanelProjection
import OAI.Hierarchy.DescentContactJointGeometry

namespace OAI
/-! The mounted private panel identifies both true endpoints at every positive local slot. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentParallelBase
open DescentCompiler DescentColonies DescentDenseHostOrder DescentResetPeerUnionRAM DescentGroupPeerOrder
open DescentPackedColony DescentSIMDLookup DescentPackedZip ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {pinBits : P→ℕ} {W : MarkedWorld F d P pinBits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "J" => 2^(T).commonDepth
local notation "D₀" => input.placement.degree
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Slot" => Fin (2^(S.groupWidth k tail i+k-(T).commonDepth))×Fin (2*input.placement.cap)
local notation "kind_" => Axes.kind (stemsCount B) (contactCount B) (privateCount B)

variable {H field keyBits bits count : ℕ} (pad : Fintype.card input.V ≤ H)
local notation "padded" => (vertex).trans (Fin.castLEEmb pad)
local notation "named" => (Z).rawHostRank T padded
local notation "coords" => (Z).hostFields T padded
local notation "pitch" => H*shelf


open DescentResetLocalRoster DescentPackedPrivateMenu DescentResetPeerUnionRAM
variable (prior : PriorPeerWords B H field keyBits)
local notation "groups₁" => S.groupCount (i+1)
local notation "host₁" => Stage.Host (Fin groups₁) B.next.V k
local notation "orig" => (fun (u:host₁)=>vertex (receiverRoot B u).1)

open DescentResetWindowResidentSources
open private slot_address from OAI.Hierarchy.DescentPrivateReachedMask
variable (unit : 0<B.reset.unit) (panels : Bool→B.reset.Fallback→DescentPackedFallbackTree.Panel (GroupStage.depthBound D n f g) count)
    (issued : PeerOrigins B pad prior unit panels) (oldBatch batch b : ℕ)

include issued in
theorem private_rank_requests (u : host₁) (s : Bool) (t : (Z).RootTicket T) (l : Fin capacity)
    (a : Local (blocks B) u) (found : localOrigin B u (privateShelfIndex B (localPrivateId _ _ capacity (s,t,l)))=some a)
    (shapeFit : shelf≤2^b) (widthFit : B.next.placement.cap<2^b) :
    let src:=(blocks B).src a.val
    let dst:=(blocks B).dst a.val
    (privateDigit B pad prior oldBatch batch b u s t l 0).val=relativeShape B src ∧
    (privateDigit B pad prior oldBatch batch b u s t l 1).val=relativeShape B dst ∧
    (receiverRoot B src).1=(receiverRoot B u).1 ∧ (receiverRoot B dst).1=(receiverRoot B u).1 ∧
    src∈sources B.next.placement u ∧ dst∈sources B.next.placement u:=by
  intro src dst
  obtain ⟨p,edge,slot⟩:=(private_shelf_iff B u _ a).1 found
  have live : active (blocks B) u (privateWire B p):=edge ▸ a.property
  have home:=private_owner B u p live.2
  have ticket:=(localPrivateId r (2^(Z).n) capacity).injective slot
  have original:=(slot_address B u s t l p).2 ⟨home,ticket⟩
  let row:=priorPrivate B pad prior (orig u) (receiverRoot B u).2 s t l
  have actual:=(issued.installed (orig u) (receiverRoot B u).2 s t l) p original
  have tags:=issued_relative B p row actual unit
  have roots:=private_endpoint_roots B p
  have first:=private_digits B pad prior unit panels issued oldBatch batch b u s t l 0 shapeFit widthFit
  have last:=private_digits B pad prior unit panels issued oldBatch batch b u s t l 1 shapeFit widthFit
  have start : (receiverRoot B src).1=(receiverRoot B u).1:=by
    change (receiverRoot B ((blocks B).src a.val)).1=_
    rw [edge,roots.1,home]
  have stop : (receiverRoot B dst).1=(receiverRoot B u).1:=by
    change (receiverRoot B ((blocks B).dst a.val)).1=_
    rw [edge,roots.2,home]
  refine ⟨?_,?_,start,stop,DescentResetWindowResidentSources.source_mem B.next.placement
    (B.next.order.trans Fin.valEmbedding) (blocks B) u a,destination_mem B u a⟩
  · change _=relativeShape B ((blocks B).src a.val)
    rw [edge]
    rw [first]
    change (if row 0=1 then row 1 else 0)=_
    simpa only [tags.1, ↓reduceIte] using tags.2.1
  · change _=relativeShape B ((blocks B).dst a.val)
    rw [edge]
    rw [last]
    change (if row 0=1 then row 2 else 0)=_
    simpa only [tags.1, ↓reduceIte] using tags.2.2.1

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
