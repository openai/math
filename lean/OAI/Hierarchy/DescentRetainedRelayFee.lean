import OAI.Hierarchy.DescentResetOriginalFees
import OAI.Hierarchy.DescentResetTrunkOperandPrefix
import OAI.Hierarchy.DescentResetTrunkRelay

namespace OAI
/-! # Original funded source bank of the incoming stem at its true relay -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetLocalRoster
open scoped Classical BigOperators
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "R" => B.reset.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "U" => Fintype.card input.V
local notation "H₀" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H₀*2^k
local notation "slots" => max Y (2^height)
local notation "pcCap" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "okCode" => fun t=>((T).codeLegal t).2
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Short" => DescentResetCompactParent.Word H₀ r Y L (A).cap slots pcCap

open DescentPackedColony DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentResetFieldAssembler
local notation "K" => totalLocal B
local notation "X" => 2^k
local notation "grp" => S.groupCount (i+1)
local notation "board_" => blocks B
local notation "entry" => (Z).rawHostRank T vertex
open DescentResetSourceTicketCompare DescentResetSourceTicketRAM
variable {H b : ℕ} (rack : Fin H→Option B.next.V)

theorem relay_fee (age : 0< i) (sorted : SourceSorted W input.order)
    (name : B.next.V↪Fin H) (physical : ∀v,rack (name v)=some v)
    (room : B.next.placement.cap<2^b) (neighbors : B.next.placement.degree+1<2^b)
    (words : DescentResetParentCodec.capCount H₀ r Y L (A).cap slots pcCap≤2^b)
    (j : (old).graph.Edge) :
    let p:=stemParent B (true,j)
    let u:=(blocks B).src p
    (∑l,feeAt (wordBefore B) (original_fees (b:=b) B rack u.2 (name u.1.2) u.1.1)
      (incomingCandidate B (incomingIndex B j)) l)=earlierIncoming B j :=by
  let p:=stemParent B (true,j)
  let u:=(blocks B).src p
  have pos : 0<(blocks B).count p := (stem_one B true j).symm ▸ Nat.zero_lt_one
  let local_ : Local (blocks B) u:=⟨p,pos,Or.inl rfl⟩
  have index : localRoster B u (sourceOccurrence B u local_)=incomingCandidate B (incomingIndex B j) :=
    Fin.ext (stem_number B u true j (sourceOccurrence B u local_).property)
  have paid:=ticket_issued B rack age sorted name physical room neighbors words u.2 u.1.2 u.1.1 local_
  change (∑l,feeAt (wordBefore B) (original_fees (b:=b) B rack u.2 (name u.1.2) u.1.1)
    (incomingCandidate B (incomingIndex B j)) l)=_
  rw [←index]
  exact paid.trans (incoming_sourceTicket B j pos)

theorem relay_fee_at_trunk (age : 0< i) (sorted : SourceSorted W input.order)
    (name : B.next.V↪Fin H) (physical : ∀v,rack (name v)=some v)
    (room : B.next.placement.cap<2^b) (neighbors : B.next.placement.degree+1<2^b)
    (words : DescentResetParentCodec.capCount H₀ r Y L (A).cap slots pcCap≤2^b)
    (t₀ : (Z).Fallback) (j : (old).graph.Edge) (same : (T).home ((old).graph.dst j)=t₀) :
    let u:=(blocks B).dst (trunkParent B t₀)
    (∑l,feeAt (wordBefore B) (original_fees (b:=b) B rack u.2 (name u.1.2) u.1.1)
      (incomingCandidate B (incomingIndex B j)) l)=earlierIncoming B j :=by
  dsimp only
  rw [←(incoming_home B t₀ j).2 same]
  exact relay_fee B rack age sorted name physical room neighbors words j

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
