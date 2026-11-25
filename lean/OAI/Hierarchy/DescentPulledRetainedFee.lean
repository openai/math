import OAI.Hierarchy.DescentRetainedRelayFee
import OAI.Hierarchy.DescentResetTrunkCompactWindow

namespace OAI
/-! # True relay counter at the earlier operand's compact physical host -/
noncomputable section
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetLocalRoster
open scoped Classical BigOperators
set_option hygiene false
set_option quotPrecheck false
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


open DescentResetTrunkCompactPointer
variable {H₀' : ℕ} (previous : Fintype.card input.V≤H₀') (bounded : Fintype.card B.next.V≤H)
local notation "dense" => (Z).denseHostRank T ((vertex).trans (Fin.castLEEmb previous))
local notation "name" => (dense).trans (Fin.castLEEmb bounded)

/-- Reading the saved sibling pointer on a primary host reaches the row whose
incoming stem prefix is the chronological offset of the actual old operand. -/
theorem pulled_relay_fee (age : 0< i) (sorted : SourceSorted W input.order)
    (physical : ∀v,rack (name v)=some v) (room : B.next.placement.cap<2^b)
    (neighbors : B.next.placement.degree+1<2^b)
    (words : DescentResetParentCodec.capCount H₀ r Y L (A).cap slots pcCap≤2^b)
    (t₀ : (Z).Fallback) (j : (old).graph.Edge) (same : (T).home ((old).graph.dst j)=t₀) :
    let u:=(blocks B).src (trunkParent B t₀)
    (pointer bounded (compactTrunkPeer B previous) (name u.1.2)).elim 0 (fun h₁=>
      ∑l,feeAt (wordBefore B) (original_fees (b:=b) B rack u.2 h₁ u.1.1)
        (incomingCandidate B (incomingIndex B j)) l)=earlierIncoming B j:=by
  let u:=(blocks B).src (trunkParent B t₀)
  obtain ⟨p,atHost,_,dest,_⟩:=trunk_labels_at B u t₀ false
    (trunk_side B t₀ false).1 (trunk_side B t₀ false).2
  change (pointer bounded (compactTrunkPeer B previous) ((dense u.1.2).castLE bounded)).elim 0 _=_
  rw [compact_peer_at B previous bounded,atHost]
  change (∑l,feeAt (wordBefore B) (original_fees (b:=b) B rack (portAt B u p.right).2
    (name (portAt B u p.right).1.2) (portAt B u p.right).1.1)
    (incomingCandidate B (incomingIndex B j)) l)=_
  rw [dest]
  exact relay_fee_at_trunk B rack age sorted name physical room neighbors words t₀ j same

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
