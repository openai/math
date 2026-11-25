import OAI.Hierarchy.DescentNamedRetainedControlsRead
import OAI.Hierarchy.DescentIssuedCarriedIndex

namespace OAI
/-! # The measured retained hub and fee at each original incoming operand -/
noncomputable section
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetLocalRoster
set_option quotPrecheck false
set_option hygiene false
open scoped Classical BigOperators Fin.CommRing
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

open DescentResetTrunkIssue
local notation "primary" t:arg => (blocks B).src (trunkParent B t)
local notation "groups" => S.groupCount (i+1)

/-- On a true selected incoming signed grain the published ticket lies at that
grain's own donor and signed-slot index. The word is its exact arrival count. -/
theorem recorded_incoming_value {field count : ℕ} (age : 0< i) (sorted : SourceSorted W input.order)
    (physical : ∀v,rack (name v)=some v) (room : B.next.placement.cap<2^b)
    (neighbors : B.next.placement.degree+1<2^b)
    (words : DescentResetParentCodec.capCount H₀ r Y L (A).cap slots pcCap≤2^b)
    (fieldRoom : B.next.placement.cap<2^field)
    (sel : Fin count→Fin (totalLocal B)) (positions : ∀j,(sel j).val=2^k*(2*(A).cap)+j.val)
    (fee : Fin (2^k)→Fin count→Fin H→Fin groups→Cell field)
    (seen : ∀x j h gr,fee x j h gr=(((pointer bounded (compactTrunkPeer B previous) h).elim 0
      (fun v=>∑n,feeAt (wordBefore B) (original_fees (b:=b) B rack x v gr) (sel j) n):ℕ):Cell field))
    (t₀ : (Z).Fallback) (e : (old).graph.Edge) (land : (T).home ((old).graph.dst e)=t₀)
    (j : Fin count) (which : j.val=(incomingIndex B e).val) :
    (fee (primary t₀).2 j (name (primary t₀).1.2) (primary t₀).1.1).val=earlierIncoming B e:=by
  have index : sel j=incomingCandidate B (incomingIndex B e):=by
    apply Fin.ext
    rw [positions,which]
    simp only [incomingCandidate,Fin.val_castLE,finProdFinEquiv_apply_val]
    change 2^k*(2*(A).cap)+(incomingIndex B e).val=
      (incomingIndex B e).val+(2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*(A).cap))*1
    rw [calendar_low_count B,mul_one,Nat.add_comm]
  have paid:=pulled_relay_fee B rack previous bounded age sorted physical room neighbors words t₀ e land
  rw [seen,index,paid,Fin.val_cast_of_lt ((incoming_cap B e).trans fieldRoom)]

/-- Both sides of the physical terminal carry the hub flag read from its
original optional socket. -/
theorem recorded_primary_hub {field : ℕ} (hub : Fin H→Fin groups→Cell field)
    (seen : ∀h g,hub h g=if ((originalTrunkRack B h).elim .blank (hostShape B)).core then 0 else 1)
    (t₀ : (Z).Fallback) :
    hub (name (primary t₀).1.2) (primary t₀).1.1=
      if ((T).code t₀).2.2.isSome then 0 else 1:=by
  have atHost : originalTrunkRack B (name (primary t₀).1.2) = some (primary t₀).1.2 :=
    (original_rack_order B previous bounded).1 _
  rw [seen,atHost]
  simp only [Option.elim_some,primary_hub_digit B t₀]

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
