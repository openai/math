import OAI.Hierarchy.DescentResetActualSourcePull
import OAI.Hierarchy.DescentResetSourceTicketPair

namespace OAI
/-! # The original positive-parent invoice at every reset receiver -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetLocalRoster
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
local notation "K" => totalLocal B
local notation "X" => 2^k
local notation "grp" => S.groupCount (i+1)
local notation "board_" => blocks B
local notation "entry" => (Z).rawHostRank T vertex
open DescentResetSourceTicketCompare DescentResetSourceTicketRAM
variable {H b : ℕ} (rack : Fin H→Option B.next.V)

def original_fees (x : Fin X) (v : Fin H) (g₀ : Fin grp) : Fields K b :=
  DescentResetSourceTicketPair.fields (fun j=>actualMeta B rack x j v g₀)
    (fun j=>(actualParentNumber B rack x j v g₀:Cell b))

/-- Each unit of a positive local parent occupies its own genuine incident
grain, including the single incidence of a loop. -/
theorem local_count_le (u : Host) :
    (∑e : Local (blocks B) u,(blocks B).count e.val)≤B.next.placement.cap := by
  let c:=blocks B
  let board:=Stage.source B.next.placement (B.next.order.trans Fin.valEmbedding)
  let ids (s : Σe : Local c u,Fin (c.count e.val)) : Σe,Fin (c.count e) := ⟨s.1.val,s.2⟩
  let ticket (s : Σe : Local c u,Fin (c.count e.val)) : ↥(board.incident u) :=
    ⟨c.order (ids s),by
      simp only [Ends.incident,Finset.mem_filter,Finset.mem_univ,true_and]
      change board.src (c.order ⟨s.1.val,s.2⟩)=u ∨ board.dst (c.order ⟨s.1.val,s.2⟩)=u
      rw [c.atSource,c.atTarget];exact s.1.property.2⟩
  have faithful : Function.Injective ticket := by
    rintro ⟨⟨e,he⟩,j⟩ ⟨⟨f,hf⟩,k₀⟩ eqn
    have pair:=c.order.injective (congrArg Subtype.val eqn)
    change (⟨e,j⟩ : Σa,Fin (c.count a))=⟨f,k₀⟩ at pair
    cases pair
    rfl
  have receipt:=Fintype.card_le_of_injective ticket faithful
  have ceiling:=Stage.measured B.next.placement (B.next.order.trans Fin.valEmbedding) S B.next.valid u
  simpa only [Fintype.card_sigma,Fintype.card_fin,Fintype.card_coe] using
    (receipt.trans (by simpa only [Fintype.card_coe] using ceiling))

private theorem fee_le (keys : Fields K b) (j s : Fin K) :
    feeAt (wordBefore B) keys j s≤field keys s 3 := by
  unfold feeAt
  split <;> omega

theorem sum_fee_le (x : Fin X) (v : Fin H) (g₀ : Fin grp) (j : Fin K) :
    (∑s,feeAt (wordBefore B) (original_fees (b:=b) B rack x v g₀) j s)≤B.next.placement.cap := by
  let keys:=original_fees (b:=b) B rack x v g₀
  refine (Finset.sum_le_sum (fun s _=>fee_le B keys j s)).trans ?_
  cases hr:rack v with
  | none=>
    have eqn (s : Fin K) : field keys s 3=0 := by
      rw [show keys=original_fees (b:=b) B rack x v g₀ from rfl]
      simp [original_fees,DescentResetSourceTicketPair.component,DescentResetSourceTicketPair.quad,
        actualMeta,hr,Meta.blank]
    simp [eqn]
  | some h₀=>
    let u : Host:=((g₀,h₀),x)
    have le (s : Fin K) : field keys s 3≤(localOrigin B u s).elim 0 (fun e=>(blocks B).count e.val) := by
      change field (DescentResetSourceTicketPair.fields _ _) s 3≤_
      rw [DescentResetSourceTicketPair.component]
      have observed : actualMeta B rack x s v g₀ = «meta» B u (localOrigin B u s) := by
        simp only [actualMeta,hr,Option.elim_some]
        rfl
      rw [observed]
      cases localOrigin B u s with
      | none => exact Nat.zero_le 0
      | some e => exact Nat.mod_le _ _
    exact (Finset.sum_le_sum (fun s _=>le s)).trans
      ((local_sum B u (fun e=>(blocks B).count e.val)).le.trans (local_count_le B u))

theorem ticket_issued (age : 0 < i) (sorted : SourceSorted W input.order)
    (name : B.next.V↪Fin H) (physical : ∀u,rack (name u)=some u)
    (room : B.next.placement.cap<2^b) (neighbors : B.next.placement.degree+1<2^b)
    (words : DescentResetParentCodec.capCount H₀ r Y L (A).cap slots pcCap≤2^b)
    (x : Fin X) (h₀ : B.next.V) (g₀ : Fin grp) (e : Local (blocks B) ((g₀,h₀),x)) :
    (∑slot,feeAt (wordBefore B)
      (original_fees (b:=b) B rack x (name ((blocks B).src e.val).1.2) g₀)
      (localRoster B _ (sourceOccurrence B _ e)) slot)=(sourceTicket B e.val e.property.1).val := by
  let u:Host:=(blocks B).src e.val
  have window : ((g₀,u.1.2),x)=u :=
    DescentResetWindowResidentSources.source_at B.next.placement (B.next.order.trans Fin.valEmbedding) (blocks B) ((g₀,h₀),x) e
  have classRoom (z : Host) : localClass B u z<2^b :=
    (Finset.card_filter_le _ _).trans_lt ((DescentResetWindowResidentSources.sources_room B.next.placement u).trans_lt neighbors)
  have unitRoom (s : Local (blocks B) u) : (blocks B).count s.val<2^b :=
    (Finset.single_le_sum (f:=fun t : Local (blocks B) u=>(blocks B).count t.val)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ s)).trans_lt ((local_count_le B u).trans_lt room)
  have observed (j : Fin K) : actualMeta B rack x j (name u.1.2) g₀ =
      «meta» B u (localOrigin B u j) := by
    simp only [actualMeta, physical, Option.elim_some]
    exact congrArg (fun h => «meta» B h (localOrigin B h j)) window
  have numbered (j : Fin K) : actualParentNumber B rack x j (name u.1.2) g₀ =
      (localOrigin B u j).elim 0 (fun t => wordNumber B u t.val) := by
    simp only [actualParentNumber, physical, Option.elim_some]
    exact congrArg (fun h => (localOrigin B h j).elim 0 (fun t => wordNumber B h t.val)) window
  apply compact_source_ticket B age sorted e.val e.property.1 _ _ (localClass B u)
  · rw [source_lookup B ((g₀,h₀),x) e];rfl
  · intro slot s found
    change localOrigin B u slot=some s at found
    let keys:=original_fees (b:=b) B rack x (name u.1.2) g₀
    change field keys slot 0=localClass B u ((blocks B).src s.val) ∧
      field keys slot 1=localClass B u ((blocks B).dst s.val) ∧
      field keys slot 2=wordNumber B u s.val ∧ field keys slot 3=(blocks B).count s.val
    simp only [keys,original_fees,DescentResetSourceTicketPair.component, observed, numbered, found,Option.elim_some]
    exact ⟨Nat.mod_eq_of_lt (classRoom _),Nat.mod_eq_of_lt (classRoom _),
      Nat.mod_eq_of_lt ((wordNumber_lt B u s.val).trans_le words),Nat.mod_eq_of_lt (unitRoom s)⟩
  · intro slot found
    change localOrigin B u slot=none at found
    change field (original_fees (b:=b) B rack x (name u.1.2) g₀) slot 3=0
    simp only [original_fees,DescentResetSourceTicketPair.component, observed, found]
    rfl
end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
