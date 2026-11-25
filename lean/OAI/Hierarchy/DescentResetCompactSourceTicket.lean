import OAI.Hierarchy.DescentResetSourceTicketBank
import OAI.Hierarchy.DescentResetNativeLocalBefore
import OAI.Hierarchy.DescentResetSourceTicketRoster

namespace OAI
/-! # The actual local source ticket with measured compact descriptors -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetSourceTicketRAM DescentResetSourceTicketCompare
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
local notation "H" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H*2^k
local notation "slots" => max Y (2^height)
local notation "pcCap" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "okCode" => fun t=>((T).codeLegal t).2
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Kind" => (Bool×(old).graph.Edge) ⊕ ((Z).Fallback ⊕ ((R).Contact ⊕ PrivateOccurrence B))
local notation "Short" => DescentResetCompactParent.Word H r Y L (A).cap slots pcCap

local notation "tape" => (Z).nativeResetEdges T vertex birth

def wordNumber (u : Host) (e : (coarse).graph.Edge) := DescentResetParentCodec.number (zeroCoarse B u) (nativeWord B u e)

def wordBefore := DescentResetParentCodec.before («H»:=H) («r»:=r) («Y»:=Y) («L»:=L) (cap:=(A).cap)
  (links:=slots) (program:=pcCap) (T).commonDepth

theorem wordNumber_lt (u : Host) (e : (coarse).graph.Edge) :
    wordNumber B u e<DescentResetParentCodec.capCount H r Y L (A).cap slots pcCap :=
  DescentResetParentCodec.number_lt _ _

theorem wordBefore_iff (age : 0 < i) (sorted : SourceSorted W input.order) (u : Host)
    (x y : Local (blocks B) u) :
    wordBefore B (wordNumber B u x.val) (wordNumber B u y.val)=true ↔ (tape).rank x.val<(tape).rank y.val := by
  rw [wordBefore,wordNumber,wordNumber,DescentResetParentCodec.before_number,decide_eq_true_eq]
  exact nativeLocalBefore B age sorted u x y

/-- The src/dst codes may be arbitrary numbers assigned to the sites in the
immediate halo. Every positive candidate is resident at the queried source.
The ghost slots have zero units. The sum is the exact original source prefix. -/
theorem compact_source_ticket (age : 0 < i) (sorted : SourceSorted W input.order) (e : (coarse).graph.Edge)
    (he : 0<weight B e) (j : Fin (totalLocal B)) {b : ℕ} (keys : Fields (totalLocal B) b)
    (names : Host→ℕ)
    (querySeen : (localOrigin B ((blocks B).src e) j).map Subtype.val=some e)
    (seen : ∀slot s,localOrigin B ((blocks B).src e) slot=some s →
      field keys slot 0=names ((blocks B).src s.val) ∧ field keys slot 1=names ((blocks B).dst s.val) ∧
      field keys slot 2=wordNumber B ((blocks B).src e) s.val ∧ field keys slot 3=(blocks B).count s.val)
    (dormant : ∀slot,localOrigin B ((blocks B).src e) slot=none → field keys slot 3=0) :
    (∑slot,feeAt (wordBefore B) keys j slot)=(sourceTicket B e he).val := by
  obtain ⟨q₀,qLive,qEq⟩ : ∃s,localOrigin B ((blocks B).src e) j=some s ∧ s.val=e:=by
    cases hx : localOrigin B ((blocks B).src e) j with
    | none=>simp [hx] at querySeen
    | some s=>exact ⟨s,rfl,by simpa only [hx,Option.map_some,Option.some.injEq] using querySeen⟩
  have sq:=seen j q₀ qLive
  have positive : field keys j 3≠0:=by rw [sq.2.2.2];exact Nat.ne_of_gt q₀.property.1
  apply measured_values B e he
  intro slot
  cases h : localOrigin B ((blocks B).src e) slot with
  | none=>simp [feeAt,dormant slot h]
  | some s=>
    obtain ⟨src,dst,key,units⟩:=seen slot s h
    have touches : field keys slot 0=field keys j 0 ∨ field keys slot 1=field keys j 0:=by
      rw [src,dst,sq.1,qEq]
      rcases s.property.2 with v|v
      · exact .inl (congrArg names v)
      · exact .inr (congrArg names v)
    have compare:=wordBefore_iff B age sorted ((blocks B).src e) s q₀
    rw [qEq] at compare
    simp only [feeAt,touches,true_and,key,sq.2.2.1,qEq,compare,units,Option.elim_some]
    by_cases order : (tape).rank s.val < (tape).rank e
    · exact (ite_eq_left ⟨positive,order⟩).trans (ite_eq_left order).symm
    · exact (ite_eq_right (fun hit => order hit.2)).trans (ite_eq_right order).symm

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
