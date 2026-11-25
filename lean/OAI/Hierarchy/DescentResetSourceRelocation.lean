import OAI.Hierarchy.DescentResetNativeLocalBefore
import OAI.Hierarchy.DescentResetWindowEmittedSources
import OAI.Hierarchy.DescentResetWindowTicket
import OAI.Hierarchy.DescentResetSourceSlotCode
import OAI.Hierarchy.DescentClosedRosterCoverage
import OAI.Hierarchy.DescentResetSourceClassRAM

namespace OAI
/-! # The physical source roster address of every live reset parent -/
noncomputable section
set_option quotPrecheck false

namespace Hierarchy.DescentResetCompactParent

theorem sourceLabel_installed (r : ℕ) (tag : Label r) :
    sourceLabel r tag=(DescentResetCableSlots.interval r tag).val := rfl

end Hierarchy.DescentResetCompactParent

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
local notation "H" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H*2^k
local notation "slots" => max Y (2^height)
local notation "pcCap" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "okCode" => fun t=>((T).codeLegal t).2
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Short" => DescentResetCompactParent.Word H r Y L (A).cap slots pcCap

def sourceOccurrence (u : Host) (x : Local (blocks B) u) :
    Local (blocks B) ((blocks B).src x.val) := ⟨x.val,x.property.1,Or.inl rfl⟩

theorem source_lookup (u : Host) (x : Local (blocks B) u) :
    localOrigin B ((blocks B).src x.val) (localRoster B _ (sourceOccurrence B u x))=
      some (sourceOccurrence B u x) := (local_read B _ _ _).2 rfl

private theorem contact_source_index (u : Host) (c₀ : (R).Contact)
    (atSource : DescentResetLocalRoster.active (blocks B) ((blocks B).src (contactParent B c₀)) (contactParent B c₀)) :
    (localRoster B _ ⟨contactParent B c₀,atSource⟩).val =
      sourceSlotFrom (stemsCount B) (2^height) 0 (.inr (.inr (.inl
        (siteWord B u ((R).owner false c₀),directDigit B c₀))) : Short) := by
  rw [contact_number]
  have side : ∀x : ContactAt B ((blocks B).src (contactParent B c₀)), x.val=c₀→contactSide B x=false := by
    intro x hx
    change decide ((blocks B).src (contactParent B x.val) ≠ (blocks B).src (contactParent B c₀)) = false
    simp [hx]
  let here : ContactAt B ((blocks B).src (contactParent B c₀)) := ⟨c₀,atSource.2⟩
  let site := (Z).rootTicket T ((R).owner (contactSide B here) c₀)
  let socket := contactSocket B (contactSide B here) c₀
  let port := DescentResetCableSlots.sum (Function.Embedding.refl (Fin Y))
    (Function.Embedding.refl (Fin (2^height))) socket
  have packed : (contactDigit B _ ⟨c₀,atSource⟩).val =
      (finTwoEquiv.symm (contactSide B here)).val*(rootSlots r Y*(Y+2^height)) +
      (rootId r Y site).val*(Y+2^height) + port.val := by
    change (finProdFinEquiv (finTwoEquiv.symm (contactSide B here),finProdFinEquiv (rootId r Y site,port))).val = _
    simp only [finProdFinEquiv_apply_val]
    ac_rfl
  rw [packed]
  dsimp only [site,port,socket]
  rw [side here rfl]
  have zero : (finTwoEquiv.symm false).val = 0 := rfl
  rw [zero, Nat.zero_mul, Nat.zero_add]
  cases c₀ with
  | inl a =>
    let lab := (Z).goodLabel T ((R).ends false a.1)
    let slot := ((R).outputName (T).commonDepth false a).2.val
    let root := (DescentResetCableSlots.interval r lab).val
    change stemsCount B + 1 + (root*(Y+2^height)+slot) =
      stemsCount B + 1 + root*(Y+2^height)+slot
    omega
  | inr a =>
    let lab := (Z).fallLabel T a.val.1
    let leg := (DescentResetCableSlots.optional ((T).code a.val.1).2.2).val
    let slot := ((leaf (R) height (T).bookHeight false (fallEnd (R) false a)) (fallLeg (R) false a)).val
    let label := (DescentResetCableSlots.interval r lab).val
    change stemsCount B + 1 + ((2^(r+1) + (leg+(Y+1)*label))*(Y+2^height)+(Y+slot)) =
      stemsCount B + 1 + (2^(r+1)+label*(Y+1)+leg)*(Y+2^height)+(Y+slot)
    ac_rfl

/-- Each right incidence recovers the same source-side resident and the
same first new incidence and ticket using one lookup indexed by this slot. -/
theorem source_slot (u : Host) (x : Local (blocks B) u) :
    sourceSlotFrom (stemsCount B) (2^height) (localRoster B u x).val (nativeWord B u x.val)=
      (localRoster B _ (sourceOccurrence B u x)).val := by
  obtain ⟨e,live⟩:=x
  obtain ⟨p,rfl⟩:=(motherNames B).symm.surjective e
  simp only [nativeWord,Equiv.apply_symm_apply]
  rcases p with ⟨s,j⟩|t|c₀|p
  · change (localRoster B u ⟨stemParent B (s,j),live⟩).val=_
    exact (stem_number B u s j live).trans (stem_number B _ s j _).symm
  · change (localRoster B u ⟨trunkParent B t,live⟩).val=_
    exact (trunk_number B u t live).trans (trunk_number B _ t _).symm
  · have index:=contact_source_index B u c₀ (sourceOccurrence B u ⟨contactParent B c₀,live⟩).property
    cases c₀ <;> exact index.symm
  · change (localRoster B u ⟨privateWire B p,live⟩).val=_
    exact (private_number B u p live).trans (private_number B _ p _).symm

/-- The physical four-port roster selects the actual transmitting host,
preserving the target row's group and low block. -/
theorem source_host {pitch ports : ℕ} (name : B.next.V↪Fin pitch)
    (ordered : ∀x y : B.next.V,name x<name y ↔ (Z).rawHostRank T vertex x<(Z).rawHostRank T vertex y)
    (peer : Fin pitch→Fin ports→Option (Fin pitch)) (u : Host)
    (real : DescentSortedRoster.present peer (name u.1.2)=(insert u.1.2 (B.next.placement.near u.1.2)).map name)
    (x : Local (blocks B) u) (j : Fin ports) (slot : j.val=(sourceClass B u x).val) :
    DescentSortedRoster.indexed peer (name u.1.2) j=some (name ((blocks B).src x.val).1.2) := by
  let src:=(blocks B).src x.val
  let ns:=insert u.1.2 (B.next.placement.near u.1.2)
  have contained :=DescentResetWindowResidentSources.source_mem B.next.placement
    (B.next.order.trans Fin.valEmbedding) (blocks B) u x
  rw [DescentResetWindowResidentSources.sources_as_map] at contained
  obtain ⟨v,hv,eqn⟩:=Finset.mem_map.mp contained
  have eqHost : v=src.1.2:=congrArg (fun h : Host=>h.1.2) eqn
  have member : src.1.2∈ns:=eqHost ▸ hv
  apply (DescentSortedRoster.indexed_iff _ _ _ _).2
  refine ⟨by rw [real];exact Finset.mem_map.mpr ⟨_,member,rfl⟩,?_⟩
  rw [slot,sourceClass_host,DescentSortedRoster.before,real]
  change ((ns.map name).filter (fun v => v < name src.1.2)).card =
    (ns.filter (fun v => (Z).rawHostRank T vertex v < (Z).rawHostRank T vertex src.1.2)).card
  rw [←Finset.card_map name
    (s:=ns.filter (fun v=>(Z).rawHostRank T vertex v<(Z).rawHostRank T vertex src.1.2))]
  apply congrArg Finset.card
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨mem,lt⟩ := Finset.mem_filter.mp ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp mem
    exact Finset.mem_map.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,(ordered v _).1 lt⟩,rfl⟩
  · intro ha
    obtain ⟨v,mem,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨hv,lt⟩ := Finset.mem_filter.mp mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨v,hv,rfl⟩,(ordered v _).2 lt⟩

/-- Values stored once in the source receiver's local row. -/
def sourcePair (u : Host) (x : Local (blocks B) u) :=
  (sourceTicket B x.val x.property.1,
    DescentResetWindowFields.residentAddress B.next.placement (B.next.order.trans Fin.valEmbedding)
      S B.next.valid (blocks B) _ (sourceOccurrence B u x))

def sourcePairRow (h : Host) (j : Fin (totalLocal B)) :=
  (localOrigin B h j).bind (fun x=>if (blocks B).src x.val=h then some (sourcePair B h x) else none)

theorem source_pair_read (u : Host) (x : Local (blocks B) u) :
    sourcePairRow B ((blocks B).src x.val) (localRoster B _ (sourceOccurrence B u x))=
      some (sourcePair B u x) := by
  unfold sourcePairRow
  rw [source_lookup B u x]
  change (if (blocks B).src x.val = (blocks B).src x.val then some _ else none) = _
  rw [ite_eq_left rfl]
  rfl

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
