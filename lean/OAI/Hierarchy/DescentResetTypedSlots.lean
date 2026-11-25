import OAI.Hierarchy.DescentClosedRosterCoverage

namespace OAI
/-! # Which genuine receiver-owned parent occupies each contact or private slot -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks DescentSharedCableNames
open DescentResetLocalRoster DescentParallelBase
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))



def contactShelfIndex (slot : Fin (contactCount B)) : Fin (totalLocal B) :=
  ⟨stemsCount B+1+slot.val,by have hi:=slot.isLt;unfold totalLocal;omega⟩

def privateShelfIndex (slot : Fin (privateCount B)) : Fin (totalLocal B) :=
  ⟨stemsCount B+1+contactCount B+slot.val,by have hi:=slot.isLt;unfold totalLocal;omega⟩

private theorem stem_below (u : Host) (s : Bool) (j : (W.granular B.count (z*G.b) B.fit).graph.Edge) (live : active (blocks B) u (stemParent B (s,j))) :
    (localRoster B u ⟨stemParent B (s,j),live⟩).val<stemsCount B := by
  rw [stem_number B u s j live]
  exact Fin.isLt _

theorem contact_shelf_iff (u : Host) (slot : Fin (contactCount B)) (x : Local (blocks B) u) :
    localOrigin B u (contactShelfIndex B slot)=some x ↔
      ∃ (c : (placement).Contact) (live : active (blocks B) u (contactParent B c)),
        x.val=contactParent B c ∧ contactDigit B u ⟨c,live⟩=slot := by
  rw [local_read]
  constructor
  · intro found
    have atSlot:=congrArg Fin.val found
    change (localRoster B u x).val=stemsCount B+1+slot.val at atSlot
    obtain ⟨e,live⟩:=x
    obtain ⟨tag,rfl⟩:=(motherNames B).symm.surjective e
    rcases tag with ⟨s,j⟩|t|c|p
    · have below:=stem_below B u s j live
      change (localRoster B u ⟨stemParent B (s,j),live⟩).val=_ at atSlot
      omega
    · change (localRoster B u ⟨trunkParent B t,live⟩).val=_ at atSlot
      have counted := (trunk_number B u t live).symm.trans atSlot
      omega
    · change (localRoster B u ⟨contactParent B c,live⟩).val=_ at atSlot
      have counted := (contact_number B u c live).symm.trans atSlot
      exact ⟨c,live,rfl,Fin.ext (by omega)⟩
    · change (localRoster B u ⟨privateWire B p,live⟩).val=_ at atSlot
      have counted := (private_number B u p live).symm.trans atSlot
      have below:=slot.isLt
      omega
  · rintro ⟨c,live,same,digit⟩
    obtain ⟨e,h⟩:=x
    change e=_ at same
    subst e
    apply Fin.ext
    exact (contact_number B u c h).trans (congrArg (fun j : Fin (contactCount B)=>stemsCount B+1+j.val) digit)

theorem private_shelf_iff (u : Host) (slot : Fin (privateCount B)) (x : Local (blocks B) u) :
    localOrigin B u (privateShelfIndex B slot)=some x ↔
      ∃ p : PrivateOccurrence B, x.val=privateWire B p ∧
        localPrivateId _ _ capacity (privateTicket B p)=slot := by
  rw [local_read]
  constructor
  · intro found
    have atSlot:=congrArg Fin.val found
    change (localRoster B u x).val=stemsCount B+1+contactCount B+slot.val at atSlot
    obtain ⟨e,live⟩:=x
    obtain ⟨tag,rfl⟩:=(motherNames B).symm.surjective e
    rcases tag with ⟨s,j⟩|t|c|p
    · have below:=stem_below B u s j live
      change (localRoster B u ⟨stemParent B (s,j),live⟩).val=_ at atSlot
      omega
    · change (localRoster B u ⟨trunkParent B t,live⟩).val=_ at atSlot
      have counted := (trunk_number B u t live).symm.trans atSlot
      omega
    · change (localRoster B u ⟨contactParent B c,live⟩).val=_ at atSlot
      have counted := (contact_number B u c live).symm.trans atSlot
      have below:=(contactDigit B u ⟨c,live⟩).isLt
      omega
    · change (localRoster B u ⟨privateWire B p,live⟩).val=_ at atSlot
      have counted := (private_number B u p live).symm.trans atSlot
      exact ⟨p,rfl,Fin.ext (by omega)⟩
  · rintro ⟨p,same,digit⟩
    obtain ⟨e,h⟩:=x
    change e=_ at same
    subst e
    apply Fin.ext
    exact (private_number B u p h).trans (congrArg (fun j : Fin (privateCount B)=>stemsCount B+1+contactCount B+j.val) digit)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
