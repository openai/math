import OAI.Hierarchy.DescentClosedRosterCoverage
import OAI.Hierarchy.DescentResetWindowStemOrder

namespace OAI
/-! # The first signed block of the genuine reset candidate roster -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
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
local notation "Host" => DescentSharedCableNames.Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "widthsAgree" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub widthsAgree (Z).bank (Z).tables
local notation "key" => DescentOrderedReset.grains W B.count B.order


local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)


local notation "Slot" => Fin (2^(m-c))×Fin (2*(A).cap)

def stemIndex (s : Bool) (place : Slot) : Fin (totalLocal B) :=
  let raw : Fin (stemsCount B):=finProdFinEquiv (finTwoEquiv.symm s,finProdFinEquiv place)
  raw.castLE (Nat.le_add_right ..)

/-- The padding after the signed-donor slab cannot supply any of its positive
slots. Within the slab the old signed donor and the receiver determine every
original cable, including both occurrences when old endpoints coincide. -/
theorem stem_index_iff (u : Host) (s : Bool) (slot : Slot) (x : Local (blocks B) u) :
    localOrigin B u (stemIndex B s slot)=some x ↔
      ∃j : (old).graph.Edge, x.val=stemParent B (s,j) ∧ slot=priorStemSlot B s j := by
  rw [local_read]
  constructor
  · intro yes
    have atRank:=congrArg Fin.val yes
    have under : (localRoster B u x).val<stemsCount B := by
      rw [yes]
      exact (finProdFinEquiv (finTwoEquiv.symm s,finProdFinEquiv slot)).isLt
    rcases x with ⟨e,active⟩
    obtain ⟨tag,rfl⟩ : ∃tag,(motherNames B).symm tag=e :=
      ⟨motherNames B e,(motherNames B).symm_apply_apply e⟩
    rcases tag with ⟨t,j⟩|term|link|priv
    · change (localRoster B u ⟨stemParent B (t,j),active⟩).val=_ at atRank
      rw [stem_number B u t j active] at atRank
      have same := finProdFinEquiv.injective (Fin.ext atRank)
      have sign := finTwoEquiv.symm.injective (congrArg Prod.fst same)
      subst t
      exact ⟨j,rfl,(finProdFinEquiv.injective (congrArg Prod.snd same)).symm⟩
    · change (localRoster B u ⟨trunkParent B term,active⟩).val<_ at under
      rw [trunk_number B u term active] at under
      omega
    · change (localRoster B u ⟨contactParent B link,active⟩).val<_ at under
      rw [contact_number B u link active] at under
      omega
    · change (localRoster B u ⟨privateWire B priv,active⟩).val<_ at under
      rw [private_number B u priv active] at under
      omega
  · rintro ⟨j,same,rfl⟩
    rcases x with ⟨e,live⟩
    change e=_ at same
    subst e
    exact Fin.ext (stem_number B u s j live)

/-- A missing or wrong-polarity predecessor slot provides no physical
candidate. A live slot is filtered further by membership at this receiver. -/
theorem stem_slot_iff (u : Host) (s : Bool) (slot : Slot) (x : Local (blocks B) u) :
    localOrigin B u (stemIndex B s slot)=some x ↔ ∃j : (old).graph.Edge,
      x.val=stemParent B (s,j) ∧ priorStemPanel B u s slot=some (beforeStem B j) := by
  rw [stem_index_iff]
  constructor
  · rintro ⟨j,same,rfl⟩
    refine ⟨j,same,priorStemPanel_read B u s j ?_⟩
    rw [←same]
    exact x.property.2
  · rintro ⟨j,same,read⟩
    exact ⟨j,same,(panel_sound A before S input.valid digitsIn B.frame.basis fits _ _ _ _ read).2⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
