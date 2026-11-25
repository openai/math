import OAI.Computability.MultitapeWeakETH.ShrinkSupplyTape
import OAI.Computability.VPVNP.PairShrinkRoleMapLabels

/-! # The incident supply coordinates of a selected resident map -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open IntegerMultiplication VPVNP Compression Compression.ShrinkMotif NetworkKernel PairSimulation
open LocalHistory MapResidentRows MotifEntry NodeArguments
open private movedHalf from OAI.Computability.VPVNP.PairShrinkPartyNative
open private readSupplyEnd layoutCases_absorbed from OAI.Computability.VPVNP.ShrinkSupplyLocal
open scoped Classical
noncomputable section

/-- Move the parent packet to an equal site while preserving its independent half assignments. -/
def atSite {N : Network} {u v : N.Site} (h : u = v) (z : N.Half u) : N.Half v := movedHalf h z

theorem packed_atSite {a g : ℕ} (X : State a g) {u v : X.network.Site} (h : u = v)
    (z : X.network.Half u) : packed X v (atSite h z) = packed X u z := by cases h; rfl

private theorem bits_eq {n : ℕ} (x : Fin (2^n)) : inputBits x = RAMSerialization.wordBits n x := by
  funext i
  exact LiveHeader.testBit_wordBits _ _

variable {a b g pad : ℕ} (X : State a (packingLaneBits a g)) (layout : Bool) (subdiv : Fin 4 → ℕ)
    (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
    {next : Equiv.Perm (X.Base × BitWord (packingTagBits (2^a)))}
    (I : X.packingData.ShrinkIndex layout subdiv next (2^b) pad) (pos : ∀ t, 0 < subdiv t)
    (m : X.packingData.Motif) (j : Fin 6)
local notation "P" => X.packingData
local notation "width" => (fun m t => widths m (layout,t))
local notation "Y" => X.shrinkOutputState layout subdiv width I

set_option maxHeartbeats 1300000 in
/-- The layout selects the parent packet or common hidden field independently
at each end. These are the six-party matrix's original binary coordinates. -/
theorem supply_coordinates (v : Site X) (loc : (P).shrinkPartySite layout m j = v)
    (h : Placed ((P).shrinkInternalOwner layout) (internalLabel widths layout) v)
    (z : (Y).network.Half v) (bits : Bool → (Bool × Fin 4) → Bits.Word)
    (shared : ∀ dir t (hit : j = ShrinkHiddenSlots.party layout t dir),
      let own := (loc.symm.trans (congrArg ((P).shrinkPartySite layout m) hit)).trans
        (ShrinkHiddenSlots.party_owner X layout m t dir)
      bits dir (!layout,t) = List.ofFn (RAMSerialization.wordBits _ (h (m,t) own)))
    (surviving : ∀ dir t (hit : j = ShrinkSurvivingOperands.party layout t dir),
      let own := (loc.symm.trans (congrArg ((P).shrinkPartySite layout m) hit)).trans
        (ShrinkSurvivingOperands.party_site X layout m t dir)
      bits dir (layout,t) = List.ofFn (ShrinkSurvivingOperands.operand X layout subdiv width I pos m t dir (atSite own z))) :
    let arg := (P).shrinkLocalSupplyArg layout subdiv widths I pos m j (loc.symm ▸ h) (loc.symm ▸ z)
    (∀ e (hit : j = supply.src e), bits false e = List.ofFn (inputBits (arg.1 e hit))) ∧
    (∀ e (hit : j = supply.dst e), bits true e = List.ofFn (inputBits (arg.2 e hit))) := by
  subst v
  constructor
  · rintro ⟨l,t⟩ hit
    subst j
    by_cases active : l = layout
    · subst l
      have live := surviving false t rfl
      have word := ShrinkSurvivingOperands.mapColumn_bits X layout subdiv I pos m t widths false h z
      exact live.trans (congrArg List.ofFn (word.symm.trans (bits_eq _).symm))
    · obtain rfl := Bool.eq_not_of_ne active
      simp only [PackingData.shrinkLocalSupplyArg,readSupplyEnd,layoutCases_absorbed,bits_eq]
      exact shared false t rfl
  · rintro ⟨l,t⟩ hit
    subst j
    by_cases active : l = layout
    · subst l
      have live := surviving true t rfl
      have word := ShrinkSurvivingOperands.mapColumn_bits X layout subdiv I pos m t widths true h z
      exact live.trans (congrArg List.ofFn (word.symm.trans (bits_eq _).symm))
    · obtain rfl := Bool.eq_not_of_ne active
      simp only [PackingData.shrinkLocalSupplyArg,readSupplyEnd,layoutCases_absorbed,bits_eq]
      exact shared true t rfl

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
