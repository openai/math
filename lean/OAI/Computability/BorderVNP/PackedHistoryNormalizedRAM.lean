import OAI.Computability.BorderVNP.PackedHistoryNormalizedProfile
import OAI.Computability.BorderVNP.PackedHistoryBroadcastRAM

/-! # Exact enriched pack histories in the copied physical common header -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open VPVNP BurstRAM VerifierNetwork RoutingISA Crossing BorderVNP.Epoch BorderVNP.Epoch.Round
open Cover Shortening Packing Catalog Adaptive PublicCapacity TeamContraction JointHeader
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {start T : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {shape : ℕ → Shape} {W : ℕ → Type}
    [∀ t, Fintype (W t)] {deep : S.floor+1+S.drop*T ≤ start}
    {good : ∀ t, State S start P bits shape W t → Prop}
    {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ} (M : Machine deep good V w)
    {X : Type*} [Fintype X] {reserve rw : ℕ}
    (leaf : Admissible good 0) (bottom : VerifierNetwork.Frame X (W 0)) (x : X → Bool)
    (initial : bottom.eval x = leaf.val.words)
    (widths : ℕ → ℕ) (order : ∀ j, Guess S start w j ≃ Fin (widths j))
    (fits : broadcastWidth (fan S) widths T ≤ reserve)

local notation "code" => M.nativeCode leaf bottom x initial widths order fits
local notation "ord" => broadcastOrder (fan S) widths order T
local notation "hist" => compile M.steps T le_rfl (repeatLeaf (fan S) bottom T)
local notation "valid" => validProfile ord fits (fun q => VerifierNetwork.Frame.eval hist (Sum.elim x q) (Sum.inr ()) = true)

/-- The sole original pack history matching a returning physical header, and
the exact complete terminal words reconstructed from its RAM addresses. -/
theorem decode_profile_RAM (mem : Memory rw) (base : ℕ) (passed : valid (profileRAM mem base)) :
    let q := (code).symm ⟨profileRAM mem base,passed⟩
    (∃! i, (code i).val = profileRAM mem base) ∧
      output M.steps T le_rfl (repeatLeaf (fan S) bottom T) x (readProfile ord fits (profileRAM mem base)) =
        ((packHistory leaf M.epoch T).term q).val.words := by
  intro q
  have eqv : code q = ⟨profileRAM mem base,passed⟩ := (code).apply_symm_apply _
  refine ⟨⟨q,congrArg Subtype.val eqv,fun i hi => (code).injective (Subtype.ext (hi.trans (congrArg Subtype.val eqv).symm))⟩,?_⟩
  have state := M.nativeCode_state leaf bottom x initial widths order fits q
  change output M.steps T le_rfl (repeatLeaf (fan S) bottom T) x (readProfile ord fits (code q).val) = _ at state
  rwa [eqv] at state

/-- A canonical transmitted history is decoded back to itself after the real
positive-width header copy. The arbitrary declaration, claim and padding fields
are all outside the occupied profile addresses. -/
theorem copied_profile_RAM {R d base tallyBits extra : ℕ} {mem : Memory rw} (hw : 0<rw)
    (q : (packHistory leaf M.epoch T).Index) (decl : List Bool) (claims : Fin R → Fin d → ℕ)
    (copy : FlatAt mem base (padded (evaluation (List.ofFn (code q).val ++ decl) tallyBits claims) extra)) :
    (∃ passed : valid (profileRAM mem base), (code).symm ⟨profileRAM mem base,passed⟩ = q) ∧
      output M.steps T le_rfl (repeatLeaf (fan S) bottom T) x (readProfile ord fits (profileRAM mem base)) =
        ((packHistory leaf M.epoch T).term q).val.words := by
  have h := profileRAM_eq_of_copy hw (code q).val decl claims copy
  have pass : valid (profileRAM mem base) := h ▸ (code q).property
  have back : (code).symm ⟨profileRAM mem base,pass⟩ = q :=
    (code).injective (((code).apply_symm_apply _).trans (Subtype.ext h))
  exact ⟨⟨pass,back⟩,back ▸ (M.decode_profile_RAM leaf bottom x initial widths order fits mem base pass).2⟩

/-- Every exported sparse geometry word uses the true terminal pin assignment
for the same decoded original history. The surrounding public pins are the
actual copied header, including its forced zero padding. -/
theorem emitted_profile_RAM {o b : ℕ} (mem : Memory rw) (base : ℕ)
    (passed : valid (profileRAM mem base)) (emit : VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ W T) (Fin o × Fin b)) :
    let q := (code).symm ⟨profileRAM mem base,passed⟩
    ∀ i, emittedWords hist ord fits emit x (profileRAM mem base) i =
      ParseBatchSort.value (fun j => emit.eval
        (Sum.elim (Sum.elim x (profileRAM mem base)) ((packHistory leaf M.epoch T).term q).val.words) (i,j)) := by
  intro q i
  exact M.nativeCode_emittedWords leaf bottom x initial widths order fits emit
    (congrArg Subtype.val ((code).apply_symm_apply ⟨profileRAM mem base,passed⟩)) i

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
