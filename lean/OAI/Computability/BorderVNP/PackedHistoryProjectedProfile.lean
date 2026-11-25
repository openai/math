import OAI.Computability.BorderVNP.PackedHistoryNormalizedProfile
import OAI.Computability.BorderVNP.PackedHistoryAllWordProjection

/-! # Original profile codes and augmented physical outputs on every shared input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open VPVNP BurstRAM VerifierNetwork RoutingISA RoutingISA.Evaluator Crossing BorderVNP.Epoch BorderVNP.Epoch.Round
open Cover Shortening Packing Catalog Adaptive PublicCapacity DiagonalResidueRAM
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {start T : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {shape : ℕ → Shape} {W A : ℕ → Type}
    [∀ t, Fintype (W t)] [∀ t, Fintype (A t)] {deep : S.floor+1+S.drop*T ≤ start}
    {good : ∀ t, State S start P bits shape W t → Prop}
    {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ} (M : Machine deep good V w)

variable {X : Type*} [Fintype X] {reserve o b rw : ℕ}
variable (leaf : Admissible good 0) (bottom : VerifierNetwork.Frame X (W 0)) (x : X → Bool)
variable (initial : bottom.eval x = leaf.val.words)
variable (widths : ℕ → ℕ) (order : ∀ j, Guess S start w j ≃ Fin (widths j))
variable (fits : broadcastWidth (fan S) widths T ≤ reserve)

/-- Equality of the two physical guard predicates, including the canonical padding test. -/
theorem projected_profile_valid (pick : ∀ j, W j → A j) (aug : Steps (fan S) T A (Guess S start w))
    (project : StepsProject pick aug M.steps) (front : VerifierNetwork.Frame X (A 0))
    (front_eq : front.eval x ∘ pick 0 = bottom.eval x) (profile : Fin reserve → Bool) :
    let ord := broadcastOrder (fan S) widths order T
    validProfile ord fits (fun g => flag aug T le_rfl (repeatLeaf (fan S) front T) x g = true) profile ↔
      validProfile ord fits (fun g => flag M.steps T le_rfl (repeatLeaf (fan S) bottom T) x g = true) profile := by
  intro ord
  apply and_congr _ Iff.rfl
  exact iff_of_eq (congrArg (· = true)
    (project.repeatLeaf T le_rfl front bottom x x front_eq (readProfile ord fits profile)).2)

/-- The original chronological bit code enumerates all physically accepted
augmented profiles, with exactly the same reserved word. -/
noncomputable def projectedNativeCode (pick : ∀ j, W j → A j) (aug : Steps (fan S) T A (Guess S start w))
    (project : StepsProject pick aug M.steps) (front : VerifierNetwork.Frame X (A 0))
    (front_eq : front.eval x ∘ pick 0 = bottom.eval x) :
    (packHistory leaf M.epoch T).Index ≃ {profile : Fin reserve → Bool //
      validProfile (broadcastOrder (fan S) widths order T) fits
        (fun g => flag aug T le_rfl (repeatLeaf (fan S) front T) x g = true) profile} :=
  (M.nativeCode leaf bottom x initial widths order fits).trans
    (Equiv.subtypeEquivRight fun profile =>
      (M.projected_profile_valid bottom x widths order fits pick aug project front front_eq profile).symm)

/-- Reserve decoding followed by the actual augmented circuit gives the field
array emitted on the original choice tuple. -/
theorem projected_emittedWords (aug : Steps (fan S) T A (Guess S start w)) (front : VerifierNetwork.Frame X (A 0))
    (emit : VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ A T) (Fin o × Fin b))
    {profile : Fin reserve → Bool} {q : (packHistory leaf M.epoch T).Index}
    (eq : (M.nativeCode leaf bottom x initial widths order fits q).val = profile) (i : Fin o) :
    emittedWords (compile aug T le_rfl (repeatLeaf (fan S) front T)) (broadcastOrder (fan S) widths order T)
      fits emit x profile i = ParseBatchSort.value (fun j => emit.eval (Sum.elim (Sum.elim x profile)
        (output aug T le_rfl (repeatLeaf (fan S) front T) x (M.packBits leaf T le_rfl q))) (i,j)) := by
  subst profile
  change ParseBatchSort.value (fun j => emit.eval (Sum.elim (Sum.elim x _)
    (output aug T le_rfl (repeatLeaf (fan S) front T) x (readProfile _ fits _))) (i,j)) = _
  rw [M.nativeCode_readProfile]

/-- The complete augmented profile program accepts precisely the original codes,
including the test on unused profile slots. It emits its own extra terminal
fields on the same chronological choices, with all true pin traces and costs. -/
theorem projected_native_profile_outputs (pick : ∀ j, W j → A j) (aug : Steps (fan S) T A (Guess S start w))
    (project : StepsProject pick aug M.steps) (front : VerifierNetwork.Frame X (A 0))
    (front_eq : front.eval x ∘ pick 0 = bottom.eval x)
    (emit : VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ A T) (Fin o × Fin b))
    (profile : Fin reserve → Bool) (body : Code) (guesses : ℕ) (pub : Arg → Word rw) (mac : TeamOpcode.Macros rw 8)
    (bank : Bank rw) (mem : Memory rw) (time dest : ℕ) {resident : (Fin guesses → Bool) → Memory rw → Prop} :
    let history := compile aug T le_rfl (repeatLeaf (fan S) front T)
    let ord := broadcastOrder (fan S) widths order T
    let ok := validProfile ord fits (fun g => history.eval (Sum.elim x g) (.inr ()) = true) profile
    let code := M.nativeCode leaf bottom x initial widths order fits
    ProfilePaths body guesses pub mac bank mem ok time dest (emittedWords history ord fits emit x profile) resident →
    (Nonempty (Returns body pub mac bank mem) ↔ ∃! q, (code q).val = profile) ∧
    ∀ q, (code q).val = profile → ∃ E : (Fin guesses → Bool) ≃ Returns body pub mac bank mem, ∀ g,
      (E g).val.1.flatMap TeamRAM.Event.choices = List.ofFn g ∧ traceCost (E g).val.1 ≤ time ∧
      signedWeight (E g).val.1 = 1 ∧ resident g (E g).val.2.2 ∧ ∀ i,
      readings (E g).val.2.2 (dest+i.val) = ParseBatchSort.value (fun j => emit.eval
        (Sum.elim (Sum.elim x profile) (output aug T le_rfl (repeatLeaf (fan S) front T) x (M.packBits leaf T le_rfl q))) (i,j)) := by
  intro history ord ok code paths
  have valid : ok ↔ ∃! q, (code q).val = profile := by
    exact (M.projected_profile_valid bottom x widths order fits pick aug project front front_eq profile).trans
      (M.nativeCode_valid leaf bottom x initial widths order fits profile)
  refine ⟨paths.passes.trans valid,fun q eq => ?_⟩
  have accepted : ok := valid.mpr ⟨q,eq,fun p hp => code.injective (Subtype.ext (hp.trans eq.symm))⟩
  obtain ⟨E,eff⟩ := paths.outputs accepted
  refine ⟨E,fun g => ⟨(eff g).1,(eff g).2.1,(eff g).2.2.1,paths.memory (E g) g (eff g).1,fun i => ?_⟩⟩
  exact ((eff g).2.2.2 i).trans (M.projected_emittedWords leaf bottom x initial widths order fits aug front emit eq i)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
