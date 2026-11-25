import OAI.Computability.BorderVNP.PackedHistoryNormalizedBits
import OAI.Computability.BorderVNP.PackedHistoryGeometryBranch

/-! # Native profile codes for the calibrated enriched pack-history machine

The actual machine already stores the admissibility proof in every boundary state. Its
concrete chronological choice codes give the native validator all original dependent
histories and all terminal words, including zero-width rows and integral route choices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open VPVNP BurstRAM VerifierNetwork RoutingISA RoutingISA.Evaluator Crossing BorderVNP.Epoch BorderVNP.Epoch.Round
open Cover Shortening Packing Catalog Adaptive PublicCapacity DiagonalResidueRAM
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

private theorem transfer_correct {k t : ℕ} {A : ℕ → Type*} {W G : ℕ → Type} [∀ j, Fintype (W j)] [∀ j, Fintype (G j)]
    {s p : System k t A} (h : s = p) (codec : Codec s G) (rep : Represents A W) (steps : Steps k t W G)
    (proof : LocalCorrect codec rep steps) : LocalCorrect (h ▸ codec) rep steps := by cases h; exact proof

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {start T : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {shape : ℕ → Shape} {W : ℕ → Type}
    [∀ t, Fintype (W t)] {deep : S.floor+1+S.drop*T ≤ start}
    {good : ∀ t, State S start P bits shape W t → Prop}
    {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ} (M : Machine deep good V w)

/-- Every state of the calibrated machine already carries its boundary certificate. -/
theorem closed : Capacity.Closed (outerSystem T M.epoch) (fun _ _ => True) := fun _ _ _ _ _ => trivial

/-- The machine's local count-word table in the repeated-pack presentation. -/
noncomputable def outerCodec : Codec (outerSystem T M.epoch) (Guess S start w) := M.system_eq ▸ M.codec

/-- Restriction to the certified native states keeps the original histogram index and its word. -/
noncomputable def profileCodec : Codec (Capacity.restrict (outerSystem T M.epoch) (fun _ _ => True) M.closed)
    (Guess S start w) where
  word j hj c := M.outerCodec.word j hj (fun i => (c i).val)
  injective j hj c := M.outerCodec.injective j hj (fun i => (c i).val)

/-- Each compiled local guard and all output bits have their actual machine semantics.
This discharges the verifier premise of the signed and finite physical profile entry points. -/
theorem profileCorrect : LocalCorrect M.profileCodec (fun j z a => represents (good := good) j z a.val) M.steps := by
  have h := transfer_correct M.system_eq M.codec (represents (good := good)) M.steps M.correct
  constructor
  · exact fun j hj c y g hy => h.valid j hj (fun i => (c i).val) y g hy
  · exact fun j hj c y g q hy eq => h.next j hj (fun i => (c i).val) y g q hy eq

variable {X : Type*} [Fintype X] {reserve o b rw : ℕ}
variable (leaf : Admissible good 0) (bottom : VerifierNetwork.Frame X (W 0)) (x : X → Bool)
variable (initial : bottom.eval x = leaf.val.words)
variable (widths : ℕ → ℕ) (order : ∀ j, Guess S start w j ≃ Fin (widths j))
variable (fits : broadcastWidth (fan S) widths T ≤ reserve)

/-- The forward map writes the actual chronological bits. The bounded verifier
gives the cardinality of its accepted bank, so injectivity of those concrete
words makes the encoding onto as well. -/
private noncomputable def checkedBits : (packHistory leaf M.epoch T).Index ≃
    {g : Slot (fan S) (Guess S start w) T → Bool //
      flag M.steps T le_rfl (repeatLeaf (fan S) bottom T) x g = true} := by
  let write := fun q : (packHistory leaf M.epoch T).Index =>
    (⟨M.packBits leaf T le_rfl q, (M.packBits_correct leaf bottom x initial T le_rfl q).1⟩ :
      {g // flag M.steps T le_rfl (repeatLeaf (fan S) bottom T) x g = true})
  apply Equiv.ofBijective write
  exact (Fintype.bijective_iff_injective_and_card write).mpr
    ⟨fun _ _ eq => M.packBits_injective leaf T le_rfl (congrArg Subtype.val eq),
      Fintype.card_congr (acceptedOuterBounded M.epoch (fun _ _ => True) M.closed ⟨leaf,trivial⟩
        M.profileCodec (represents (good := good)) M.steps M.profileCorrect bottom x initial)⟩

/-- The finite reserved profile word of each original history of the actual calibrated epochs. -/
noncomputable def nativeCode : (packHistory leaf M.epoch T).Index ≃
    {profile : Fin reserve → Bool // validProfile (broadcastOrder (fan S) widths order T) fits
      (fun q => (compile M.steps T le_rfl (repeatLeaf (fan S) bottom T)).eval (Sum.elim x q) (.inr ()) = true) profile} :=
  acceptedBroadcastOfEquiv _ fits _ (M.checkedBits leaf bottom x initial)

/-- Reading the active positions restores every child transcript and local
histogram of the original history, in their circuit slot order. -/
theorem nativeCode_readProfile (q : (packHistory leaf M.epoch T).Index) :
    readProfile (broadcastOrder (fan S) widths order T) fits
      (M.nativeCode leaf bottom x initial widths order fits q).val = M.packBits leaf T le_rfl q :=
  readProfile_of_broadcast _ fits _ (M.checkedBits leaf bottom x initial) q

/-- Decoding the broadcast for this actual pack history yields all of its
stored terminal words, including the physical row and route arrays. -/
theorem nativeCode_state (q : (packHistory leaf M.epoch T).Index) :
    output M.steps T le_rfl (repeatLeaf (fan S) bottom T) x
      (readProfile (broadcastOrder (fan S) widths order T) fits
        (M.nativeCode leaf bottom x initial widths order fits q).val) =
      ((packHistory leaf M.epoch T).term q).val.words := by
  rw [M.nativeCode_readProfile]
  exact (M.packBits_correct leaf bottom x initial T le_rfl q).2

/-- A word is valid precisely when one native history writes it. -/
theorem nativeCode_valid (profile : Fin reserve → Bool) :
    validProfile (broadcastOrder (fan S) widths order T) fits
      (fun g => flag M.steps T le_rfl (repeatLeaf (fan S) bottom T) x g = true) profile ↔
      ∃! q, (M.nativeCode leaf bottom x initial widths order fits q).val = profile := by
  let code := M.nativeCode leaf bottom x initial widths order fits
  constructor
  · intro h
    have eq := congrArg Subtype.val (code.apply_symm_apply ⟨profile,h⟩)
    exact ⟨code.symm ⟨profile,h⟩,eq,fun p hp => code.injective (Subtype.ext (hp.trans eq.symm))⟩
  · rintro ⟨q,h,_⟩
    exact h ▸ (code q).property

/-- The physical geometry frame on a history's word reads its exact terminal
state, with the full reserved word retained on the public pins. -/
theorem nativeCode_emittedWords (emit : VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ W T) (Fin o × Fin b))
    {q : (packHistory leaf M.epoch T).Index} {profile : Fin reserve → Bool}
    (eq : (M.nativeCode leaf bottom x initial widths order fits q).val = profile) (i : Fin o) :
    emittedWords (compile M.steps T le_rfl (repeatLeaf (fan S) bottom T))
      (broadcastOrder (fan S) widths order T) fits emit x profile i =
    ParseBatchSort.value (fun j => emit.eval
      (Sum.elim (Sum.elim x profile) ((packHistory leaf M.epoch T).term q).val.words) (i,j)) := by
  subst profile
  change ParseBatchSort.value (fun j => emit.eval (Sum.elim (Sum.elim x _)
    (output M.steps T le_rfl (repeatLeaf (fan S) bottom T) x (readProfile _ fits _))) (i,j)) = _
  rw [M.nativeCode_state]

/-- The true calibrated machine, as seen by the returning signed or field profile prefix.
All row words are computed on the original history's exact terminal assignment. -/
theorem native_profile_outputs (emit : VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ W T) (Fin o × Fin b))
    (profile : Fin reserve → Bool) (body : Code) (guesses : ℕ) (pub : Arg → Word rw) (mac : TeamOpcode.Macros rw 8)
    (bank : Bank rw) (mem : Memory rw) (time dest : ℕ) {resident : (Fin guesses → Bool) → Memory rw → Prop} :
    let history := compile M.steps T le_rfl (repeatLeaf (fan S) bottom T)
    let ord := broadcastOrder (fan S) widths order T
    let ok := validProfile ord fits (fun g => history.eval (Sum.elim x g) (.inr ()) = true) profile
    let code := M.nativeCode leaf bottom x initial widths order fits
    ProfilePaths body guesses pub mac bank mem ok time dest (emittedWords history ord fits emit x profile) resident →
    (Nonempty (Returns body pub mac bank mem) ↔ ∃! q, (code q).val = profile) ∧
    ∀ q, (code q).val = profile → ∃ E : (Fin guesses → Bool) ≃ Returns body pub mac bank mem, ∀ g,
      (E g).val.1.flatMap TeamRAM.Event.choices = List.ofFn g ∧ traceCost (E g).val.1 ≤ time ∧
      signedWeight (E g).val.1 = 1 ∧ resident g (E g).val.2.2 ∧ ∀ i,
      readings (E g).val.2.2 (dest+i.val) = ParseBatchSort.value (fun j => emit.eval
        (Sum.elim (Sum.elim x profile) ((packHistory leaf M.epoch T).term q).val.words) (i,j)) := by
  intro history ord ok code paths
  refine ⟨paths.passes.trans (M.nativeCode_valid leaf bottom x initial widths order fits profile),fun q eq => ?_⟩
  have passed : ok := by dsimp only [ok]; rw [← eq]; exact (code q).property
  obtain ⟨E,eff⟩ := paths.outputs passed
  exact ⟨E,fun g => ⟨(eff g).1,(eff g).2.1,(eff g).2.2.1,paths.memory (E g) g (eff g).1,fun i =>
    ((eff g).2.2.2 i).trans (M.nativeCode_emittedWords leaf bottom x initial widths order fits emit eq i)⟩⟩

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
