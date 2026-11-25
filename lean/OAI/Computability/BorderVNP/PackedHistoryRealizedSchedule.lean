import OAI.Computability.BorderVNP.PackedHistoryMeasuredMachine
import OAI.Computability.BorderVNP.PackedHistoryNormalizedSelected
import OAI.Computability.BorderVNP.ShortenEnrichedSiteEpoch

/-! # The full realized Boolean history on the calibrated site schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Adaptive Packing PublicCapacity
open Diagonal TeamScales Filter EnrichedOuter VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The actual gate and guess size of the concrete calibrated machine, including
subdivision, all selected source frames, terminal motion and the repeated grid
initializer. The schedule chooses all these gate lists before the child's
field tables and before any histogram word is supplied. -/
def WithinHistoryBudget {P : Type} [Fintype P] (bits : P → ℕ) {r n start T : ℕ}
    (deep : S.floor+1+S.drop*T ≤ start) (base Q : ℕ)
    (R : Compiled bits deep (boundaryBudget S base) (innerCap S base) (60*logWidth r n)) : Prop :=
  ∀ {σ : Type} [Fintype σ]
    (f : Frame σ (Boundary.Pins S start (boundaryShape S start) (60*logWidth r n) 0)), f.size≤2 →
    ((Q*(compile R.machine.steps T le_rfl (repeatLeaf (fan S) f T)).size+
      Fintype.card (Slot (fan S) (Machine.Guess S start (fun _ _ => 60*logWidth r n)) T) : ℕ) : ℝ) <
      r*(n:ℝ)^(92/100:ℝ)

set_option maxHeartbeats 1100000 in
/-- Every sufficiently large admissible processor obtains a concrete machine.
Its gate estimate uses the actual measured boundary and source frames supplied
by compilation, and every count pin is charged once at its own node. -/
theorem eventually_realized_sizes (hm : 0 < m) {a x : ℕ} (scales : EpochScales S a x)
    (physical : ∀ d ≥ S.floor, S.FitsLevels d ∧ S.HasLeaves d ∧ S.RunsEnriched.{max 1 u,u} d) (Q : ℕ) :
    ∃ A a₀ B b J j : ℕ, ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
      ∀ base : ℕ, 1+base ≤ TeamScales.width n (1/2:ℝ) → ∀ (P : Type) [Fintype P] (bits : P → ℕ),
        let T := epochs scales.τ n
        let start := CoverScale.initialDepth (Cube D) r n
        ∃ deep : S.floor+1+S.drop*T ≤ start,
        ∃ R : Compiled bits deep (boundaryBudget S base) (innerCap S base) (60*logWidth r n),
          Machine.LocalSizes (r:=r) (n:=n) A a₀ B b J j R.machine ∧
          WithinHistoryBudget S (n:=n) (r:=r) bits deep base Q R := by
  obtain ⟨A,a₀,B,b,J,j,source⟩ := eventually_compiled S hm scales physical
  obtain ⟨ω,hω,work⟩ := Machine.eventually_machine_history S A a₀ B b J j Q scales
  refine ⟨A,a₀,B,b,J,j,ω,hω,?_⟩
  filter_upwards [source,work] with n comp bound
  intro r hr room base small P fp bits T start
  obtain ⟨deep,R,raw⟩ := comp r hr base small P bits
  refine ⟨deep,R,?_⟩
  let w := 60*logWidth r n
  have localSize : Machine.LocalSizes (r:=r) (n:=n) A a₀ B b J j R.machine := by
    constructor
    · exact fun t ht => (raw t ht).1
    · exact fun t ht => (raw t ht).2.1
    · intro t ht i hi
      exact (Nat.le_add_right _ _).trans ((raw t ht).2.2 ⟨i,hi⟩)
    · intro t ht i hi
      let z : Fin S.rounds := ⟨i,hi⟩
      have pins := (Fintype.card_congr (Physical.pinEquiv (I := Cube D) (e := e)
        (B := fun i => (S.source.pattern i).bins.Bin) (depth := S.level (offset S start t))
        (fun _ => w) z)).symm
      exact pins.le.trans ((Nat.le_add_left _ _).trans ((raw t ht).2.2 z))
  refine ⟨localSize,?_⟩
  intro σ inst f hf
  exact bound r hr room deep P bits (Boundary.Pins S start (boundaryShape S start) w)
    (fun t => S.source.StatePins S.last (S.high (offset S start t))
      (fun j => (before S start t j).sites) (fun j => (before S start t j).edges) w)
    (Boundary.Good (S:=S) (start:=start) (shape:=boundaryShape S start) (bits:=bits) (w:=w) (boundaryBudget S base))
    R.machine localSize f hf

set_option maxHeartbeats 1100000 in
/-- The calibrated compiler realizes the full physical histogram circuit at every sufficiently large processor length. -/
theorem eventually_realized_history (hm : 0 < m) {a x : ℕ} (scales : EpochScales S a x)
    (physical : ∀ d ≥ S.floor, S.FitsLevels d ∧ S.HasLeaves d ∧ S.RunsEnriched.{max 1 u,u} d) (Q : ℕ) :
    ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
      ∀ base : ℕ, 1+base ≤ TeamScales.width n (1/2:ℝ) → ∀ (P : Type) [Fintype P] (bits : P → ℕ),
        let T := epochs scales.τ n
        let start := CoverScale.initialDepth (Cube D) r n
        ∃ deep : S.floor+1+S.drop*T ≤ start,
        ∃ R : Compiled bits deep (boundaryBudget S base) (innerCap S base) (60*logWidth r n),
          WithinHistoryBudget S (n:=n) (r:=r) bits deep base Q R := by
  obtain ⟨A,a₀,B,b,J,j,ω,hω,haveR⟩ := eventually_realized_sizes S hm scales physical Q
  refine ⟨ω,hω,?_⟩
  filter_upwards [haveR] with n result
  intro r hr room base small P fp bits T start
  obtain ⟨deep,R,_,bound⟩ := result r hr room base small P bits
  exact ⟨deep,R,bound⟩

/-- A concrete calibrated schedule exists before the epoch parameters, batch
length, processor count and all input/output fields. At every sufficiently
large admissible size its actual enriched history meets the strict rate. -/
theorem exists_realized_schedule (e : PaidIdentity K D m) (hm : 0 < m) :
    ∃ S : SiteSchedule e, ∀ {a x : ℕ} (scales : EpochScales S a x) (Q : ℕ),
      ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
        ∀ base : ℕ, 1+base ≤ TeamScales.width n (1/2:ℝ) → ∀ (P : Type) [Fintype P] (bits : P → ℕ),
          let T := epochs scales.τ n
          let start := CoverScale.initialDepth (Cube D) r n
          ∃ deep : S.floor+1+S.drop*T ≤ start,
          ∃ R : Compiled bits deep (boundaryBudget S base) (innerCap S base) (60*logWidth r n),
            WithinHistoryBudget S (n:=n) (r:=r) bits deep base Q R := by
  obtain ⟨S,physical⟩ := exists_enriched_executions.{max 1 u,u} e hm
  exact ⟨S,fun scales Q => eventually_realized_history S hm scales physical Q⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
