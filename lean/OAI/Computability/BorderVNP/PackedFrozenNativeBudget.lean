import OAI.Computability.BorderVNP.PackedInheritedWorkGeometryCosts
import OAI.Computability.BorderVNP.PackedFrozenSelectedNodeCost
import OAI.Computability.BorderVNP.PackedFrozenNativeFrames
import OAI.Computability.BorderVNP.PackedFrozenPrepBudget
import OAI.Computability.BorderVNP.PackedFrozenHistoryBudget

/-! # Total gate and guess budget for the native chronological record tree -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Inherited WorkWords FrozenTape ProgramSchemas Diagonal TeamScales Filter EnrichedOuter
open VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 5500

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The augmented machine's gates include every compiled frozen-row writer
and its measured state fields. The remaining inputs to this estimate are
the initial physical row count, the original selected geometric gate receipts
and the size of the actual bottom circuit. -/
theorem eventually_native_budget (hm : 0 < m) {u x : ℕ} (scales : EpochScales S u x)
    (A a B b J j C₀ Cf fExp Q : ℕ) :
    ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
      let T := epochs scales.τ n
      let start := CoverScale.initialDepth (Cube D) r n
      let w := 60*logWidth r n
      let V := CoverScale.sites (Cube D) start
      ∀ (deep : S.floor+1+S.drop*T ≤ start) {P : Type} [Fintype P] {bits : P → ℕ}
        {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} (R : Compiled bits deep budget cap w),
        Machine.LocalSizes (r:=r) (n:=n) A a B b J j R.machine →
      ∀ (base : Format), Fintype.card base.Rows ≤ C₀*physicalRows (bottom (D:=D) start) →
      ∀ (header : WorkWords.Ports V) (leaf : P ↪ Fin V) (wr : WidthRanges S start T w)
        {σ : Type} [Fintype σ] (f : Frame σ (outerPins S start w base 0)),
        f.size+1 ≤ rowWork Cf V (logWidth r n) fExp (bottom (D:=D) start) →
        ((Q*(compile (R.tapeSteps base header leaf wr hm) T le_rfl (repeatLeaf (fan S) f T)).size+
          Fintype.card (Slot (fan S) (Machine.Guess S start (fun _ _ => w)) T) : ℕ) : ℝ) < r*(n:ℝ)^(92/100:ℝ) := by
  obtain ⟨Cn,p,writer⟩ := eventually_frozen_node_work S hm scales C₀
  obtain ⟨Cp,prepare⟩ := eventually_tape_pre S scales C₀
  let C := Cf+Cp+(Cn+186+widthNodeFactor S+(2*S.fanIn+4))
  let h := max fExp (max 4 (max 3 p))
  obtain ⟨ω,hω,complete⟩ := eventually_tape_budget S A a B b J j 2 C h Q scales
  refine ⟨ω,hω,?_⟩
  filter_upwards [writer,prepare,complete,eventually_ranges S scales (fun _ => 0) (fun _ => 0),
    eventually_ge_atTop 1] with n localNode localPre work ranges hn
  intro r hr bound T start w V deep P fp bits budget cap R sizes base rows header leaf wr σ fs f bottomSize
  have hL : 1≤logWidth r n := by
    rw [public_logWidth]
    exact (Nat.clog_mono_right 2 (by nlinarith only [Nat.mul_le_mul hn hr] : 2≤2*n*r)).trans' (by decide)
  apply work r hr bound P bits deep budget cap R sizes base f
    (fun t ht => R.tapePre base t ht (prepHeader t header) (wr.initial t ht))
    (fun t ht => R.stageSteps base header leaf wr hm t ht)
  constructor
  · exact bottomSize.trans (rowWork_mono _ hL (by dsimp only [C]; omega) (le_max_left ..))
  · intro t ht
    have pre := localPre r hr base rows deep R t ht (prepHeader t header) (wr.initial t ht)
    exact pre.trans (Nat.add_le_add (Nat.le_mul_of_pos_left _ (by decide : 0<2))
      (rowWork_mono _ hL (by dsimp only [C]; omega) ((le_max_left ..).trans (le_max_right ..))))
  · intro t ht i hi
    let k : Fin S.rounds := ⟨i,hi⟩
    have stages := localNode r hr (Fintype.card base.Rows) rows t ht k
    have native := R.tapeNative_rowWork base hm wr header leaf ht k stages ((ranges r hr).2 t ht k) hL ((ranges r hr).1 t k)
    change (R.stageSteps base header leaf wr hm t ht k.val k.isLt).size + _ ≤ _
    rw [R.stageSteps_size]
    exact native.trans (Nat.add_le_add_left (rowWork_mono _ hL (by dsimp only [C]; omega)
      ((le_max_right ..).trans (le_max_right ..))) _)

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
