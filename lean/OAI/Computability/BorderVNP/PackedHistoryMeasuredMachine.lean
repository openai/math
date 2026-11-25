import OAI.Computability.BorderVNP.PackedHistoryScheduleBudget
import OAI.Computability.BorderVNP.PackedHistoryNormalizedMachine

/-! # Counting the gate lists and literal count pins of the enriched history machine -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open Crossing Cover BorderVNP.Epoch Packing Shortening PublicCapacity Diagonal TeamScales Filter VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {n r start T : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {O : ℕ → Type} [∀ t, Fintype (O t)] {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)]
    {deep : S.floor+1+S.drop*T ≤ start}
    {good : ∀ t, State S start P bits (SelectedSchedule.boundary S start) O t → Prop}

/-- The compiler's local cost receipts, measured on precisely the frames in
the enriched machine. All rounds, including the final rounded row directory,
use the reserved processor word width. -/
structure LocalSizes (A a B b J j : ℕ) (M : Machine deep good V (fun _ _ => 60*logWidth r n)) : Prop where
  subdivision : ∀ t ht, (M t ht).pre.size ≤ startCost (Fintype.card (Cube D)) (SelectedSchedule.interiors S) A a
    (fan S) (S.high (offset S start t)) (60*logWidth r n) (SelectedSchedule.boundary S start t)
  terminal : ∀ t ht, (M t ht).post.size ≤ finishCost B b (offset S start t) (60*logWidth r n)
    (SelectedSchedule.boundary S start (t+1))
  round : ∀ t ht i (hi : i<S.rounds),
    let W := rowWork J (CoverScale.sites (Cube D) start) (logWidth r n) j ((SelectedSchedule.before S start t i).parallel S.fanIn)
    ((M t ht).step i hi).size + (2*S.fanIn+4) ≤ W
  counts : ∀ t (_ : t<T) i (_ : i<S.rounds), Fintype.card (Count S start t (fun _ => 60*logWidth r n) i) ≤
    rowWork J (CoverScale.sites (Cube D) start) (logWidth r n) j ((SelectedSchedule.before S start t i).parallel S.fanIn)

variable (S) (A a B b J j Q : ℕ)

set_option maxHeartbeats 900000 in
/-- The same compiled enriched circuit used in the acceptance and tensor
theorems and its whole public guess bank jointly satisfy the strict 0.92
bound. Its inputs are the raw cost receipts of the actual row compilers. -/
theorem eventually_machine_history {p x : ℕ} (scale : EpochScales S p x) :
    ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
      let T := epochs scale.τ n
      let start := CoverScale.initialDepth (Cube D) r n
      ∀ (deep : S.floor+1+S.drop*T ≤ start) (P : Type) [Fintype P] (bits : P → ℕ)
        (O : ℕ → Type) [∀ t, Fintype (O t)] (V : ℕ → ℕ → Type) [∀ t i, Fintype (V t i)]
        (good : ∀ t, State S start P bits (SelectedSchedule.boundary S start) O t → Prop)
        (M : Machine deep good V (fun _ _ => 60*logWidth r n)),
        LocalSizes (r:=r) (n:=n) A a B b J j M →
        ∀ {σ : Type} [Fintype σ] (f : Frame σ (O 0)), f.size≤2 →
          ((Q*(compile M.steps T le_rfl (repeatLeaf (fan S) f T)).size+
            Fintype.card (Slot (fan S) (Guess S start (fun _ _ => 60*logWidth r n)) T) : ℕ) : ℝ) <
            r*(n:ℝ)^(92/100:ℝ) := by
  obtain ⟨H,h,hboundary⟩ := boundary_costs (Cube D) 60 (Fintype.card (Cube D)) (SelectedSchedule.interiors S)
    A a B b (fan S)
  let C := 3+H+J
  let exp := max h j
  obtain ⟨ω,hω,work⟩ := SelectedSchedule.eventually_schedule_history S scale C exp Q
  refine ⟨ω,hω,?_⟩
  filter_upwards [work,SelectedSchedule.eventually_boundaries S scale,eventually_ge_atTop 1] with n bounds rows hn
  intro r hr hr' T start deep P _ bits O _ V _ good M cost σ _ f hf
  let L := logWidth r n
  let tiles := CoverScale.sites (Cube D) start
  have hL : 1≤L := by
    change 1 ≤ logWidth r n
    rw [public_logWidth]
    exact (Nat.clog_mono_right 2 (by nlinarith [Nat.mul_le_mul hn hr] : 2≤2*n*r)).trans' (by decide)
  have promote {X k : ℕ} (s : Shape) (hX : X≤C) (hk : k≤exp) :
      rowWork X tiles L k s ≤ rowWork C tiles L exp s :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ hX) (Nat.pow_le_pow_right hL hk)
  apply bounds r hr hr' σ O V (fun t => Count S start t (fun _ => 60*L)) f
    (fun t ht => (M t ht).step) (fun t ht => (M t ht).pre) (fun t ht => (M t ht).post)
  constructor
  · have hn' : 1 ≤ (SelectedSchedule.bottom (D:=D) start).volume tiles := by dsimp [Shape.volume]; omega
    have hc := Nat.le_mul_of_pos_right C hn'
    exact (show f.size+1≤C by dsimp [C]; omega).trans (hc.trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos hL)))
  · intro t ht
    have depth : S.high (offset S start t) ≤ start+1 := by
      rw [(levels S deep ht).2.2]
      dsimp [EnrichedOuter.depth]
      omega
    let s := SelectedSchedule.boundary S start t
    have hraw := (hboundary (r:=r) (n:=n) (z:=start+1) s hr hn ((rows r hr).1 t ht.le) depth le_rfl).1
    exact (cost.subdivision t ht).trans (hraw.trans (promote s (by dsimp [C]; omega) (le_max_left ..)))
  · intro t ht
    have depth : offset S start t ≤ start+1 := by dsimp [offset,EnrichedOuter.depth]; omega
    let s := SelectedSchedule.boundary S start (t+1)
    have hraw := (hboundary (r:=r) (n:=n) (z:=start+1) s hr hn ((rows r hr).1 (t+1) ht) depth le_rfl).2
    exact (cost.terminal t ht).trans (hraw.trans (promote s (by dsimp [C]; omega) (le_max_left ..)))
  · intro t ht i hi
    have up := promote ((SelectedSchedule.before S start t i).parallel S.fanIn)
      (show J≤C by dsimp [C]; omega) (le_max_right h j)
    exact ⟨(cost.round t ht i hi).trans up,(cost.counts t ht i hi).trans up⟩

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
