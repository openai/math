import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionTypes
import OAI.Optimization.LinearProgramming.PriceGame.ChargingActualProbe

/-! # Allocations of the selected local experts

The market chooses maximizing options for its representative raw values. An
agreement of the recorded feature comparisons transports this fact to the hidden
values. Repeated tuple slots denote one good and one market fraction. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

open Finset States.Mass TrialExecution

/-- Score of a tuple option, with zero for the outside option. -/
def slotValue (score : Fin 64 → ℚ) : Option (Fin 64) → ℚ
  | none => 0
  | some j => score j

private theorem outside_mem {N : ℕ} (s : Skeleton N) (hist : History N)
    (y : Vertex N s.level → ℚ) (j : Fin 64) :
    s.outsideTest hist y j ∈ s.testsAt ⟨s.level, y, hist⟩ := by
  unfold Skeleton.testsAt
  split
  · exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨j,rfl⟩, List.mem_cons_self⟩
  · rename_i he
    exact (he rfl).elim

private theorem pair_mem {N : ℕ} (s : Skeleton N) (hist : History N)
    (y : Vertex N s.level → ℚ) (j k : Fin 64) :
    s.pairTest y j k ∈ s.testsAt ⟨s.level, y, hist⟩ := by
  unfold Skeleton.testsAt
  split
  · exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨j,rfl⟩,
      List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨k,rfl⟩)⟩
  · rename_i he
    exact (he rfl).elim

/-- Agreement of the three-way comparisons on the probe's actual emitted tests
preserves all weak rankings of the 64 slots and the outside option, including ties. -/
theorem preserves_option_rankings {N : ℕ} (s : Skeleton N) (raw truth : Fin N → ℚ)
    (hist : History N) (y : Vertex N s.level → ℚ)
    (keeps : ∀ t ∈ s.testsAt ⟨s.level, y, hist⟩,
      compare (featureValue raw t.feature) t.threshold =
      compare (featureValue truth t.feature) t.threshold) :
    ∀ a b : Option (Fin 64),
      slotValue ((⟨s,raw⟩ : Expert N).utility hist y) a ≤
      slotValue ((⟨s,raw⟩ : Expert N).utility hist y) b →
      slotValue ((⟨s,truth⟩ : Expert N).utility hist y) a ≤
      slotValue ((⟨s,truth⟩ : Expert N).utility hist y) b := by
  have le_test {test : Test N} (ht : test ∈ s.testsAt ⟨s.level, y, hist⟩) :
      (featureValue raw test.feature ≤ test.threshold ↔ featureValue truth test.feature ≤ test.threshold) := by
    rw [← compare_le_iff_le, keeps test ht, compare_le_iff_le]
  have ge_test {test : Test N} (ht : test ∈ s.testsAt ⟨s.level, y, hist⟩) :
      (test.threshold ≤ featureValue raw test.feature ↔ test.threshold ≤ featureValue truth test.feature) := by
    rw [← compare_ge_iff_ge, keeps test ht, compare_ge_iff_ge]
  rintro (_ | j) (_ | k) h
  · exact le_rfl
  · change 0 ≤ (⟨s,raw⟩ : Expert N).utility hist y k at h
    change 0 ≤ (⟨s,truth⟩ : Expert N).utility hist y k
    rw [Skeleton.outsideTest_difference] at h ⊢
    exact sub_nonneg.mpr ((ge_test (outside_mem s hist y k)).mp (sub_nonneg.mp h))
  · change (⟨s,raw⟩ : Expert N).utility hist y j ≤ 0 at h
    change (⟨s,truth⟩ : Expert N).utility hist y j ≤ 0
    rw [Skeleton.outsideTest_difference] at h ⊢
    exact sub_nonpos.mpr ((le_test (outside_mem s hist y j)).mp (sub_nonpos.mp h))
  · have diff := sub_nonpos.mpr h
    change (⟨s,raw⟩ : Expert N).utility hist y j - (⟨s,raw⟩ : Expert N).utility hist y k ≤ 0 at diff
    change (⟨s,truth⟩ : Expert N).utility hist y j ≤ (⟨s,truth⟩ : Expert N).utility hist y k
    apply sub_nonpos.mp
    rw [Skeleton.pairTest_difference] at diff ⊢
    exact sub_nonpos.mpr ((le_test (pair_mem s hist y j k)).mp (sub_nonpos.mp diff))

private theorem sum_over_embedding {V G : Type*} [Fintype V] [Fintype G]
    (v : V ↪ G) (f : G → ℚ) (hz : ∀ i, (∀ j, v j ≠ i) → f i = 0) :
    ∑ j, f (v j) = ∑ i, f i := by
  classical
  rw [← sum_map]
  apply sum_subset (subset_univ _)
  intro i _ hi
  apply hz i
  intro j hj
  exact hi (mem_map.mpr ⟨j, mem_univ _, hj⟩)

variable {V : Type*} [Fintype V] {N ne l : ℕ} {experts : Fin ne → Expert N}
  {hist : History N} {L : Weights ne}

private def marketSlot (M : MarketAnswer experts l hist L) (row : Fin ne)
    (g : Fin 64 → Vertex N l) (o : Option (Fin 64)) : ℚ :=
  Market.score (fun e => (experts e).skeleton.positive) (fun e i => (experts e).intercept hist i)
    M.prices row (o.map g)

private theorem fraction_zero_off_tuple (M : MarketAnswer experts l hist L) (row : Fin ne)
    (g : Fin 64 → Vertex N l)
    (only : ∀ i, (experts row).accepts l i = true ↔ ∃ j, g j = i)
    {i : Vertex N l} (off : ∀ j, g j ≠ i) : M.fractions row (some i) = 0 := by
  apply le_antisymm _ (M.balanced.nonneg _ _)
  by_contra! hpos
  obtain ⟨j,hj⟩ := (only i).mp (M.balanced.allowed _ _ hpos)
  exact off j hj

/-- Transfer an actual market answer to the sampled tuple experts. The column embedding
restricts the market to the active coordinates. Fractions outside the embedding vanish
because an expert accepts only the goods in its tuple. -/
def marketProbeAllocation (M : MarketAnswer experts l hist L) (v : V ↪ Vertex N l)
    (select : (Fin 64 → V) → Fin ne) (surplus : V → ℚ)
    (accepts : ∀ x i, (experts (select x)).accepts l i = true ↔ ∃ j, v (x j) = i)
    (preserves : ∀ x a b,
      marketSlot M (select x) (fun j => v (x j)) a ≤ marketSlot M (select x) (fun j => v (x j)) b →
      slotValue (fun j => surplus (x j)) a ≤ slotValue (fun j => surplus (x j)) b) :
    ProbeAllocation 64 surplus := by
  let chosen (x : Fin 64 → V) (j : Fin 64) := v (x j)
  have eligible (x : Fin 64 → V) (o : Option (Fin 64)) :
      Market.eligible (fun e i => (experts e).accepts l i = true) (select x) (o.map (chosen x)) := by
    cases o with
    | none => exact True.intro
    | some j => exact (accepts x _).mpr ⟨j,rfl⟩
  have max (x : Fin 64 → V) {a : Option (Fin 64)}
      (hp : 0 < M.fractions (select x) (a.map (chosen x))) (b : Option (Fin 64)) :
      slotValue (fun j => surplus (x j)) b ≤ slotValue (fun j => surplus (x j)) a :=
    preserves x b a (M.balanced.maximizes _ _ hp _ (eligible x a) (eligible x b))
  have supported (x : Fin 64 → V) (i : V) (hp : 0 < M.fractions (select x) (some (v i))) :
      ∃ j, x j = i := by
    obtain ⟨j,hj⟩ := (accepts x _).mp (M.balanced.allowed _ _ hp)
    exact ⟨j,v.injective hj⟩
  refine { weight := fun x i => M.fractions (select x) (some (v i))
           outside := fun x => M.fractions (select x) none
           nonneg := fun x i => M.balanced.nonneg _ _
           outside_nonneg := fun x => M.balanced.nonneg _ _
           total := ?_
           supported := supported
           outside_max := fun x hp j => max x (a := none) hp (some j)
           inside_max := ?_
           beats_outside := ?_ }
  · intro x
    have hr := sum_over_embedding v (fun i => M.fractions (select x) (some i)) (fun i h =>
      fraction_zero_off_tuple M (select x) _ (accepts x) (fun j => h (x j)))
    rw [hr]
    simpa [Fintype.sum_option, add_comm] using M.balanced.unit (select x)
  · intro x i hp j
    obtain ⟨k,rfl⟩ := supported x i hp
    exact max x (a := some k) hp (some j)
  · intro x i hp
    obtain ⟨k,rfl⟩ := supported x i hp
    exact max x (a := some k) hp none

/-- Local skeleton of one sampled tuple, with fixed sign and pivot. -/
def tupleSkeleton {N : ℕ} (k : Fin (depth N)) (h : Bool)
    (g : Fin 64 → Vertex N k) (pivot : Pivot N k) : Skeleton N :=
  ⟨k,h,g,pivot⟩

/-- The common shift of all sampled local experts when their raw values are replaced
by the hidden values. -/
def historyShift {N l : ℕ} (h : Bool) (pivot : Pivot N l) (truth : Fin N → ℚ)
    (hist : History N) : ℚ :=
  match pivot with
  | none => 0
  | some ⟨j,i⟩ => truth (rootVertex N j i) - States.signed h (hist j i)

private theorem selected_accepts {N : ℕ} (k : Fin (depth N)) (h : Bool)
    (g : Fin 64 → Vertex N k) (pivot : Pivot N k) (e : Expert N)
    (hes : e.skeleton = tupleSkeleton k h g pivot) (i : Vertex N k) :
    e.accepts k i = true ↔ ∃ j, g j = i := by
  obtain ⟨s, raw⟩ := e
  change s = _ at hes
  subst s
  simp [Expert.accepts, tupleSkeleton]
  change decide (∃ j, g j = i) = true ↔ ∃ j, g j = i
  exact decide_eq_true_iff

private theorem selected_slot {N ne : ℕ} {experts : Fin ne → Expert N} {hist : History N}
    {L : Weights ne} {k : Fin (depth N)} (M : MarketAnswer experts k hist L)
    (e : Fin ne) (h : Bool) (g : Fin 64 → Vertex N k) (pivot : Pivot N k)
    (hes : (experts e).skeleton = tupleSkeleton k h g pivot) (o : Option (Fin 64)) :
    marketSlot M e g o =
      slotValue ((⟨tupleSkeleton k h g pivot, (experts e).raw⟩ : Expert N).utility hist M.prices) o := by
  cases o with
  | none => rfl
  | some j =>
    simp only [marketSlot, Option.map_some, Market.score, Market.side, slotValue, Expert.utility,
      Expert.intercept, hes, tupleSkeleton, Skeleton.signed]
    cases h <;> simp

private theorem hidden_slot {N : ℕ} (k : Fin (depth N)) (h : Bool)
    (g : Fin 64 → Vertex N k) (pivot : Pivot N k) (truth : Fin N → ℚ)
    (hist : History N) (y : Vertex N k → ℚ) (o : Option (Fin 64)) :
    slotValue ((⟨tupleSkeleton k h g pivot, truth⟩ : Expert N).utility hist y) o =
      slotValue (fun j => probeSurplus (fun i => truth (rootVertex N k i)) y h
        (historyShift h pivot truth hist) (g j)) o := by
  cases o with
  | none => rfl
  | some j =>
    cases pivot <;> rfl

/-- The `ProbeAllocation` drawn from the actual selected rows. Its only learning
premise is equality of observed three-way feature comparisons against the hidden
values; all maximizing and exclusion properties follow from the market. -/
def selectedMarketAllocation {N ne : ℕ} {experts : Fin ne → Expert N} {hist : History N}
    {L : Weights ne} {k : Fin (depth N)} (M : MarketAnswer experts k hist L)
    (v : V ↪ Vertex N k) (select : (Fin 64 → V) → Fin ne)
    (h : Bool) (pivot : Pivot N k) (truth : Fin N → ℚ)
    (hsk : ∀ x, (experts (select x)).skeleton = tupleSkeleton k h (fun j => v (x j)) pivot)
    (keeps : ∀ x, ∀ t ∈ (tupleSkeleton k h (fun j => v (x j)) pivot).testsAt ⟨k,M.prices,hist⟩,
        compare (featureValue (experts (select x)).raw t.feature) t.threshold =
        compare (featureValue truth t.feature) t.threshold) :
    ProbeAllocation 64 (fun i => probeSurplus (fun i => truth (rootVertex N k i)) M.prices h
      (historyShift h pivot truth hist) (v i)) :=
  marketProbeAllocation M v select _ (fun x => selected_accepts k h _ pivot _ (hsk x))
    (fun x a b hr => by
      rw [selected_slot M _ h _ pivot (hsk x) a, selected_slot M _ h _ pivot (hsk x) b] at hr
      have htr := preserves_option_rankings (tupleSkeleton k h (fun j => v (x j)) pivot)
        _ truth hist M.prices (keeps x) a b hr
      rwa [hidden_slot, hidden_slot] at htr)

/-- The expert sign multiplied by the recorded feedback sign is the signed label
used in the finite-tuple charging calculation. -/
theorem signed_labelAgreement (h lab : Bool) :
    labelSign h * labelSign lab = labelAgreement h lab := by
  cases h <;> cases lab <;> norm_num [labelSign, labelAgreement]

/-- The selected local row has exactly its trial gain, including the sign and the
discarded outside option. No renormalization is performed when the active subtype
is used for sampling. -/
theorem selectedMarket_gain {N ne : ℕ} {experts : Fin ne → Expert N} {hist : History N}
    {L : Weights ne} {k : Fin (depth N)} (M : MarketAnswer experts k hist L)
    (v : V ↪ Vertex N k) (select : (Fin 64 → V) → Fin ne)
    (h : Bool) (pivot : Pivot N k) (truth : Fin N → ℚ)
    (hsk : ∀ x, (experts (select x)).skeleton = tupleSkeleton k h (fun j => v (x j)) pivot)
    (keeps : ∀ x, ∀ t ∈ (tupleSkeleton k h (fun j => v (x j)) pivot).testsAt ⟨k,M.prices,hist⟩,
        compare (featureValue (experts (select x)).raw t.feature) t.threshold =
        compare (featureValue truth t.feature) t.threshold)
    (labels : Vertex N k → Bool) (x : Fin 64 → V) :
    probeGain (selectedMarketAllocation M v select h pivot truth hsk keeps)
      (fun i => labelAgreement h (labels (v i))) x =
      Moment.gainQ (fun e i => M.fractions e (some i)) (sides experts)
        (fun i => labelSign (labels i)) (select x) := by
  have hs : sides experts (select x) = labelSign h := by
    simp only [sides, Market.side, hsk, tupleSkeleton, labelSign]
  change ∑ i, M.fractions (select x) (some (v i)) * labelAgreement h (labels (v i)) = _
  simp only [Moment.gainQ, hs, mul_assoc, signed_labelAgreement]
  apply sum_over_embedding v (fun i => M.fractions (select x) (some i) * labelAgreement h (labels i))
  intro i hoff
  rw [fraction_zero_off_tuple M (select x) _ (selected_accepts k h _ pivot _ (hsk x))
    (fun j => hoff (x j)), zero_mul]

/-- A probe test charged against the actual market-row gain for each selected tuple,
rather than an unrelated maximizing allocation. Only legal tie replies and recorded
feature comparison preservation are required in addition to the input market. -/
theorem selected_market_probe_test {N ne : ℕ} {experts : Fin ne → Expert N} {hist : History N}
    {L : Weights ne} {k : Fin (depth N)} (M : MarketAnswer experts k hist L)
    (v : V ↪ Vertex N k) (select : (Fin 64 → V) → Fin ne) (m : V → ℚ)
    (h : Bool) (pivot : Pivot N k) (truth : Fin N → ℚ)
    (hsk : ∀ x, (experts (select x)).skeleton = tupleSkeleton k h (fun j => v (x j)) pivot)
    (keeps : ∀ x, ∀ t ∈ (tupleSkeleton k h (fun j => v (x j)) pivot).testsAt ⟨k,M.prices,hist⟩,
        compare (featureValue (experts (select x)).raw t.feature) t.threshold =
        compare (featureValue truth t.feature) t.threshold)
    (S : Vertex N k → Prop) (live : ∀ j, S (v j))
    (x : Vertex N k × Bool → ℚ) (answer : Vertex N k → Bool)
    (valid : ∀ i, M.prices i = States.parentPrices M.prices x i →
      States.Extreme S (fun j => truth (rootVertex N k j)) (States.parentPrices M.prices x)
        h (historyShift h pivot truth hist) i → answer i = h)
    (hm : ∀ j, 0 ≤ m j) (hM0 : 0 < ∑ j, m j) (hM1 : ∑ j, m j ≤ 1) :
    let P := fun i => truth (rootVertex N k i)
    let t := historyShift h pivot truth hist
    let label := probeFeedback M.prices x answer
    Nonempty (ProbeTest m (fun j => probeSurplus P M.prices h t (v j))
      (actualSuccess v S P M.prices h t x)
      (weighted (tupleDistribution m) (fun tuple =>
        Moment.gainQ (fun e i => M.fractions e (some i)) (sides experts)
          (fun i => labelSign (label i)) (select tuple)))) := by
  classical
  dsimp only
  let A := selectedMarketAllocation M v select h pivot truth hsk keeps
  have test := actual_probe_test v live m (fun i => truth (rootVertex N k i)) M.prices h
    (historyShift h pivot truth hist) x answer valid A hm hM0 hM1
  have gain : probeGain A (fun j => labelAgreement h (probeFeedback M.prices x answer (v j))) =
      fun tuple => Moment.gainQ (fun e i => M.fractions e (some i)) (sides experts)
        (fun i => labelSign (probeFeedback M.prices x answer i)) (select tuple) :=
    funext fun tuple => selectedMarket_gain M v select h pivot truth hsk keeps _ tuple
  rwa [gain] at test

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
