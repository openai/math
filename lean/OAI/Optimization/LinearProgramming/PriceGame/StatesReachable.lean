import OAI.Optimization.LinearProgramming.PriceGame.Experts
import OAI.Optimization.LinearProgramming.PriceGame.StatesFeedback
import OAI.Optimization.LinearProgramming.PriceGame.ChargingActualProbe
import OAI.Optimization.LinearProgramming.PriceGame.ChargingTransfer

/-! Possible states of the duplicated-coordinate game, with finite active sets and
actual ancestral pivot descriptors. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace States

open Finset
open Mass (Vertex weight depth)

variable {N R k : ℕ} {anchor : Fin N}

/-- The descriptor and finite active set carried by the analysis of a node. The
same publicly queried history may admit several such states. -/
structure FiniteState (N k : ℕ) where
  pivot : Pivot N k
  active : Finset (Vertex N k)

namespace FiniteState

def value (h : Hidden N R anchor) (k : ℕ) (i : Vertex N k) : ℚ :=
  priority h (rootVertex N k i)

def decode (h : Hidden N R anchor) (history : History N) : Pivot N k → ℚ
  | none => 0
  | some ⟨j, v⟩ => value h j v - signed h.positive (history j v)

def shift (s : FiniteState N k) (h : Hidden N R anchor) (history : History N) : ℚ :=
  decode h history s.pivot

def root (h : Hidden N R anchor) : FiniteState N 0 := ⟨none, h.active⟩

/-- Promote an old pivot or designate a vertex at the current depth. -/
def childPivot (p : Pivot N k) : Option (Vertex N k) → Pivot N (k+1)
  | none => p.map (fun ⟨j, v⟩ => ⟨j.castSucc, v⟩)
  | some i => some ⟨Fin.last k, i⟩

def nextShift (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (y : Vertex N k → ℚ) : Option (Vertex N k) → ℚ
  | none => s.shift h history
  | some i => value h k i - signed h.positive (y i)

def strictSet (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (y : Vertex N k → ℚ) (o : Option (Vertex N k)) : Finset (Vertex N k) :=
  Mass.violators s.active (fun i => value h k i - signed h.positive (y i))
    (s.nextShift h history y o)

def child (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (y : Vertex N k → ℚ) (o : Option (Vertex N k)) : FiniteState N (k+1) :=
  ⟨childPivot s.pivot o, Mass.childActive h.positive s.active (s.strictSet h history y o)⟩

theorem child_shift (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (y : Vertex N k → ℚ) (o : Option (Vertex N k)) :
    (s.child h history y o).shift h (history.push k y) = s.nextShift h history y o := by
  cases o with
  | some v => simp [shift, child, childPivot, nextShift, decode, History.push]
  | none =>
    simp only [shift, child, childPivot, nextShift]
    cases hp : s.pivot with
    | none => rfl
    | some a =>
      obtain ⟨j,v⟩ := a
      simp [decode, History.push, Nat.ne_of_lt j.isLt]

theorem mem_child (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (y : Vertex N k → ℚ) (o : Option (Vertex N k)) (v : Vertex N (k+1)) :
    v ∈ (s.child h history y o).active ↔
      childActive (· ∈ s.active) (value h k) y h.positive (s.nextShift h history y o) v :=
  mem_childActive_iff _ _ _ _ _ _

theorem strictSet_subset (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (y : Vertex N k → ℚ) (o : Option (Vertex N k)) :
    s.strictSet h history y o ⊆ s.active := filter_subset _ _

def totalMass (s : FiniteState N k) (h : Hidden N R anchor) : ℚ :=
  ∑ i ∈ s.active, weight N k h.positive i

def ambientMass (s : FiniteState N k) (h : Hidden N R anchor) (v : Vertex N k) : ℚ :=
  Charging.maskedMass s.active (weight N k h.positive) v

theorem child_ambientMass (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (y : Vertex N k → ℚ) (o : Option (Vertex N k)) :
    (s.child h history y o).ambientMass h =
      Charging.transitionMass h.positive s.active (s.strictSet h history y o) (weight N k h.positive) := by
  funext v
  rfl

/-- Actual successes for this finite set. -/
def wins (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (x : Vertex N k → ℚ) : Prop :=
  Succeeds (· ∈ s.active) (value h k) x h.positive (s.shift h history)

/-- The test for a child run uses the same returned prices for every proposed
descriptor. A decreasing shift is ineligible, even if those prices happen to succeed. -/
def testPass (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (y : Vertex N k → ℚ) (x : Vertex N (k+1) → ℚ) (o : Option s.active) : Prop :=
  (s.shift h history ≤ s.nextShift h history y (o.map Subtype.val)) ∧
    (s.child h history y (o.map Subtype.val)).wins h (history.push k y) x

theorem child_wins_iff (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (y : Vertex N k → ℚ) (o : Option (Vertex N k)) (x : Vertex N (k+1) → ℚ) :
    (s.child h history y o).wins h (history.push k y) x ↔
      Succeeds (childActive (· ∈ s.active) (value h k) y h.positive (s.nextShift h history y o))
        (fun v => value h k v.1) x h.positive (s.nextShift h history y o) := by
  simp only [wins, child_shift, Succeeds, mem_child]
  rfl

theorem testPass_iff_actualSuccess (s : FiniteState N k) (h : Hidden N R anchor)
    (history : History N) (y : Vertex N k → ℚ) (x : Vertex N (k+1) → ℚ) (o : Option s.active) :
    s.testPass h history y x o ↔
      Charging.actualSuccess Subtype.val (· ∈ s.active) (value h k) y h.positive (s.shift h history) x o := by
  cases o with
  | none => exact and_congr Iff.rfl (s.child_wins_iff _ _ _ _ _)
  | some i => exact and_congr Iff.rfl (s.child_wins_iff _ _ _ _ _)

def surplus (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (y : Vertex N k → ℚ) (i : Vertex N k) : ℚ :=
  value h k i - s.shift h history - signed h.positive (y i)

def priceThreshold (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (i : Vertex N k) : ℚ := signed h.positive (value h k i - s.shift h history)

theorem fails_iff_exists_miss (s : FiniteState N k) (h : Hidden N R anchor)
    (history : History N) (x : Vertex N k → ℚ) :
    ¬s.wins h history x ↔ ∃ i : s.active, Charging.misses h.positive (s.priceThreshold h history i) (x i) = true := by
  simp only [wins, Succeeds, not_forall, not_le, exists_prop]
  constructor
  · rintro ⟨i, hi, hfail⟩
    refine ⟨⟨i,hi⟩, ?_⟩
    apply (Charging.misses_iff_positive_surplus (value h k) x h.positive (s.shift h history) i).2
    unfold Charging.probeSurplus
    linarith
  · rintro ⟨i,hm⟩
    refine ⟨i.val,i.property,?_⟩
    have hp := (Charging.misses_iff_positive_surplus (value h k) x h.positive (s.shift h history) i.val).1 hm
    unfold Charging.probeSurplus at hp
    linarith

theorem positiveMass_eq_violatedMass (s : FiniteState N k) (h : Hidden N R anchor)
    (history : History N) (y : Vertex N k → ℚ) :
    Charging.positiveMass (fun i : s.active => weight N k h.positive i.val)
      (fun i => s.surplus h history y i) =
    Charging.violatedMass (fun i : s.active => weight N k h.positive i.val) h.positive
      (fun i => s.priceThreshold h history i) (fun i => y i) :=
  Charging.positiveMass_eq_violatedMass (fun i : s.active => i.val)
    (fun i : s.active => weight N k h.positive i.val) (value h k) y h.positive (s.shift h history)

theorem inherited_pass_mapped (s : FiniteState N k) (h : Hidden N R anchor)
    (history : History N) (y : Vertex N k → ℚ) (x : Vertex N (k+1) → ℚ)
    (pass : s.testPass h history y x none) (i : s.active) :
    Charging.misses h.positive (s.priceThreshold h history i) (parentPrices y x i) = false :=
  Charging.inherited_mapped_prices_do_not_miss
    ((s.testPass_iff_actualSuccess _ _ _ _ _).1 pass).2 i.property

theorem child_totalMass_le (s : FiniteState N k) (h : Hidden N R anchor) (history : History N)
    (y : Vertex N k → ℚ) (o : Option (Vertex N k)) (hs : s.totalMass h ≤ 1)
    (hu : ∑ i ∈ s.strictSet h history y o, weight N k h.positive i ≤ 1/16) :
    (s.child h history y o).totalMass h ≤ 1 :=
  Mass.child_mass_le_one _ _ _ _ hs hu

/-- Sampling uses just the active subtype; all sums are still the original unnormalised masses. -/
theorem sum_on_active (s : FiniteState N k) (h : Hidden N R anchor) :
    (∑ i : s.active, weight N k h.positive i.val) = s.totalMass h :=
  Finset.sum_coe_sort _ _

private theorem sum_strictSet (s : FiniteState N k) (h : Hidden N R anchor)
    (history : History N) (y : Vertex N k → ℚ) (o : Option (Vertex N k)) :
    (∑ i ∈ s.strictSet h history y o, weight N k h.positive i) =
      ∑ i : s.active, if s.nextShift h history y o < value h k i - signed h.positive (y i)
        then weight N k h.positive i else 0 := by
  unfold strictSet Mass.violators
  rw [Finset.sum_filter]
  exact (Finset.sum_coe_sort _ _).symm

theorem admissible_shift_and_mass (s : FiniteState N k) (h : Hidden N R anchor)
    (history : History N) (y : Vertex N k → ℚ) (o : Option s.active)
    (ha : Charging.admissibleTest (fun i : s.active => weight N k h.positive i.val)
      (fun i : s.active => s.surplus h history y i.val) o) :
    s.shift h history ≤ s.nextShift h history y (o.map Subtype.val) ∧
      (∑ i ∈ s.strictSet h history y (o.map Subtype.val), weight N k h.positive i) ≤ 1/16 := by
  cases o with
  | none =>
    refine ⟨le_rfl, ?_⟩
    rw [sum_strictSet]
    change (∑ i ∈ univ.filter (fun i : s.active => 0 < s.surplus h history y i),
      weight N k h.positive i.val) ≤ 1/16 at ha
    rw [Finset.sum_filter] at ha
    apply le_trans (le_of_eq ?_) ha
    apply Finset.sum_congr rfl
    intro i _
    have he : s.shift h history < value h k i - signed h.positive (y i) ↔
        0 < s.surplus h history y i := by unfold surplus; constructor <;> intro hlt <;> linarith
    simp only [Option.map_none, nextShift, he]
  | some j =>
    change (0 < s.surplus h history y j.val ∧
      (∑ i ∈ univ.filter (fun i : s.active => s.surplus h history y j < s.surplus h history y i),
        weight N k h.positive i.val) ≤ 1/16) at ha
    obtain ⟨hj, ha⟩ := ha
    constructor
    · change s.shift h history ≤ value h k j - signed h.positive (y j)
      unfold surplus at hj
      linarith
    · rw [sum_strictSet]
      rw [Finset.sum_filter] at ha
      apply le_trans (le_of_eq ?_) ha
      apply Finset.sum_congr rfl
      intro i _
      have he : value h k j - signed h.positive (y j) < value h k i - signed h.positive (y i) ↔
          s.surplus h history y j < s.surplus h history y i := by
        unfold surplus; constructor <;> intro hlt <;> linarith
      simp only [Option.map_some, nextShift, he]

theorem expert_shift (s : Skeleton N) (h : Hidden N R anchor) (history : History N)
    (hs : s.positive = h.positive) :
    s.shift (priority h) history = decode h history s.pivot := by
  unfold Skeleton.shift
  cases hp : s.pivot with
  | none => rfl
  | some a =>
    obtain ⟨j,v⟩ := a
    simp [decode, value, Skeleton.signed, signed, hs]

end FiniteState

/-- Paths and histories are public; a hidden state is possible precisely by a sequence
of active, nondecreasing and mass-admissible pivot choices from the root. -/
inductive Possible (h : Hidden N R anchor) :
    {k : ℕ} → History N → Path (Fin N) (Vertex N k) → FiniteState N k → Prop where
  | root (history : History N) : Possible h (k := 0) history .root (.root h)
  | child {k : ℕ} {history : History N} {path : Path (Fin N) (Vertex N k)} {s : FiniteState N k}
      (previous : Possible h history path s) (level : k < depth N) (y : Vertex N k → ℚ)
      (o : Option (Vertex N k)) (live : ∀ i, o = some i → i ∈ s.active)
      (increases : s.shift h history ≤ s.nextShift h history y o)
      (budget : (s.child h history y o).totalMass h ≤ 1) :
      Possible h (k := k+1) (history.push k y) (.extend path y (vertexDecidableEq N k)) (s.child h history y o)

namespace Possible

variable {h : Hidden N R anchor} {history : History N} {path : Path (Fin N) (Vertex N k)}
    {s : FiniteState N k}

theorem depth_le (p : Possible h history path s) : k ≤ depth N := by
  cases p with
  | root => omega
  | child _ level _ _ _ _ _ => omega

theorem mass_le (p : Possible h history path s) : s.totalMass h ≤ 1 := by
  cases p with
  | root => exact Mass.root_mass_le_one N (Nat.zero_lt_of_lt anchor.isLt) _ _
  | child _ _ _ _ _ _ budget => exact budget

theorem shift_nonneg (p : Possible h history path s) : 0 ≤ s.shift h history := by
  induction p with
  | root => exact le_rfl
  | child _ _ _ _ _ increases _ ih => rw [FiniteState.child_shift]; exact ih.trans increases

/-- The finite-state construction meets the exact premises of the one-designated-label oracle. -/
theorem toReachable (p : Possible h history path s) :
    Reachable h.positive (priority h) (· ∈ h.active) path (FiniteState.value h k)
      (· ∈ s.active) (s.shift h history) := by
  induction p with
  | root => exact .root
  | @child k history path s prev level y o live inc budget ih =>
    rw [FiniteState.child_shift]
    have ha : (fun v => v ∈ (s.child h history y o).active) =
        childActive (· ∈ s.active) (FiniteState.value h k) y h.positive (s.nextShift h history y o) :=
      funext fun v => propext (s.mem_child h history y o v)
    rw [ha]
    exact .extend ih y inc

theorem nonempty (p : Possible h history path s) : s.active.Nonempty := by
  induction p with
  | root => exact ⟨anchor, h.anchor_mem⟩
  | @child k history path s prev level y o live inc budget ih =>
    obtain ⟨i,hi⟩ := ih
    exact ⟨(i,!h.positive), (s.mem_child h history y o _).2 ⟨hi, Or.inl rfl⟩⟩

theorem active_root (p : Possible h history path s) {i : Vertex N k} (hi : i ∈ s.active) :
    rootVertex N k i ∈ h.active := by
  induction p with
  | root => exact hi
  | @child k history path s prev level y o live inc budget ih =>
    exact ih ((s.mem_child h history y o _).1 hi).1

/-- Every initially active coordinate survives at every depth along at least one copy. -/
theorem root_fiber (p : Possible h history path s) {a : Fin N} (ha : a ∈ h.active) :
    ∃ i ∈ s.active, rootVertex N k i = a := by
  induction p with
  | root => exact ⟨a,ha,rfl⟩
  | @child k history path s prev level y o live inc budget ih =>
    obtain ⟨i,hi,hai⟩ := ih
    exact ⟨(i,!h.positive), (s.mem_child h history y o _).2 ⟨hi, Or.inl rfl⟩, hai⟩

theorem image_root (p : Possible h history path s) : s.active.image (rootVertex N k) = h.active := by
  ext a
  simp only [mem_image]
  exact ⟨fun ⟨i, hi, eq⟩ => eq ▸ p.active_root hi, p.root_fiber⟩

/-- At every nonterminal node, for every public baseline, at least one legal
state reaches the child. If any threshold is above the shift, choose a maximizing
active vertex; otherwise the inherited descriptor has no expensive copies. -/
theorem exists_child (p : Possible h history path s) (level : k < depth N) (y : Vertex N k → ℚ) :
    ∃ o : Option (Vertex N k), Possible h (k := k+1)
      (history.push k y) (.extend path y (vertexDecidableEq N k)) (s.child h history y o) := by
  let threshold := fun i => FiniteState.value h k i - signed h.positive (y i)
  by_cases above : ∃ i ∈ s.active, s.shift h history < threshold i
  · obtain ⟨i, hi, hh, _, hm⟩ := Mass.maximum_pivot_admissible (weight N k h.positive)
      h.positive s.active threshold (s.shift h history) p.mass_le above
    refine ⟨some i, p.child level y (some i) ?_ hh.le hm⟩
    intro j hji
    exact Option.some.inj hji ▸ hi
  · refine ⟨none, p.child level y none (fun _ he => by cases he) le_rfl ?_⟩
    apply s.child_totalMass_le _ _ _ _ p.mass_le
    have empty : s.strictSet h history y none = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact above ⟨i,(mem_filter.mp hi).1,(mem_filter.mp hi).2⟩
    simp [empty]

theorem weight_pos (i : Vertex N k) : 0 < weight N k h.positive i := by
  rw [Mass.weight_dyadic]
  have hN : 0 < N := Nat.zero_lt_of_lt anchor.isLt
  positivity

theorem mass_pos (p : Possible h history path s) : 0 < s.totalMass h := by
  obtain ⟨i,hi⟩ := p.nonempty
  exact lt_of_lt_of_le (weight_pos i) (single_le_sum (fun j _ => Mass.weight_nonneg N k h.positive j) hi)

/-- Both the inherited test and every positive-probability pivot in the high test
give possible child states; this does not presuppose success of the child's prices. -/
theorem child_of_admissible (p : Possible h history path s) (level : k < depth N)
    (y : Vertex N k → ℚ) (o : Option s.active)
    (ha : Charging.admissibleTest (fun i : s.active => weight N k h.positive i.val)
      (fun i : s.active => s.surplus h history y i.val) o) :
    Possible h (k := k+1) (history.push k y) (.extend path y (vertexDecidableEq N k))
      (s.child h history y (o.map Subtype.val)) := by
  obtain ⟨hinc, hsmall⟩ := s.admissible_shift_and_mass h history y o ha
  apply p.child level y (o.map Subtype.val) _ hinc (s.child_totalMass_le _ _ _ _ p.mass_le hsmall)
  intro i hi
  cases o with
  | none => simp at hi
  | some j =>
    obtain rfl : j.val = i := Option.some.inj hi
    exact j.property

/-- A failed admissible test gives an actual possible child state in which the
shared returned prices fail, as needed by induction on the trial height. -/
theorem failed_child (p : Possible h history path s) (level : k < depth N)
    (y : Vertex N k → ℚ) (x : Vertex N (k+1) → ℚ) (o : Option s.active)
    (ha : Charging.admissibleTest (fun i : s.active => weight N k h.positive i.val)
      (fun i : s.active => s.surplus h history y i.val) o)
    (failed : ¬s.testPass h history y x o) :
    Possible h (k := k+1) (history.push k y) (.extend path y (vertexDecidableEq N k))
        (s.child h history y (o.map Subtype.val)) ∧
      ¬(s.child h history y (o.map Subtype.val)).wins h (history.push k y) x :=
  ⟨p.child_of_admissible level y o ha, fun win =>
    failed ⟨(s.admissible_shift_and_mass h history y o ha).1, win⟩⟩

/-- Actual single-coordinate oracle execution yields the probe test used in charging.
No auxiliary callback supplying tie labels is assumed. -/
theorem probeTest_of_feedbackAll (p : Possible h history path s)
    (y : Vertex N k → ℚ) (x : Vertex N (k+1) → ℚ) (labels : Vertex N k → Bool)
    (run : Computation.Reaches h (feedbackAll path y x) labels)
    (A : Charging.ProbeAllocation 64 (fun i : s.active => s.surplus h history y i.val)) :
    Nonempty (Charging.ProbeTest (fun i : s.active => weight N k h.positive i.val)
      (fun i : s.active => s.surplus h history y i.val) (s.testPass h history y x)
      (Charging.weighted (Charging.tupleDistribution (fun i : s.active => weight N k h.positive i.val))
        (Charging.probeGain A (fun i : s.active => if labels i.val = h.positive then 1 else -1)))) := by
  apply Charging.exists_probe_test
  · exact fun i => Mass.weight_nonneg _ _ _ _
  · rw [s.sum_on_active]; exact p.mass_pos
  · rw [s.sum_on_active]; exact p.mass_le
  · intro i
    split <;> norm_num
  · rintro ⟨hshift,win⟩ i hpos
    have w := (s.child_wins_iff h history y _ x).1 win
    have eligible : signed h.positive (y i.val) ≤ FiniteState.value h k i.val -
        s.nextShift h history y (Option.map Subtype.val (none : Option s.active)) := by
      change signed h.positive (y i.val) ≤ FiniteState.value h k i.val - s.shift h history
      unfold FiniteState.surplus at hpos
      linarith
    have correct := feedbackAll_correct h p.toReachable hshift x w labels run i.val i.property eligible
    simp [correct]
  · rintro j ⟨hshift,win⟩ i hlarge
    have w := (s.child_wins_iff h history y _ x).1 win
    have eligible : signed h.positive (y i.val) ≤ FiniteState.value h k i.val -
        s.nextShift h history y ((some j).map Subtype.val) := by
      change signed h.positive (y i.val) ≤
        FiniteState.value h k i.val - (FiniteState.value h k j.val - signed h.positive (y j.val))
      unfold FiniteState.surplus at hlarge
      linarith
    have correct := feedbackAll_correct h p.toReachable hshift x w labels run i.val i.property eligible
    simp [correct]

theorem leaf_wins {history : History N} {path : Path (Fin N) (Vertex N (depth N))}
    {s : FiniteState N (depth N)} (p : Possible h history path s) :
    s.wins h history (Mass.leafPrice N (R+1)) := by
  intro i hi
  apply Mass.leaf_succeeds N (Nat.zero_lt_of_lt anchor.isLt) _ _ _ _ _ p.mass_le _ p.shift_nonneg i hi
  intro j _
  unfold FiniteState.value priority
  have : (0:ℚ) ≤ ((h.cost (rootVertex N (depth N) j)).val : ℚ) := by positivity
  linarith

end Possible
end States
end PriceGame
end LinearProgramming
end Optimization
end OAI
