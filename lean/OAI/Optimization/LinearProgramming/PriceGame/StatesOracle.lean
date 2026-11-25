import OAI.Optimization.LinearProgramming.PriceGame.Model
import OAI.Optimization.LinearProgramming.PriceGame.States
import OAI.Optimization.LinearProgramming.PriceGame.StatesMass

/-! Connect the sign-independent path algorithm to the actual partial-support price
oracle, including the price encodings and the optional query used for feedback. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace States

universe u

private theorem median₃_cases (a b c : ℚ) :
    median₃ a b c = a ∨ median₃ a b c = b ∨ median₃ a b c = c := by
  simp only [median₃, max_def, min_def]
  split_ifs <;> simp_all

/-- An arbitrary price encoding invariant holds at all of a path's public baselines. -/
def Path.pricesSatisfy {I : Type u} (good : ℚ → Prop) : {J : Type u} → Path I J → Prop
  | _, .root => True
  | _, .extend parent y _ => parent.pricesSatisfy good ∧ ∀ j, good (y j)

/-- Writing the root query only selects from supplied rationals. In particular its
largest numerator and denominator lengths are bounded by the input price lengths. -/
theorem rootQuery_pricesSatisfy {I J : Type u} (good : ℚ → Prop) (p : Path I J)
    (bases : p.pricesSatisfy good) (x : J → ℚ) (hprice : ∀ j, good (x j)) (i : J) :
    ∀ j, good ((p.rootQuery x i).1 j) := by
  induction p with
  | root => exact hprice
  | extend parent y dec ih =>
    obtain ⟨hb, hy⟩ := bases
    apply ih hb (fun j => @override _ dec y x i j) _ i.1
    intro j
    unfold override
    split
    · exact hprice i
    · unfold parentPrices
      rcases median₃_cases (y j) (x (j, false)) (x (j, true)) with he | he | he
      · rw [he]; exact hy j
      · rw [he]; exact hprice _
      · rw [he]; exact hprice _

variable {N R : ℕ} {anchor : Fin N}

/-- The hidden values used for the surplus representation in the price-game proof. -/
def priority (h : Hidden N R anchor) (i : Fin N) : ℚ := (R : ℚ) + 1 - h.cost i

/-- A nonnegative surplus maximizer is an active exact minimizer for the paper's
original oracle. The oracle is free to answer arbitrarily at all other coordinates. -/
theorem forced_of_extreme (h : Hidden N R anchor) (q : Query N)
    (hq : Extreme (· ∈ h.active) (priority h) q.prices h.positive 0 q.index) :
    h.Forced q := by
  obtain ⟨hi, _, hmax⟩ := hq
  refine ⟨hi, fun j hj => ?_⟩
  have hm := hmax j hj
  change (h.cost q.index : ℕ) + signed h.positive (q.prices q.index) ≤
    (h.cost j : ℕ) + signed h.positive (q.prices j)
  simp only [priority, sub_zero] at hm
  linarith

/-- The actual single query generated from a descendant price vector. -/
def designatedQuery {J : Type} (p : Path (Fin N) J) (x : J → ℚ) (i : J) : Query N :=
  let q := p.rootQuery x i
  ⟨q.1, q.2⟩

/-- Read one designated price-oracle reply and return it immediately. -/
def readDesignated {J : Type} (p : Path (Fin N) J) (x : J → ℚ) (i : J) : Tree N :=
  .ask (designatedQuery p x i) .result

theorem readDesignated_height {J : Type} (p : Path (Fin N) J) (x : J → ℚ) (i : J) :
    (readDesignated p x i).height = 1 := rfl

theorem readDesignated_correct {J : Type} (h : Hidden N R anchor) {p : Path (Fin N) J}
    {value : J → ℚ} {active : J → Prop} {t : ℚ}
    (reached : Reachable h.positive (priority h) (· ∈ h.active) p value active t)
    (x : J → ℚ) (i : J) (hext : Extreme active value x h.positive t i) :
    Tree.Correct h (readDesignated p x i) := by
  have forced : h.Forced (designatedQuery p x i) :=
    forced_of_extreme h _ (rootQuery_extreme reached x i hext)
  intro b hrun
  cases hrun with
  | ask allowed rest =>
    cases rest
    exact allowed forced

/-- At a strict price change the feedback is local. At a tie it uses exactly
one designated root query. -/
def feedbackAt {J : Type} (p : Path (Fin N) J) (y : J → ℚ) (x : J × Bool → ℚ)
    (i : J) : Tree N :=
  let d := parentPrices y x
  if y i < d i then .result true else if d i < y i then .result false
  else readDesignated p d i

theorem feedbackAt_height {J : Type} (p : Path (Fin N) J) (y : J → ℚ)
    (x : J × Bool → ℚ) (i : J) : (feedbackAt p y x i).height ≤ 1 := by
  simp only [feedbackAt]
  split_ifs <;> simp [Tree.height, readDesignated]

theorem feedbackAt_correct {J : Type} (h : Hidden N R anchor) {p : Path (Fin N) J}
    {value y : J → ℚ} {active : J → Prop} {t t' : ℚ}
    (reached : Reachable h.positive (priority h) (· ∈ h.active) p value active t)
    (hshift : t ≤ t') (x : J × Bool → ℚ)
    (win : Succeeds (childActive active value y h.positive t') (fun q => value q.1)
      x h.positive t') (i : J) (hi : active i) (eligible : signed h.positive (y i) ≤ value i - t') :
    Tree.Correct h (feedbackAt p y x i) := by
  have hwin := succeeds_parent win
  have hdi := hwin i hi
  simp only [feedbackAt]
  split_ifs with hup hdown
  · intro b hb
    cases hb
    cases hsign : h.positive with
    | true => rfl
    | false =>
      simp [signed, hsign] at eligible hdi
      linarith
  · intro b hb
    cases hb
    cases hsign : h.positive with
    | false => rfl
    | true =>
      simp [signed, hsign] at eligible hdi
      linarith
  · have heq : parentPrices y x i = y i := le_antisymm (le_of_not_gt hup) (le_of_not_gt hdown)
    apply readDesignated_correct h reached
    refine ⟨hi, ?_, ?_⟩
    · rw [heq]; linarith
    · intro j hj
      have hj' := hwin j hj
      rw [heq]; linarith

/-- The finite mass calculation and the designation proof use the same active copies. -/
theorem mem_childActive_iff {J : Type*} [DecidableEq J] (S : Finset J) (P y : J → ℚ)
    (h : Bool) (t' : ℚ) (q : J × Bool) :
    q ∈ Mass.childActive h S (Mass.violators S (fun i => P i - signed h (y i)) t') ↔
      childActive (· ∈ S) P y h t' q := by
  obtain ⟨i, tag⟩ := q
  simp only [Mass.childActive, Mass.violators, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_filter, childActive]
  have hcmp : (t' < P i - signed h (y i)) ↔ signed h (y i) < P i - t' := by
    constructor <;> intro hh <;> linarith
  cases h <;> cases tag <;> simp [hcmp]

end States
end PriceGame
end LinearProgramming
end Optimization
end OAI
