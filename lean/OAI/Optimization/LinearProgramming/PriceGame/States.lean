import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

/-! Prices on duplicated coordinates and the designated-label reduction in Section 4. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace States

universe u

/-- The hidden sign is encoded as `true` for `+1` and `false` for `-1`. -/
def signed (h : Bool) (x : ℚ) : ℚ := if h then x else -x

/-- Median of three values, including repeated entries. -/
def median₃ (a b c : ℚ) : ℚ := max (min a b) (min (max a b) c)

/-- A copy in the opposite direction is always active. A copy in the hidden
sign direction is active exactly when the baseline misses the new threshold. -/
def childActive {I : Type*} (S : I → Prop) (P y : I → ℚ) (h : Bool) (t' : ℚ)
    (q : I × Bool) : Prop :=
  S q.1 ∧ (q.2 = !h ∨ signed h (y q.1) < P q.1 - t')

def parentPrices {I : Type*} (y : I → ℚ) (x : I × Bool → ℚ) (i : I) : ℚ :=
  median₃ (y i) (x (i, false)) (x (i, true))

/-- A designated coordinate is active and maximizes nonnegative surplus. -/
def Extreme {I : Type*} (S : I → Prop) (P x : I → ℚ) (h : Bool) (t : ℚ) (i : I) : Prop :=
  S i ∧ 0 ≤ P i - t - signed h (x i) ∧
    ∀ j, S j → P j - t - signed h (x j) ≤ P i - t - signed h (x i)

def Succeeds {I : Type*} (S : I → Prop) (P x : I → ℚ) (h : Bool) (t : ℚ) : Prop :=
  ∀ i, S i → P i - t ≤ signed h (x i)

/-- A lower bound on the always-active copy and a conditional lower bound on
its sibling imply the corresponding lower bound on the signed median. -/
private theorem median_bound (h : Bool) (y a b T U : ℚ) (hU : 0 ≤ U)
    (ha : T - signed h (if h then a else b) ≤ U)
    (hb : signed h y < T → T - signed h (if h then b else a) ≤ U) :
    T - signed h (median₃ y a b) ≤ U := by
  by_cases hy : signed h y < T
  · specialize hb hy
    cases h <;> simp only [signed, Bool.false_eq_true, ite_false, ite_true] at * <;>
      simp only [median₃, max_def, min_def] <;> split_ifs <;> linarith
  · cases h <;> simp only [signed, Bool.false_eq_true, ite_false, ite_true] at * <;>
      simp only [median₃, max_def, min_def] <;> split_ifs <;> linarith

/-- The median transfer inequality in upper-bound form, also covering zero surplus. -/
theorem median_surplus_le {I : Type*} {S : I → Prop} {P y : I → ℚ} {h : Bool}
    {t' U : ℚ} (x : I × Bool → ℚ) {i : I} (hi : S i) (hU : 0 ≤ U)
    (hcopy : ∀ s, childActive S P y h t' (i, s) → P i - t' - signed h (x (i, s)) ≤ U) :
    P i - t' - signed h (parentPrices y x i) ≤ U := by
  apply median_bound h (y i) (x (i, false)) (x (i, true)) (P i - t') U hU
  · cases h <;> exact hcopy _ ⟨hi, Or.inl rfl⟩
  · intro hy
    cases h <;> exact hcopy _ ⟨hi, Or.inr hy⟩

/-- Pass child prices to the parent, replacing the designated coordinate's
median with the designated copy's actual price. -/
def override {I : Type*} [DecidableEq I] (y : I → ℚ) (x : I × Bool → ℚ)
    (q : I × Bool) (j : I) : ℚ :=
  if j = q.1 then x q else parentPrices y x j

/-- One upward step preserves designation, including ties and a changing shift. -/
theorem extreme_override {I : Type*} [DecidableEq I] {S : I → Prop} {P y : I → ℚ}
    {h : Bool} {t t' : ℚ} (hshift : t ≤ t') {x : I × Bool → ℚ} {q : I × Bool}
    (hq : Extreme (childActive S P y h t') (fun z => P z.1) x h t' q) :
    Extreme S P (override y x q) h t q.1 := by
  obtain ⟨hact, hpos, hmax⟩ := hq
  refine ⟨hact.1, ?_, ?_⟩
  · simp [override]
    linarith
  · intro j hj
    by_cases heq : j = q.1
    · rw [heq]
    · simp [override, heq]
      have hmed := median_surplus_le x hj hpos (fun s hs => hmax (j, s) hs)
      linarith

/-- Child success transfers its new threshold to every active parent coordinate. -/
theorem succeeds_parent {I : Type*} {S : I → Prop} {P y : I → ℚ} {h : Bool}
    {t' : ℚ} {x : I × Bool → ℚ}
    (hchild : Succeeds (childActive S P y h t') (fun z => P z.1) x h t') :
    Succeeds S P (parentPrices y x) h t' := by
  intro i hi
  have hmed := median_surplus_le x hi (le_refl (0 : ℚ)) (fun s hs => by
    have hc := hchild (i, s) hs
    dsimp only at hc
    linarith)
  linarith

/-- Parent feedback reads the oracle answer only at a tie. -/
def feedback (y d : ℚ) (answer : Bool) : Bool :=
  if y < d then true else if d < y then false else answer

/-- Both assertions of the feedback implication. -/
theorem succeeds_feedback {I : Type*} {S : I → Prop} {P y : I → ℚ} {h : Bool}
    {t t' : ℚ} (hshift : t ≤ t') {x : I × Bool → ℚ}
    (hchild : Succeeds (childActive S P y h t') (fun z => P z.1) x h t')
    (answer : I → Bool)
    (hanswer : ∀ i, Extreme S P (parentPrices y x) h t i → answer i = h) :
    Succeeds S P (parentPrices y x) h t' ∧
    ∀ i, S i → signed h (y i) ≤ P i - t' →
      feedback (y i) (parentPrices y x i) (answer i) = h := by
  have hs := succeeds_parent hchild
  refine ⟨hs, ?_⟩
  intro i hi hbase
  have hd := hs i hi
  by_cases heq : parentPrices y x i = y i
  · have hext : Extreme S P (parentPrices y x) h t i := by
      refine ⟨hi, ?_, ?_⟩
      · rw [heq]; linarith
      · intro j hj
        have hj' := hs j hj
        rw [heq]; linarith
    simpa [feedback, heq] using hanswer i hext
  · have hstrict : signed h (y i) ≤ signed h (parentPrices y x i) := hbase.trans hd
    cases h <;> simp only [signed, Bool.false_eq_true, ite_false, ite_true] at hstrict
    · have hlt : parentPrices y x i < y i := lt_of_le_of_ne (neg_le_neg_iff.mp hstrict) heq
      simp [feedback, hlt, not_lt_of_gt hlt]
    · have hlt : y i < parentPrices y x i := lt_of_le_of_ne hstrict (Ne.symm heq)
      simp [feedback, hlt]

/-- A path to a node records only the public baselines from its ancestors. A path
ending at type `J` has one price and one possible designation for each `j : J`. -/
inductive Path (I : Type u) : Type u → Type (u + 1) where
  | root : Path I I
  | extend {J : Type u} (parent : Path I J) (y : J → ℚ) (dec : DecidableEq J) : Path I (J × Bool)

/-- Compute the single root query by successively overriding ancestor prices.
Its computation takes no oracle and has no access to the hidden state. -/
def Path.rootQuery {I : Type u} : {J : Type u} → Path I J → (J → ℚ) → J → ((I → ℚ) × I)
  | _, .root, x, i => (x, i)
  | _, .extend parent y dec, x, q => parent.rootQuery (@override _ dec y x q) q.1

/-- The invariants needed to transfer designation. Monotone changes of shift
include every allowed pivot choice, and the proof applies without a mass bound. -/
inductive Reachable {I : Type u} (h : Bool) (P : I → ℚ) (S : I → Prop) :
    {J : Type u} → Path I J → (J → ℚ) → (J → Prop) → ℚ → Prop where
  | root : Reachable h P S .root P S 0
  | extend {J : Type u} [DecidableEq J] {parent : Path I J}
      {value : J → ℚ} {active : J → Prop} {t t' : ℚ}
      (previous : Reachable h P S parent value active t) (y : J → ℚ) (hshift : t ≤ t') :
      Reachable h P S (.extend parent y inferInstance) (fun q => value q.1)
        (childActive active value y h t') t'

/-- Lemma 4.1. An active child maximizer of nonnegative surplus is sent to
a root maximizer by a query independent of the state witnessing extremality. -/
theorem rootQuery_extreme {I J : Type u} {h : Bool} {P : I → ℚ} {S : I → Prop}
    {path : Path I J} {value : J → ℚ} {active : J → Prop} {t : ℚ}
    (reachable : Reachable h P S path value active t) :
    ∀ (x : J → ℚ) (i : J), Extreme active value x h t i →
      Extreme S P (path.rootQuery x i).1 h 0 (path.rootQuery x i).2 := by
  induction reachable with
  | root => exact fun _ _ hext => hext
  | extend previous y hshift ih =>
    exact fun x i hext => ih _ _ (extreme_override hshift hext)

/-- An answer to the single computed root query therefore supplies the designated
label, even when the rest of the current oracle transcript is adversarial. -/
theorem one_designated_label {I J : Type u} {h : Bool} {P : I → ℚ} {S : I → Prop}
    {path : Path I J} {value : J → ℚ} {active : J → Prop} {t : ℚ}
    (reachable : Reachable h P S path value active t) (x : J → ℚ) (i : J) (answer : Bool)
    (root_rule : Extreme S P (path.rootQuery x i).1 h 0 (path.rootQuery x i).2 → answer = h)
    (hext : Extreme active value x h t i) : answer = h :=
  root_rule (rootQuery_extreme reachable x i hext)

end States
end PriceGame
end LinearProgramming
end Optimization
end OAI
