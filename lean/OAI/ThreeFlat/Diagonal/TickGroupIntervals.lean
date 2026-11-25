import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

namespace OAI
/-! # Packed external-pair intervals in a group scan -/

namespace ThreeFlat.Diagonal.TickGroupIntervals

structure Interval where
  group : ℕ
  first : ℕ
  stop : ℕ
  packed : ℕ
  deriving DecidableEq, Repr

def Interval.inside (e : Interval) (x : ℕ) : Prop := e.first ≤ x ∧ x < e.stop

def Interval.covered (g lo hi : ℕ) (e : Interval) : ℕ :=
  if e.group = g then min e.stop hi - max e.first lo else 0

def Interval.words (g lo hi : ℕ) (e : Interval) : Finset ℕ :=
  if e.group = g then Finset.Ico (max e.first lo) (min e.stop hi) else ∅

@[simp] theorem Interval.mem_words (g lo hi : ℕ) (e : Interval) (x : ℕ) :
    x ∈ e.words g lo hi ↔ e.group = g ∧ e.inside x ∧ lo ≤ x ∧ x < hi := by
  by_cases h : e.group = g <;> simp [Interval.words,h,Interval.inside]; tauto

theorem Interval.covered_card (g lo hi : ℕ) (e : Interval) :
    e.covered g lo hi = (e.words g lo hi).card := by
  by_cases h : e.group = g <;> simp [Interval.covered,Interval.words,h]

/-- Located chunks can be processed in original bucket order. -/
def activeWords (g lo hi : ℕ) : List Interval → Finset ℕ
  | [] => ∅
  | e :: es => e.words g lo hi ∪ activeWords g lo hi es

@[simp] theorem mem_activeWords (g lo hi x : ℕ) (es : List Interval) :
    x ∈ activeWords g lo hi es ↔ ∃ e ∈ es, x ∈ e.words g lo hi := by
  induction es with
  | nil => simp [activeWords]
  | cons e es ih => simp [activeWords,ih]

/-- Disjointness only within each group suffices for the native write count. -/
def Compatible (e f : Interval) : Prop :=
  e.group = f.group → ∀ x, e.inside x → f.inside x → False

theorem covered_eq_active_card (g lo hi : ℕ) (es : List Interval) (disj : es.Pairwise Compatible) :
    (es.map (Interval.covered g lo hi)).sum = (activeWords g lo hi es).card := by
  induction es with
  | nil => simp [activeWords]
  | cons e es ih =>
    have rel := List.pairwise_cons.mp disj
    have sep : Disjoint (e.words g lo hi) (activeWords g lo hi es) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨group, inside, _⟩ := (Interval.mem_words ..).mp hx
      obtain ⟨f,hf,hw⟩ := (mem_activeWords ..).mp hx'
      obtain ⟨group',inside',_⟩ := (Interval.mem_words ..).mp hw
      exact rel.1 f hf (group.trans group'.symm) x inside inside'
    simp only [List.map_cons, List.sum_cons, activeWords, Finset.card_union_of_disjoint sep,
      ih rel.2,Interval.covered_card]

theorem covered_le (g lo hi : ℕ) (es : List Interval) (disj : es.Pairwise Compatible) :
    (es.map (Interval.covered g lo hi)).sum ≤ hi-lo := by
  rw [covered_eq_active_card _ _ _ _ disj, ← Nat.card_Ico lo hi]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨e,_,he⟩ := (mem_activeWords ..).mp hx
  exact Finset.mem_Ico.mpr ((Interval.mem_words ..).mp he).2.2

/-- A zero map entry preserves an unowned bit. A selected range writes one
plus the local pair position, allowing packed offset zero. -/
def Interval.code (g x : ℕ) (e : Interval) : ℕ :=
  if e.group = g ∧ e.first ≤ x ∧ x < e.stop then 1+e.packed+(x-e.first) else 0

def pairCode (g x : ℕ) : List Interval → ℕ
  | [] => 0
  | e :: es => if e.code g x = 0 then pairCode g x es else e.code g x

theorem pairCode_eq_zero (g x : ℕ) (es : List Interval) :
    pairCode g x es = 0 ↔ ∀ e ∈ es, e.group = g → ¬ e.inside x := by
  induction es with
  | nil => simp [pairCode]
  | cons e es ih =>
    by_cases h : e.group = g ∧ e.first ≤ x ∧ x < e.stop
    · simp [pairCode,Interval.code,h,Interval.inside]
    · have miss : e.group = g → e.first ≤ x → e.stop ≤ x := by
        intro ge le
        exact Nat.le_of_not_gt (fun lt => h ⟨ge,le,lt⟩)
      simp [pairCode,Interval.code,h,ih,Interval.inside]
      exact fun _ => miss

theorem pairCode_owned (g x : ℕ) {es : List Interval} (disj : es.Pairwise Compatible)
    {e : Interval} (he : e ∈ es) (hg : e.group = g) (hx : e.inside x) :
    pairCode g x es = 1+e.packed+(x-e.first) := by
  induction es with
  | nil => simp at he
  | cons q es ih =>
    obtain rfl | he := List.mem_cons.mp he
    · simp [pairCode,Interval.code,hg,hx.1,hx.2]
    · have hq : ¬(q.group = g ∧ q.first ≤ x ∧ x < q.stop) := by
        rintro ⟨hq,hxq⟩
        exact (List.pairwise_cons.mp disj).1 e he (hq.trans hg.symm) x hxq hx
      simp only [pairCode,Interval.code,ite_eq_right hq,ite_true]
      exact ih (List.pairwise_cons.mp disj).2 he

end ThreeFlat.Diagonal.TickGroupIntervals

end OAI
