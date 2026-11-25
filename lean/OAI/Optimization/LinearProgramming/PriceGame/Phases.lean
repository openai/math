import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

/-! Greedy epochs in §7: retain the most recently selected entries until a comparison
fails, then replace all selections at the start of the next trial. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Phases

/-- The trial at which the current crop of representatives was selected. -/
def origin (miss : ℕ → ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | t+1 => if miss (origin miss t) t then t+1 else origin miss t

def exceptional (miss : ℕ → ℕ → Bool) (t : ℕ) : Bool := miss (origin miss t) t

theorem origin_le (miss : ℕ → ℕ → Bool) (t : ℕ) : origin miss t ≤ t := by
  induction t with
  | zero => rfl
  | succ t ih => change (if exceptional miss t then t+1 else origin miss t) ≤ t+1; split <;> omega

theorem origin_succ (miss : ℕ → ℕ → Bool) (t : ℕ) :
    origin miss (t+1) = if exceptional miss t then t+1 else origin miss t := rfl

theorem origin_const (miss : ℕ → ℕ → Bool) {u v : ℕ} (huv : u ≤ v)
    (good : ∀ k, u ≤ k → k < v → exceptional miss k = false) :
    origin miss v = origin miss u := by
  induction v, huv using Nat.le_induction with
  | base => rfl
  | succ v huv ih =>
    rw [origin_succ, good v huv (Nat.lt_succ_self _)]
    exact ih (fun k h₁ h₂ => good k h₁ (Nat.lt_succ_of_lt h₂))

/-- Exceptional trial times among the first T trials. -/
def events (miss : ℕ → ℕ → Bool) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter fun t => exceptional miss t = true

theorem mem_events {miss : ℕ → ℕ → Bool} {T t : ℕ} :
    t ∈ events miss T ↔ t < T ∧ exceptional miss t = true := by simp [events]

theorem events_mono (miss : ℕ → ℕ → Bool) {s t : ℕ} (hle : s ≤ t) :
    events miss s ⊆ events miss t := by
  intro x hx
  exact mem_events.mpr ⟨(mem_events.mp hx).1.trans_le hle, (mem_events.mp hx).2⟩

theorem count_mono (miss : ℕ → ℕ → Bool) :
    Monotone (fun t => (events miss t).card) := fun _ _ h => Finset.card_le_card (events_mono miss h)

theorem count_succ (miss : ℕ → ℕ → Bool) (t : ℕ) :
    (events miss (t+1)).card = (events miss t).card + if exceptional miss t then 1 else 0 := by
  cases h : exceptional miss t <;> simp [events, Finset.range_add_one, Finset.filter_insert, h]

theorem no_event_between_equal_counts (miss : ℕ → ℕ → Bool) {u v : ℕ}
    (hc : (events miss u).card = (events miss v).card) :
    ∀ k, u ≤ k → k < v → exceptional miss k = false := by
  intro k huk hkv
  cases h : exceptional miss k
  · rfl
  · have hl := count_mono miss huk
    have hr := count_mono miss (show k+1 ≤ v from hkv)
    dsimp only at hl hr
    have he := count_succ miss k
    rw [h] at he
    simp only [ite_true] at he
    omega

/-- `none` charges an exception. A good trial belongs to the interval labeled by the
number of exceptional trials strictly before it. -/
def tag (miss : ℕ → ℕ → Bool) (T E : ℕ) (bound : (events miss T).card ≤ E)
    (t : Fin T) : Option (Fin (E+1)) :=
  if exceptional miss t then none else
    some ⟨(events miss t).card, Nat.lt_succ_of_le ((count_mono miss t.isLt.le).trans bound)⟩

theorem tag_none {miss : ℕ → ℕ → Bool} {T E : ℕ} {bound : (events miss T).card ≤ E}
    (t : Fin T) : tag miss T E bound t = none ↔ exceptional miss t = true := by
  cases h : exceptional miss t <;> simp [tag, h]

theorem tag_some {miss : ℕ → ℕ → Bool} {T E : ℕ} {bound : (events miss T).card ≤ E}
    (t : Fin T) (b : Fin (E+1)) :
    tag miss T E bound t = some b ↔ exceptional miss t = false ∧ (events miss t).card = b.val := by
  cases h : exceptional miss t <;> simp [tag, h, Fin.ext_iff]

theorem exceptional_fiber {miss : ℕ → ℕ → Bool} {T E : ℕ} (bound : (events miss T).card ≤ E) :
    (Finset.univ.filter fun t : Fin T => tag miss T E bound t = none).card = (events miss T).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact mem_events.mpr ⟨i.isLt, (tag_none i).mp (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ h
    exact Fin.ext h
  · intro t ht
    obtain ⟨hlt,hx⟩ := mem_events.mp ht
    exact ⟨⟨t,hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (tag_none _).mpr hx⟩, rfl⟩

theorem good_interval {miss : ℕ → ℕ → Bool} {T E : ℕ} {bound : (events miss T).card ≤ E}
    {b : Fin (E+1)} {u v w : Fin T} (huv : u ≤ v) (hvw : v ≤ w)
    (hu : tag miss T E bound u = some b) (hw : tag miss T E bound w = some b) :
    tag miss T E bound v = some b := by
  obtain ⟨_,cu⟩ := (tag_some u b).mp hu
  obtain ⟨gw,cw⟩ := (tag_some w b).mp hw
  refine (tag_some v b).mpr ⟨?_, le_antisymm ((count_mono miss hvw).trans_eq cw)
    (cu ▸ count_mono miss huv)⟩
  rcases lt_or_eq_of_le hvw with lt | rfl
  · exact no_event_between_equal_counts miss (cu.trans cw.symm) _ huv lt
  · exact gw

theorem same_origin {miss : ℕ → ℕ → Bool} {T E : ℕ} {bound : (events miss T).card ≤ E}
    {b : Fin (E+1)} {u v : Fin T} (hu : tag miss T E bound u = some b)
    (hv : tag miss T E bound v = some b) : origin miss u = origin miss v := by
  have cu := ((tag_some u b).mp hu).2
  have cv := ((tag_some v b).mp hv).2
  rcases le_total u.val v.val with h | h
  · exact (origin_const miss h (no_event_between_equal_counts miss (cu.trans cv.symm))).symm
  · exact origin_const miss h (no_event_between_equal_counts miss (cv.trans cu.symm))

end Phases
end PriceGame
end LinearProgramming
end Optimization
end OAI
