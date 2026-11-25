import OAI.ThreeFlat.Collapse.TickLinkScan
import Mathlib.Order.Fin.Basic

namespace OAI
/-! # The live trunk just before an ordered occurrence or at the terminal -/

namespace ThreeFlat.RawTick

open Collapse.TickLinkScan

private theorem last_gap (S : ℕ) (source : ℕ → ℕ) (s a b : ℕ) (hab : a≤b)
    (gap : ∀ n, a≤n → n<b → source n≠s) : last S source b s = last S source a s := by
  induction b with
  | zero =>
    have h : a=0 := by omega
    subst a
    rfl
  | succ b ih =>
    by_cases h : a=b+1
    · rw [h]
    · have le : a≤b := by omega
      rw [last_succ,ite_eq_right (gap b le (by omega))]
      exact ih le (fun n hn ht => gap n hn (by omega))

/-- Append the number of sockets as an exclusive sentinel to the occurrences of a source. -/
def stop {k : ℕ} (K : ℕ) (f : Fin k → ℕ) : Fin (k+1) → ℕ := Fin.lastCases K f

theorem stop_strict {k K : ℕ} (f : Fin k → ℕ) (mono : StrictMono f) (valid : ∀ i, f i<K) :
    StrictMono (stop K f) := by
  intro x y lt
  induction x using Fin.lastCases with
  | last => exact False.elim ((Fin.le_last y).not_gt lt)
  | cast x =>
    induction y using Fin.lastCases with
    | last => simpa [stop] using valid x
    | cast y => simpa [stop] using mono (show x<y from lt)

/-- At the boundary before occurrence j the open trunk is either the root or the
trunk made by occurrence j-1. This includes zero uses and the final boundary. -/
theorem last_at_stop {k K S s : ℕ} (source : ℕ → ℕ) (f : Fin k → ℕ) (mono : StrictMono f)
    (valid : ∀ i, f i<K) (hits : ∀ n<K, source n=s ↔ ∃ j,f j=n) (j : Fin (k+1)) :
    last S source (stop K f j) s = Fin.cases s (fun i => S+f i) j := by
  have order := stop_strict f mono valid
  have bound (z : Fin (k+1)) : stop K f z ≤ K := by
    induction z using Fin.lastCases with
    | last => simp [stop]
    | cast z => simpa [stop] using (valid z).le
  induction j using Fin.cases with
  | zero =>
    simp only [Fin.cases_zero]
    apply (last_gap S source s 0 _ (Nat.zero_le _) ?_).trans rfl
    intro n _ hlt h
    obtain ⟨z,hz⟩ := (hits n (lt_of_lt_of_le hlt (bound 0))).mp h
    have hz' : stop K f z.castSucc=n := by simpa [stop] using hz
    have impossible := order.monotone (Fin.zero_le z.castSucc)
    omega
  | succ j =>
    simp only [Fin.cases_succ]
    have here : stop K f j.castSucc=f j := Fin.lastCases_castSucc ..
    have before : f j<stop K f j.succ := here ▸ order j.castSucc_lt_succ
    have same := last_gap S source s (f j+1) (stop K f j.succ) before (by
      intro n hn ht he
      obtain ⟨i,hi⟩ := (hits n (lt_of_lt_of_le ht (bound _))).mp he
      have hi' : stop K f i.castSucc=n := by simpa [stop] using hi
      have lo : j.castSucc < i.castSucc := order.lt_iff_lt.mp (by omega)
      have up : i.castSucc < j.succ := order.lt_iff_lt.mp (by omega)
      change j.val < i.val at lo
      change i.val < j.val+1 at up
      omega)
    rw [same,last_succ,ite_eq_left ((hits _ (valid j)).mpr ⟨j,rfl⟩)]

end ThreeFlat.RawTick

end OAI
