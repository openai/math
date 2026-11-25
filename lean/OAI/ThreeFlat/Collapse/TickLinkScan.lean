import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

namespace OAI
/-! # Chronological predecessor links in the raw tick network

A source initially has one live root trunk. Each socket consumes its source's
current trunk and creates the next one. At the end the remaining live trunk
at every source is consumed by its tail site. -/

namespace ThreeFlat.Collapse.TickLinkScan

variable (S : ℕ) (source : ℕ → ℕ)

/-- The live trunk immediately after scanning the first `i` sockets. -/
def last : ℕ → ℕ → ℕ
  | 0, s => s
  | i+1, s => if source i = s then S+i else last i s

@[simp] theorem last_zero (s : ℕ) : last S source 0 s = s := rfl
theorem last_succ (i s : ℕ) :
    last S source (i+1) s = if source i = s then S+i else last S source i s := rfl

def prev (i : ℕ) := last S source i (source i)

def middleSite (c S i : ℕ) := c+S+i
def tailSite (c S K s : ℕ) := c+S+K+s

theorem last_lt {s : ℕ} (hs : s < S) (i : ℕ) : last S source i s < S+i := by
  induction i with
  | zero => simpa using hs
  | succ i ih => rw [last_succ]; split <;> omega

theorem prev_lt {i : ℕ} (hi : source i < S) : prev S source i < S+i :=
  last_lt S source hi i

/-- Distinct sources always retain distinct live trunks, including unused sources. -/
theorem last_injective (i : ℕ) {s t : ℕ} (hs : s < S) (ht : t < S) :
    last S source i s = last S source i t → s = t := by
  induction i with
  | zero => exact id
  | succ i ih =>
    have a := last_lt S source hs i
    have b := last_lt S source ht i
    intro eqn
    simp only [last_succ] at eqn
    split_ifs at eqn with x y <;> first | exact ih eqn | omega

/-- A consumed predecessor never returns to a live slot. -/
theorem prev_ne_last {i j s : ℕ} (hi : source i < S) (hs : s < S) (ij : i < j) :
    prev S source i ≠ last S source j s := by
  induction j with
  | zero => omega
  | succ j ih =>
    have bound := prev_lt S source hi
    rw [last_succ]
    split
    · omega
    · rename_i different
      by_cases h : i = j
      · subst j
        exact fun eqn => different (last_injective S source i hi hs eqn)
      · exact ih (by omega)

theorem prev_ne_prev {i j : ℕ} (hi : source i < S) (hj : source j < S) (ij : i < j) :
    prev S source i ≠ prev S source j := prev_ne_last S source hi hj ij

/-- The socket writes `dst[prev[i]] = middleSite c S i`. -/
def middleDest (c : ℕ) (initial : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => initial
  | i+1 => Function.update (middleDest c initial i) (prev S source i) (middleSite c S i)

/-- The tail pass fills one more distinct destination per source. -/
def tailDest (c K : ℕ) (initial : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => initial
  | s+1 => Function.update (tailDest c K initial s) (last S source K s) (tailSite c S K s)

def dest (c K : ℕ) (initial : ℕ → ℕ) :=
  tailDest S source c K (middleDest S source c initial K) S

theorem middleDest_at {c K i : ℕ} (initial : ℕ → ℕ) (bound : ∀ j < K, source j < S)
    (hi : i < K) : middleDest S source c initial K (prev S source i) = middleSite c S i := by
  induction K with
  | zero => omega
  | succ k ih =>
    by_cases eqn : i = k
    · subst k; simp [middleDest]
    · have lt : i < k := by omega
      rw [middleDest, Function.update_of_ne (prev_ne_prev S source (bound _ hi) (bound k (by omega)) lt)]
      exact ih (fun j hj => bound j (by omega)) lt

theorem tailDest_at {c K s n : ℕ} (initial : ℕ → ℕ) (hn : n ≤ S) (hs : s < n) :
    tailDest S source c K initial n (last S source K s) = tailSite c S K s := by
  induction n with
  | zero => omega
  | succ t ih =>
    by_cases eqn : s = t
    · subst t; simp [tailDest]
    · have lt : s < t := by omega
      have ne : last S source K s ≠ last S source K t := fun h =>
        eqn (last_injective S source K (by omega) (by omega) h)
      rw [tailDest, Function.update_of_ne ne]
      exact ih (by omega) lt

theorem tailDest_prev {c K i n : ℕ} (initial : ℕ → ℕ) (hi : i < K)
    (bound : source i < S) (hn : n ≤ S) :
    tailDest S source c K initial n (prev S source i) = initial (prev S source i) := by
  induction n with
  | zero => rfl
  | succ t ih =>
    rw [tailDest, Function.update_of_ne (prev_ne_last S source bound (by omega : t < S) hi)]
    exact ih (by omega)

theorem dest_prev {c K i : ℕ} (initial : ℕ → ℕ) (bound : ∀ j < K, source j < S) (hi : i < K) :
    dest S source c K initial (prev S source i) = middleSite c S i := by
  rw [dest, tailDest_prev S source _ hi (bound i hi) le_rfl, middleDest_at S source _ bound hi]

theorem dest_last {c K s : ℕ} (initial : ℕ → ℕ) (hs : s < S) :
    dest S source c K initial (last S source K s) = tailSite c S K s :=
  tailDest_at S source _ le_rfl hs

end ThreeFlat.Collapse.TickLinkScan

end OAI
