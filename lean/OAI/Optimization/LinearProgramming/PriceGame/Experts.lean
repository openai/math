import OAI.Optimization.LinearProgramming.PriceGame.StatesMass
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! The public expert skeletons and all comparisons recorded by a trial in Sections 4 and 7. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

open States.Mass Finset

/-- The vertex coordinates have an executable equality test at every depth. -/
instance vertexDecidableEq (N : ℕ) : (k : ℕ) → DecidableEq (Vertex N k)
  | 0 => inferInstanceAs (DecidableEq (Fin N))
  | k + 1 => by
    letI := vertexDecidableEq N k
    exact inferInstanceAs (DecidableEq (Vertex N k × Bool))

def rootVertex (N : ℕ) : (k : ℕ) → Vertex N k → Fin N
  | 0, i => i
  | k + 1, (i, _) => rootVertex N k i

/-- Public baselines on the path. Only entries strictly above the current node are inspected. -/
abbrev History (N : ℕ) := (k : ℕ) → Vertex N k → ℚ

def History.push {N : ℕ} (h : History N) (k : ℕ) (x : Vertex N k → ℚ) : History N :=
  fun j => if eq : j = k then eq.symm ▸ x else h j

abbrev Pivot (N k : ℕ) := Option ((j : Fin k) × Vertex N j)

/-- Depth, sign, 64-tuple of vertices (with repetitions), and an ancestral pivot descriptor. -/
abbrev Skeleton (N : ℕ) :=
  (k : Fin (depth N)) × Bool × ((Fin 64 → Vertex N k) × Pivot N k)

namespace Skeleton

variable {N : ℕ}

abbrev level (s : Skeleton N) : ℕ := s.1
abbrev positive (s : Skeleton N) : Bool := s.2.1
abbrev tuple (s : Skeleton N) : Fin 64 → Vertex N s.level := s.2.2.1
abbrev pivot (s : Skeleton N) : Pivot N s.level := s.2.2.2

def origin (s : Skeleton N) (j : Fin 64) : Fin N := rootVertex N s.level (s.tuple j)

/-- The only original cost coordinates that can affect this expert's comparisons. -/
def sources (s : Skeleton N) : Finset (Fin N) :=
  (univ.image s.origin) ∪ s.pivot.toFinset.image (fun j => rootVertex N j.1 j.2)

theorem card_sources_le (s : Skeleton N) : s.sources.card ≤ 65 := by
  have hfirst : (univ.image s.origin).card ≤ 64 :=
    calc _ ≤ (univ : Finset (Fin 64)).card := card_image_le
         _ = 64 := by simp
  have hsecond : (s.pivot.toFinset.image (fun j => rootVertex N j.1 j.2)).card ≤ 1 := by
    apply card_image_le.trans
    cases hp : s.pivot <;> simp
  exact (card_union_le _ _).trans (by omega)

def signed (s : Skeleton N) (x : ℚ) : ℚ := if s.positive then x else -x

def shift (s : Skeleton N) (raw : Fin N → ℚ) (history : History N) : ℚ :=
  match s.pivot with
  | none => 0
  | some ⟨j, v⟩ => raw (rootVertex N j v) - s.signed (history j v)

end Skeleton

/-- Values on unused coordinates are ignored, so an expert requires at most 65 raw entries. -/
structure Expert (N : ℕ) where
  skeleton : Skeleton N
  raw : Fin N → ℚ

namespace Expert
variable {N : ℕ}

def isLocal (e : Expert N) (k : ℕ) : Bool := decide (e.skeleton.level = k)

/-- A repeated good in the tuple remains a single market option. -/
def accepts (e : Expert N) (k : ℕ) (i : Vertex N k) : Bool :=
  if h : k = e.skeleton.level then decide (∃ j : Fin 64, e.skeleton.tuple j = h ▸ i)
  else false

def intercept (e : Expert N) (history : History N) {k : ℕ} (i : Vertex N k) : ℚ :=
  e.raw (rootVertex N k i) - e.skeleton.shift e.raw history

def utility (e : Expert N) (history : History N) (y : Vertex N e.skeleton.level → ℚ)
    (j : Fin 64) : ℚ := e.intercept history (e.skeleton.tuple j) -
  e.skeleton.signed (y (e.skeleton.tuple j))

end Expert

structure Probe (N : ℕ) where
  level : ℕ
  prices : Vertex N level → ℚ
  history : History N

/-- A single-coordinate feature, or an ordered difference of coordinates. -/
abbrev Feature (N : ℕ) := Fin N × Option (Fin N)

def featureValue {N : ℕ} (raw : Fin N → ℚ) (f : Feature N) : ℚ :=
  match f.2 with
  | none => raw f.1
  | some j => raw f.1 - raw j

/-- A feature and a queried threshold, retaining equalities as separate outcomes. -/
structure Test (N : ℕ) where
  feature : Feature N
  threshold : ℚ
deriving DecidableEq

namespace Skeleton
variable {N : ℕ} (s : Skeleton N)

def pairTest (y : Vertex N s.level → ℚ) (j j' : Fin 64) : Test N :=
  ⟨(s.origin j, some (s.origin j')), s.signed (y (s.tuple j) - y (s.tuple j'))⟩

def outsideTest (history : History N) (y : Vertex N s.level → ℚ) (j : Fin 64) : Test N :=
  match s.pivot with
  | none => ⟨(s.origin j, none), s.signed (y (s.tuple j))⟩
  | some ⟨k, i⟩ =>
    ⟨(s.origin j, some (rootVertex N k i)), s.signed (y (s.tuple j) - history k i)⟩

/-- Compute the observed feature thresholds at exactly the skeleton's destination. -/
def testsAt (probe : Probe N) : List (Test N) :=
  if h : probe.level = s.level then
    let y : Vertex N s.level → ℚ := h ▸ probe.prices
    (List.ofFn fun j : Fin 64 =>
      s.outsideTest probe.history y j :: List.ofFn fun j' : Fin 64 => s.pairTest y j j').flatten
  else []

theorem pairTest_difference (e : Expert N) (history : History N)
    (y : Vertex N e.skeleton.level → ℚ) (j j' : Fin 64) :
    let t := e.skeleton.pairTest y j j'
    e.utility history y j - e.utility history y j' = featureValue e.raw t.feature - t.threshold := by
  dsimp [Expert.utility, Expert.intercept, pairTest, featureValue, origin, signed]
  split <;> ring

theorem outsideTest_difference (e : Expert N) (history : History N)
    (y : Vertex N e.skeleton.level → ℚ) (j : Fin 64) :
    let t := e.skeleton.outsideTest history y j
    e.utility history y j = featureValue e.raw t.feature - t.threshold := by
  dsimp only [Expert.utility, Expert.intercept, shift, outsideTest, featureValue, origin, signed]
  cases hp : e.skeleton.pivot with
  | none => simp
  | some a =>
    obtain ⟨k, i⟩ := a
    simp only
    split <;> ring

end Skeleton
end PriceGame
end LinearProgramming
end Optimization
end OAI
