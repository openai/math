import OAI.Optimization.LinearProgramming.PriceGame.VertexEncoding
import OAI.Optimization.LinearProgramming.PriceGame.Schedule
import Mathlib.Data.List.OfFn

/-! First-order public data for a suspended price-game computation. Saved arrays
contain only integers, rationals, and finite lists. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control

open States.Mass

structure PackedQuery where
  prices : List ℚ
  index : ℕ
deriving DecidableEq, Repr, Inhabited

structure PackedProbe where
  level : ℕ
  prices : List ℚ
  history : List (List ℚ)
deriving DecidableEq, Repr, Inhabited

structure PackedExpert where
  level : ℕ
  positive : Bool
  tuple : List ℕ
  pivot : Option (ℕ × ℕ)
  raw : List ℚ
deriving DecidableEq, Repr, Inhabited

structure PackedRound where
  prices : List ℚ
  scores : List ℕ
  log : List PackedProbe
deriving DecidableEq, Repr, Inhabited

structure PackedPopulation where
  experts : List PackedExpert
  weights : List ℚ
deriving DecidableEq, Repr, Inhabited

/-- Duplicated-coordinate rows use the public mixed-radix index of Section 4. -/
def packTable {α : Type*} (N l : ℕ) (f : Vertex N l → α) : List α :=
  List.ofFn fun i : Fin (N * 2^l) => f ((vertexEquivFin N l).symm i)

def lookupTable {α : Type*} [Inhabited α] (N l : ℕ) (row : List α) (i : Vertex N l) : α :=
  row[(vertexEquivFin N l i).val]?.getD default

theorem lookupTable_pack {α : Type*} [Inhabited α] (N l : ℕ) (f : Vertex N l → α)
    (i : Vertex N l) : lookupTable N l (packTable N l f) i = f i := by
  simp [lookupTable, packTable, (vertexEquivFin N l i).isLt]

@[simp] theorem length_packTable {α : Type*} (N l : ℕ) (f : Vertex N l → α) :
    (packTable N l f).length = N * 2^l := List.length_ofFn

def packQuery {N : ℕ} (q : Query N) : PackedQuery := ⟨List.ofFn q.prices, q.index.val⟩

def packHistory {N : ℕ} (l : ℕ) (h : History N) : List (List ℚ) :=
  List.ofFn fun j : Fin l => packTable N j (h j)

def unpackHistory (N : ℕ) (rows : List (List ℚ)) : History N :=
  fun j i => lookupTable N j (rows[j]?.getD []) i

theorem unpackHistory_pack {N l j : ℕ} (h : History N) (hj : j < l) (i : Vertex N j) :
    unpackHistory N (packHistory l h) j i = h j i := by
  simp [unpackHistory, packHistory, hj, lookupTable_pack]

def packProbe {N : ℕ} (p : Probe N) : PackedProbe :=
  ⟨p.level, packTable N p.level p.prices, packHistory p.level p.history⟩

def unpackProbe (N : ℕ) (p : PackedProbe) : Probe N :=
  ⟨p.level, lookupTable N p.level p.prices, unpackHistory N p.history⟩

@[simp] theorem unpackProbe_pack_level {N : ℕ} (p : Probe N) :
    (unpackProbe N (packProbe p)).level = p.level := rfl

@[simp] theorem unpackProbe_pack_prices {N : ℕ} (p : Probe N) :
    (unpackProbe N (packProbe p)).prices = p.prices := by
  funext i
  exact lookupTable_pack N p.level p.prices i

theorem unpackProbe_pack_earlier {N j : ℕ} (p : Probe N) (hj : j < p.level) (i : Vertex N j) :
    (unpackProbe N (packProbe p)).history j i = p.history j i := unpackHistory_pack p.history hj i

def packExpert {N : ℕ} (e : Expert N) : PackedExpert where
  level := e.skeleton.level
  positive := e.skeleton.positive
  tuple := List.ofFn fun j => (vertexEquivFin N e.skeleton.level (e.skeleton.tuple j)).val
  pivot := e.skeleton.pivot.map fun p => (p.1.val, (vertexEquivFin N p.1 p.2).val)
  raw := List.ofFn e.raw

def packRound {N : ℕ} (ne : ℕ) (r : RoundResult N) : PackedRound :=
  ⟨List.ofFn r.prices, List.ofFn fun e : Fin ne => r.scores e.val, r.observations.map packProbe⟩

def packPopulation {N : ℕ} (p : Population N) : PackedPopulation :=
  ⟨p.experts.map packExpert, p.weights.toList⟩

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
