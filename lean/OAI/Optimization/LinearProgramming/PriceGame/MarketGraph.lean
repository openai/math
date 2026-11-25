import OAI.Optimization.LinearProgramming.PriceGame.Market
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype

/-! # Residual walks in the expert–good network -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Graph

open Quiver
open OAI.Optimization.LinearProgramming.PriceGame.Market

variable {E G : Type*}

structure Network (E G : Type*) where
  pos : E → Bool
  accepts : E → G → Prop
  c : E → G → ℚ
  f : E → Option G → ℕ

inductive Vertex (n : Network E G)
  | expert (e : E)
  | opt (o : Option G)
  deriving DecidableEq, Fintype

variable (n : Network E G)

namespace Network

def Allowed : Vertex n → Vertex n → Prop
  | .expert e, .opt o => eligible n.accepts e o ∧ (n.pos e = true ∨ 0 < n.f e o)
  | .opt o, .expert e => eligible n.accepts e o ∧ (n.pos e = false ∨ 0 < n.f e o)
  | _, _ => False

instance : Quiver (Vertex n) where
  Hom v w := PLift (Allowed n v w)

noncomputable instance (a b : Vertex n) : Fintype (a ⟶ b) := by
  classical
  exact PLift.fintypeProp _

def signedUnit (e : E) : ℤ := if n.pos e then 1 else -1

@[simp] theorem signedUnit_cast (e : E) : (n.signedUnit e : ℚ) = side n.pos e := by
  cases h : n.pos e <;> simp [signedUnit, side, h]

@[simp] theorem side_sq (e : E) : side n.pos e * side n.pos e = 1 := by
  simp [side]
  split <;> norm_num

/-- One unit of the forward orientation, negative for a reverse residual arc. -/
def edgeUnits [DecidableEq E] [DecidableEq G] :
    ∀ {a b : Vertex n}, (a ⟶ b) → E → Option G → ℤ
  | .expert e, .opt o, _, k, j => if k = e ∧ j = o then n.signedUnit e else 0
  | .opt o, .expert e, _, k, j => if k = e ∧ j = o then -n.signedUnit e else 0
  | _, _, _, _, _ => 0

def weight : ∀ {a b : Vertex n}, (a ⟶ b) → ℚ
  | .expert e, .opt o, _ => side n.pos e * bid n.c e o
  | .opt o, .expert e, _ => -(side n.pos e * bid n.c e o)
  | _, _, _ => 0

def change [DecidableEq E] [DecidableEq G] {a b : Vertex n} (p : Quiver.Path a b)
    (e : E) (o : Option G) : ℤ :=
  p.addWeight fun h => n.edgeUnits h e o

@[simp] theorem change_nil [DecidableEq E] [DecidableEq G] (a : Vertex n) (e : E)
    (o : Option G) : n.change (Quiver.Path.nil : Quiver.Path a a) e o = 0 := by simp [change]

@[simp] theorem change_cons [DecidableEq E] [DecidableEq G] {a b c : Vertex n}
    (p : Quiver.Path a b) (h : b ⟶ c) (e : E) (o : Option G) :
    n.change (p.cons h) e o = n.change p e o + n.edgeUnits h e o := by simp [change]

/-- Vertex incidence at an expert, in the sign convention of the market. -/
def eMark [DecidableEq E] (e : E) : Vertex n → ℤ
  | .expert k => if k = e then n.signedUnit e else 0
  | .opt _ => 0

/-- Vertex incidence at an option, including the dummy. -/
def oMark [DecidableEq G] (o : Option G) : Vertex n → ℚ
  | .expert _ => 0
  | .opt j => if j = o then 1 else 0

theorem edge_row [Fintype G] [DecidableEq E] [DecidableEq G] {a b : Vertex n}
    (h : a ⟶ b) (e : E) : ∑ o, n.edgeUnits h e o = n.eMark e a - n.eMark e b := by
  cases a <;> cases b
  · exact h.down.elim
  · rename_i k o
    by_cases hke : k = e
    · subst k; simp [edgeUnits, eMark]
    · simp [edgeUnits, eMark, hke, Ne.symm hke]
  · rename_i o k
    by_cases hke : k = e
    · subst k; simp [edgeUnits, eMark]
    · simp [edgeUnits, eMark, hke, Ne.symm hke]
  · exact h.down.elim

theorem edge_option [Fintype E] [DecidableEq E] [DecidableEq G] {a b : Vertex n}
    (h : a ⟶ b) (o : Option G) :
    ∑ e, side n.pos e * (n.edgeUnits h e o : ℚ) = n.oMark o b - n.oMark o a := by
  cases a <;> cases b
  · exact h.down.elim
  · rename_i e j
    by_cases heq : j = o
    · subst j; simp [edgeUnits, oMark, mul_ite]
    · simp [edgeUnits, oMark, heq, Ne.symm heq]
  · rename_i j e
    by_cases heq : j = o
    · subst j; simp [edgeUnits, oMark, mul_ite]
    · simp [edgeUnits, oMark, heq, Ne.symm heq]
  · exact h.down.elim

theorem edge_weight [Fintype E] [Fintype G] [DecidableEq E] [DecidableEq G]
    {a b : Vertex n} (h : a ⟶ b) :
    ∑ e, ∑ o, bid n.c e o * (n.edgeUnits h e o : ℚ) = n.weight h := by
  cases a <;> cases b
  · exact h.down.elim
  · rename_i k j
    simp_rw [edgeUnits, ite_and]
    simp [mul_ite, weight, mul_comm]
  · rename_i j k
    simp_rw [edgeUnits, ite_and]
    simp [mul_ite, weight, mul_comm]
  · exact h.down.elim

theorem row_change [Fintype G] [DecidableEq E] [DecidableEq G] {a b : Vertex n}
    (p : Quiver.Path a b) (e : E) : ∑ o, n.change p e o = n.eMark e a - n.eMark e b := by
  induction p with
  | nil => simp
  | cons p h ih => simp only [change_cons, Finset.sum_add_distrib, ih, edge_row]; abel

theorem option_change [Fintype E] [DecidableEq E] [DecidableEq G] {a b : Vertex n}
    (p : Quiver.Path a b) (o : Option G) :
    ∑ e, side n.pos e * (n.change p e o : ℚ) = n.oMark o b - n.oMark o a := by
  induction p with
  | nil => simp
  | cons p h ih =>
    simp only [change_cons, Int.cast_add, mul_add, Finset.sum_add_distrib, ih, edge_option]
    abel

theorem weight_change [Fintype E] [Fintype G] [DecidableEq E] [DecidableEq G]
    {a b : Vertex n} (p : Quiver.Path a b) :
    ∑ e, ∑ o, bid n.c e o * (n.change p e o : ℚ) = p.addWeight n.weight := by
  induction p with
  | nil => simp
  | cons p h ih =>
    simp only [change_cons, Int.cast_add, mul_add, Finset.sum_add_distrib, ih, edge_weight,
      Quiver.Path.addWeight_cons]

theorem edge_forbidden [DecidableEq E] [DecidableEq G] {a b : Vertex n}
    (h : a ⟶ b) (e : E) (o : Option G) (notAvailable : ¬ eligible n.accepts e o) :
    n.edgeUnits h e o = 0 := by
  cases a <;> cases b
  · rfl
  · rename_i k j
    simp only [edgeUnits]
    split_ifs with eqs
    · rcases eqs with ⟨rfl,rfl⟩
      exact (notAvailable h.down.1).elim
    · rfl
  · rename_i j k
    simp only [edgeUnits]
    split_ifs with eqs
    · rcases eqs with ⟨rfl,rfl⟩
      exact (notAvailable h.down.1).elim
    · rfl
  · rfl

theorem change_forbidden [DecidableEq E] [DecidableEq G] {a b : Vertex n}
    (p : Quiver.Path a b) (e : E) (o : Option G) (h : ¬ eligible n.accepts e o) :
    n.change p e o = 0 := by
  induction p with
  | nil => simp
  | cons p t ih => simp [ih, edge_forbidden n t e o h]

/-- A reverse traversal of an expert's option can only leave this vertex. -/
def reverseTail (e : E) (o : Option G) : Vertex n :=
  if n.pos e then .opt o else .expert e

theorem edge_lower [DecidableEq E] [DecidableEq G] {a b : Vertex n}
    (t : a ⟶ b) (e : E) (o : Option G) :
    -(if a = n.reverseTail e o then 1 else 0 : ℤ) ≤ n.edgeUnits t e o := by
  cases a <;> cases b
  · exact t.down.elim
  · rename_i k j
    by_cases eqs : e = k ∧ o = j
    · rcases eqs with ⟨rfl, rfl⟩
      cases hp : n.pos e <;> simp [edgeUnits, reverseTail, signedUnit, hp]
    · simp only [edgeUnits, ite_eq_right eqs]
      split <;> decide
  · rename_i j k
    by_cases eqs : e = k ∧ o = j
    · rcases eqs with ⟨rfl, rfl⟩
      cases hp : n.pos e <;> simp [edgeUnits, reverseTail, signedUnit, hp]
    · simp only [edgeUnits, ite_eq_right eqs]
      split <;> decide
  · exact t.down.elim

theorem edge_nonneg_of_zero [DecidableEq E] [DecidableEq G] {a b : Vertex n}
    (t : a ⟶ b) (e : E) (o : Option G) (hz : n.f e o = 0) :
    0 ≤ n.edgeUnits t e o := by
  cases a <;> cases b
  · exact t.down.elim
  · rename_i k j
    by_cases eqs : e = k ∧ o = j
    · rcases eqs with ⟨rfl, rfl⟩
      have := t.down.2.resolve_right (by omega)
      simp [edgeUnits, signedUnit, this]
    · simp [edgeUnits, eqs]
  · rename_i j k
    by_cases eqs : e = k ∧ o = j
    · rcases eqs with ⟨rfl, rfl⟩
      have := t.down.2.resolve_right (by omega)
      simp [edgeUnits, signedUnit, this]
    · simp [edgeUnits, eqs]
  · exact t.down.elim

theorem change_nonneg_of_zero [DecidableEq E] [DecidableEq G] {a b : Vertex n}
    (p : Quiver.Path a b) (e : E) (o : Option G) (hz : n.f e o = 0) :
    0 ≤ n.change p e o := by
  induction p with
  | nil => simp
  | cons p t ih => rw [change_cons]; exact add_nonneg ih (edge_nonneg_of_zero n t e o hz)

theorem change_lower [DecidableEq E] [DecidableEq G] {a b : Vertex n}
    (p : Quiver.Path a b) (e : E) (o : Option G) :
    -((p.vertices.dropLast.count (n.reverseTail e o) : ℕ) : ℤ) ≤ n.change p e o := by
  induction p with
  | nil => simp
  | @cons b c p t ih =>
    rw [change_cons, Quiver.Path.vertices_cons]
    simp only [List.concat_eq_append, List.dropLast_concat]
    rw [← p.dropLast_append_end_eq, List.count_append]
    have hs := edge_lower n t e o
    by_cases hb : b = n.reverseTail e o
    · simp [hb] at *; omega
    · simp [hb] at *; omega

theorem capacity_of_nodup [DecidableEq E] [DecidableEq G] {a b : Vertex n}
    (p : Quiver.Path a b) (hs : p.vertices.dropLast.Nodup) (e : E) (o : Option G) :
    0 ≤ (n.f e o : ℤ) + n.change p e o := by
  by_cases hz : n.f e o = 0
  · simpa [hz] using n.change_nonneg_of_zero p e o hz
  · have hc := (List.nodup_iff_count_le_one.mp hs) (n.reverseTail e o)
    have := n.change_lower p e o
    omega

end Network

end Graph
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
