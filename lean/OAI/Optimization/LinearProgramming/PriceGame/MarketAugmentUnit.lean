import OAI.Optimization.LinearProgramming.PriceGame.MarketGraph
import OAI.Optimization.LinearProgramming.PriceGame.MarketExistence
import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentPath
import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentBits

/-! The integral update along a simple augmenting path in the expert–good residual graph. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment

open Quiver OAI.Optimization.LinearProgramming.PriceGame.Market.Graph
open OAI.Optimization.LinearProgramming.PriceGame.Market.Optimum

variable {E G : Type*} (n : Network E G)

/-- The two types of vertex potential in a market form one potential on the residual graph. -/
def combine (p : E → ℚ) (q : Option G → ℚ) : Vertex n → ℚ
  | .expert e => p e
  | .opt o => q o

/-- Every residual arc obeys the dual inequality. Reverse arcs use tightness of old positive flow. -/
theorem residual_arc {p : E → ℚ} {q : Option G → ℚ}
    (hpot : ResidualPotentials n.pos n.accepts n.c n.f p q)
    {u v : Vertex n} (a : u ⟶ v) : n.weight a ≤ combine n p q u - combine n p q v := by
  cases u <;> cases v
  · exact a.down.elim
  · rename_i e o
    obtain ⟨ok, h⟩ := a.down
    cases he : n.pos e with
    | false =>
      have hb := hpot.backward e o (h.resolve_left (by simp [he]))
      simp [Network.weight, combine, side, he] at hb ⊢
      linarith
    | true => simpa [combine, Network.weight, side, he] using hpot.forward e o ok
  · rename_i o e
    obtain ⟨ok, h⟩ := a.down
    cases he : n.pos e with
    | false =>
      have hb := hpot.forward e o ok
      simp [Network.weight, combine, side, he] at hb ⊢
      linarith
    | true =>
      have hb := hpot.backward e o (h.resolve_left (by simp [he]))
      simp [Network.weight, combine, side, he] at hb ⊢
      linarith
  · exact a.down.elim

variable [DecidableEq E] [DecidableEq G]

private theorem tight_changed_arc {u v : Vertex n} (a : u ⟶ v) (q : Vertex n → ℚ)
    (tight : n.weight a = q u - q v) (e : E) (o : Option G) (h : 0 < n.edgeUnits a e o) :
    side n.pos e * (q (.expert e) - q (.opt o)) = bid n.c e o := by
  cases u <;> cases v
  · exact a.down.elim
  · rename_i j i
    by_cases heq : e = j ∧ o = i
    · rcases heq with ⟨rfl, rfl⟩
      cases he : n.pos e <;> simp_all [Network.weight, Network.edgeUnits, Network.signedUnit, side]
    · simp [Network.edgeUnits, heq] at h
  · rename_i i j
    by_cases heq : e = j ∧ o = i
    · rcases heq with ⟨rfl, rfl⟩
      cases he : n.pos e <;> simp_all [Network.weight, Network.edgeUnits, Network.signedUnit, side]
    · simp [Network.edgeUnits, heq] at h
  · exact a.down.elim

private theorem tight_changed_path (q : Vertex n → ℚ)
    (hq : ∀ {u v : Vertex n} (a : u ⟶ v), n.weight a ≤ q u - q v)
    {s t : Vertex n} (path : Path s t) (tight : path.addWeight n.weight = q s - q t)
    (e : E) (o : Option G) (hg : 0 < n.change path e o) :
    side n.pos e * (q (.expert e) - q (.opt o)) = bid n.c e o := by
  induction path with
  | nil => simp at hg
  | @cons v z p a ih =>
    have hp := path_le_drop n.weight hq p
    have ha := hq a
    rw [Path.addWeight_cons] at tight
    have eqp : p.addWeight n.weight = q s - q v := by linarith
    have eqa : n.weight a = q v - q z := by linarith
    by_cases hprev : 0 < n.change p e o
    · exact ih eqp hprev
    · rw [Network.change_cons] at hg
      exact tight_changed_arc n a q eqa e o (by omega)

/-- Natural-number flow after adding a path’s signed integer increments. -/
def applyPath {s t : Vertex n} (p : Path s t) (e : E) (o : Option G) : ℕ :=
  ((n.f e o : ℤ) + n.change p e o).toNat

theorem applyPath_cast {s t : Vertex n} (p : Path s t) (simple : p.vertices.Nodup)
    (e : E) (o : Option G) : (applyPath n p e o : ℤ) = n.f e o + n.change p e o :=
  Int.toNat_of_nonneg (n.capacity_of_nodup p (simple.sublist p.vertices.dropLast_sublist) e o)

/-- Positive flow after a tight unit augmentation is tight for the new residual dual. -/
theorem residual_applyPath [Fintype E] [Fintype G] {qty : E → ℕ}
    (f : Feasible n.pos qty n.accepts n.f) (q : Vertex n → ℚ)
    (hq : ∀ {u v : Vertex n} (a : u ⟶ v), n.weight a ≤ q u - q v)
    {s t : Vertex n} (p : Path s t) (simple : p.vertices.Nodup)
    (tight : p.addWeight n.weight = q s - q t) :
    ResidualPotentials n.pos n.accepts n.c (applyPath n p)
      (fun e => q (.expert e)) (fun o => q (.opt o)) := by
  have orig := n.residual_of_inequalities q (n.supports_of_feasible f) hq
  refine ⟨orig.forward, fun e o hp => ?_⟩
  by_cases h : 0 < n.f e o
  · exact orig.backward e o h
  · have hx := applyPath_cast n p simple e o
    exact (tight_changed_path n q hq p tight e o (by omega)).le

/-- An additional unit travels from a positive expert to the dummy, or from the dummy to a
negative expert. Both cases increase the expert's unsigned row total. -/
def start (i : E) : Vertex n := if n.pos i then .expert i else .opt none

def finish (i : E) : Vertex n := if n.pos i then .opt none else .expert i

def direct (i : E) : start n i ⟶ finish n i := by
  cases h : n.pos i <;> simp only [start, finish, h, Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨⟨True.intro, Or.inl h⟩⟩
  · exact ⟨⟨True.intro, Or.inl h⟩⟩

omit [DecidableEq G] in
private theorem expert_endpoints (i e : E) :
    n.eMark e (start n i) - n.eMark e (finish n i) = if e = i then 1 else 0 := by
  by_cases h : e = i
  · subst e
    cases h : n.pos i <;> simp [start, finish, h, Network.eMark, Network.signedUnit]
  · cases hi : n.pos i <;> simp [start, finish, hi, Network.eMark, h, Ne.symm h]

omit [DecidableEq E] in
private theorem option_endpoints (i : E) (j : G) :
    n.oMark (some j) (finish n i) - n.oMark (some j) (start n i) = 0 := by
  cases hi : n.pos i <;> simp [start, finish, hi, Network.oMark]

/-- Exact balances of a simple unit augmentation, including preservation of all real-good
columns and of every unavailable arc. -/
theorem feasible_applyPath [Fintype E] [Fintype G] {qty : E → ℕ}
    (f : Feasible n.pos qty n.accepts n.f) (i : E)
    (p : Path (start n i) (finish n i)) (simple : p.vertices.Nodup) :
    Feasible n.pos (fun e => qty e + if e = i then 1 else 0) n.accepts (applyPath n p) := by
  constructor
  · intro e
    have hrow : ∑ o, (n.f e o : ℤ) = (qty e : ℤ) := by exact_mod_cast f.row e
    have h : ∑ o, (applyPath n p e o : ℤ) = (qty e : ℤ) + if e = i then 1 else 0 := by
      simp_rw [applyPath_cast n p simple]
      rw [Finset.sum_add_distrib, hrow, n.row_change, expert_endpoints]
    by_cases hi : e = i <;> simp [hi] at h ⊢ <;> exact_mod_cast h
  · intro e j hj
    have h := applyPath_cast n p simple e (some j)
    rw [f.unavailable e j hj, n.change_forbidden p e (some j) hj] at h
    omega
  · intro j
    have ec (e : E) : (applyPath n p e (some j) : ℚ) = (n.f e (some j) : ℚ) +
        (n.change p e (some j) : ℚ) := by exact_mod_cast applyPath_cast n p simple e (some j)
    change ∑ e, side n.pos e * (applyPath n p e (some j) : ℚ) = 0
    simp_rw [ec, mul_add]
    rw [Finset.sum_add_distrib, show ∑ e, side n.pos e * (n.f e (some j) : ℚ) = 0 from f.good j,
      zero_add, n.option_change, option_endpoints]

/-- For each next binary unit in a particular row, a maximum-weight simple residual path
preserves integral feasibility and carries its own certificate of optimality. -/
theorem one_unit [Fintype E] [Fintype G] {qty : E → ℕ} (i : E)
    (f : Feasible n.pos qty n.accepts n.f) (qE : E → ℚ) (qO : Option G → ℚ)
    (dual : ResidualPotentials n.pos n.accepts n.c n.f qE qO) :
    ∃ (p : Path (start n i) (finish n i)) (q : Vertex n → ℚ),
      p.vertices.Nodup ∧ (∀ z : Path (start n i) (finish n i), z.addWeight n.weight ≤ p.addWeight n.weight) ∧
      Feasible n.pos (fun e => qty e + if e = i then 1 else 0) n.accepts (applyPath n p) ∧
      ResidualPotentials n.pos n.accepts n.c (applyPath n p)
        (fun e => q (.expert e)) (fun o => q (.opt o)) := by
  classical
  let ref := (direct n i).toPath
  let π := combine n qE qO
  let q := targetedPotential n.weight π ref
  obtain ⟨hq, p, simple, tight⟩ := targeted_path n.weight π (residual_arc n dual) ref
  exact ⟨p, q, simple, optimal_of_tight n.weight hq p tight,
    feasible_applyPath n f i p simple, residual_applyPath n f q hq p simple tight⟩

end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
