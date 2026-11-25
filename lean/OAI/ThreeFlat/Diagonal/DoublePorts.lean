import OAI.Computability.VPVNP.SlotGraph
import OAI.ThreeFlat.PortArcBound
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Removing expander loops by doubling its ports

Every old nonloop stays in its layer. A loop joins its two copies, and
every port receives one extra vertical slot. The common degree therefore
increases by one, independently of the size and the old loop counts.
-/

namespace ThreeFlat.Diagonal.DoublePorts
open Computability.VPVNP.Compression
open scoped BigOperators
variable {V : Type*} {h n : ℕ}

def multiplicity [DecidableEq V] (c : V → V → ℕ) (u v : Bool × V) : ℕ :=
  if u.1 = v.1 then (if u.2 = v.2 then 0 else c u.2 v.2)
  else (if u.2 = v.2 then c u.2 u.2 + 1 else 0)

theorem diagonal [DecidableEq V] (c : V → V → ℕ) (u : Bool × V) :
    multiplicity c u u = 0 := by simp [multiplicity]

theorem symmetric [DecidableEq V] (c : V → V → ℕ) (sym : ∀ x y, c x y = c y x)
    (u v : Bool × V) : multiplicity c u v = multiplicity c v u := by
  obtain ⟨b,x⟩ := u
  obtain ⟨b',y⟩ := v
  by_cases layer : b = b' <;> by_cases point : x = y <;>
    simp [multiplicity, layer, Ne.symm, point, eq_comm, sym x y]

theorem row_degree [Fintype V] [DecidableEq V] (c : V → V → ℕ) (rows : ∀ x, ∑ y, c x y = h)
    (u : Bool × V) : ∑ v, multiplicity c u v = h + 1 := by
  obtain ⟨b,x⟩ := u
  have pair (y : V) : (∑ t : Bool, multiplicity c (b,x) (t,y)) =
      c x y + (if y = x then 1 else 0) := by
    cases b <;> by_cases e : y = x <;> simp [multiplicity,e,Ne.symm,eq_comm]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [pair,Finset.sum_add_distrib,rows]
  simp

/-- Every multiplicity copy receives an explicit slot by the destination
order followed by its copy number. -/
def rowNumber [Fintype V] (order : V ≃ Fin n) (c : V → V → ℕ)
    (rows : ∀ x, ∑ y, c x y = h) (x : V) : (Σ y, Fin (c x y)) ≃ Fin h :=
  (Equiv.sigmaCongrLeft' (β := fun y => Fin (c x y)) order).trans
    (finSigmaFinEquiv.trans (finCongr ((order.symm.sum_comp (c x)).trans (rows x))))

def arcNumber [Fintype V] (order : V ≃ Fin n) (c : V → V → ℕ)
    (rows : ∀ x, ∑ y, c x y = h) : Expander.Arc c ≃ V × Fin h where
  toFun e := (e.1.1,rowNumber order c rows e.1.1 ⟨e.1.2,e.2⟩)
  invFun p := let q := (rowNumber order c rows p.1).symm p.2; ⟨(p.1,q.1),q.2⟩
  left_inv e := by
    obtain ⟨⟨x,y⟩,i⟩ := e
    exact congrArg (fun q : Σ j, Fin (c x j) => (⟨(x,q.1),q.2⟩ : Expander.Arc c))
      ((rowNumber order c rows x).symm_apply_apply ⟨y,i⟩)
  right_inv p := by obtain ⟨x,i⟩ := p; simp

def reverseArc (c : V → V → ℕ) (sym : ∀ x y, c x y = c y x) : Equiv.Perm (Expander.Arc c) where
  toFun e := ⟨(e.1.2,e.1.1), e.2.cast (sym _ _)⟩
  invFun e := ⟨(e.1.2,e.1.1), e.2.cast (sym _ _)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A symmetric, zero-diagonal multiplicity matrix with constant row sum
yields a regular loop-free graph in independently indexed port slots. -/
def ofMatrix [Fintype V] (order : V ≃ Fin n) (c : V → V → ℕ)
    (sym : ∀ x y, c x y = c y x) (rows : ∀ x, ∑ y, c x y = h) (zero : ∀ x, c x x = 0) :
    SlotGraph V h where
  target := (arcNumber order c rows).symm.trans ((reverseArc c sym).trans (arcNumber order c rows))
  ends_ne p := by
    obtain ⟨e,rfl⟩ := (arcNumber order c rows).surjective p
    simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
    obtain ⟨⟨x,y⟩,i⟩ := e
    change y ≠ x
    intro eq
    subst y
    exact Nat.not_lt_zero _ (i.isLt.trans_eq (zero x))

theorem ofMatrix_target [Fintype V] (order : V ≃ Fin n) (c : V → V → ℕ)
    (sym : ∀ x y, c x y = c y x) (rows : ∀ x, ∑ y, c x y = h) (zero : ∀ x, c x x = 0)
    (e : Expander.Arc c) : (ofMatrix order c sym rows zero).target (arcNumber order c rows e) =
      arcNumber order c rows (reverseArc c sym e) := by simp [ofMatrix]

theorem ofMatrix_sum [Fintype V] (order : V ≃ Fin n) (c : V → V → ℕ)
    (sym : ∀ x y, c x y = c y x) (rows : ∀ x, ∑ y, c x y = h) (zero : ∀ x, c x x = 0)
    (f : V → V → ℝ) :
    (∑ p : V × Fin h, f p.1 ((ofMatrix order c sym rows zero).target p).1) =
      ∑ x, ∑ y, (c x y : ℝ) * f x y := by
  rw [← (arcNumber order c rows).sum_comp, ← Expander.sum_arcs]
  apply Finset.sum_congr rfl
  intro e _
  rw [ofMatrix_target]
  rfl

def doubleOrder (order : V ≃ Fin n) : Bool × V ≃ Fin (2*n) :=
  (finTwoEquiv.symm.prodCongr order).trans finProdFinEquiv

def graph [Fintype V] [DecidableEq V] (order : V ≃ Fin n) (c : V → V → ℕ)
    (sym : ∀ x y, c x y = c y x) (rows : ∀ x, ∑ y, c x y = h) :
    SlotGraph (Bool × V) (h+1) :=
  ofMatrix (doubleOrder order) (multiplicity c) (symmetric c sym) (row_degree c rows) (diagonal c)

theorem sum_slots [Fintype V] [DecidableEq V] (order : V ≃ Fin n) (c : V → V → ℕ)
    (sym : ∀ x y, c x y = c y x) (rows : ∀ x, ∑ y, c x y = h) (f : (Bool × V) → (Bool × V) → ℝ) :
    (∑ p : (Bool × V) × Fin (h+1), f p.1 ((graph order c sym rows).target p).1) =
      ∑ x, ∑ y, (multiplicity c x y : ℝ) * f x y :=
  ofMatrix_sum (doubleOrder order) _ _ _ _ f

/-- For any edge weight, the only terms in a row are horizontal nonloops
and the old loop multiplicity plus one on the vertical edge. -/
theorem row_weight [Fintype V] [DecidableEq V] (c : V → V → ℕ)
    (b : Bool) (x : V) (f : (Bool × V) → ℝ) :
    (∑ v, (multiplicity c (b,x) v : ℝ) * f v) =
      (∑ y, (if x = y then 0 else (c x y : ℝ)) * f (b,y)) +
        (c x x + 1 : ℕ) * f (!b,x) := by
  let q := fun t : Bool => ∑ y, (multiplicity c (b,x) (t,y) : ℝ) * f (t,y)
  have hsum : (∑ t, q t) = q b + q (!b) := by cases b <;> simp [add_comm]
  have hor : q b = ∑ y, (if x = y then 0 else (c x y : ℝ)) * f (b,y) := by
    apply Finset.sum_congr rfl
    intro y _
    by_cases e : x = y <;> simp [multiplicity,e]
  have vert : q (!b) = (c x x + 1 : ℕ) * f (!b,x) := by
    calc
      _ = ∑ y, if y = x then (c x x + 1 : ℕ) * f (!b,x) else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases e : y = x <;> cases b <;> simp [multiplicity,e,Ne.symm,eq_comm]
      _ = _ := by simp
  rw [Fintype.sum_prod_type]
  exact hsum.trans (congrArg₂ _ hor vert)

/-- Index the doubled ports by one finite ordinal for the refresh motif. -/
def finMatrix (c : Fin n → Fin n → ℕ) (x y : Fin (2*n)) : ℕ :=
  let e := doubleOrder (Equiv.refl (Fin n))
  multiplicity c (e.symm x) (e.symm y)

theorem finMatrix_symmetric (c : Fin n → Fin n → ℕ) (sym : ∀ x y, c x y = c y x)
    (x y : Fin (2*n)) : finMatrix c x y = finMatrix c y x := symmetric c sym _ _

theorem finMatrix_diagonal (c : Fin n → Fin n → ℕ) (x : Fin (2*n)) :
    finMatrix c x x = 0 := diagonal c _

theorem finMatrix_rows (c : Fin n → Fin n → ℕ) (rows : ∀ x, ∑ y, c x y = h)
    (x : Fin (2*n)) : ∑ y, finMatrix c x y = h+1 := by
  let e := doubleOrder (Equiv.refl (Fin n))
  exact (e.symm.sum_comp (multiplicity c (e.symm x))).trans (row_degree c rows _)

def finGraph (c : Fin n → Fin n → ℕ) (sym : ∀ x y, c x y = c y x)
    (rows : ∀ x, ∑ y, c x y = h) : SlotGraph (Fin (2*n)) (h+1) :=
  ofMatrix (Equiv.refl _) (finMatrix c) (finMatrix_symmetric c sym) (finMatrix_rows c rows) (finMatrix_diagonal c)

theorem finGraph_sum (c : Fin n → Fin n → ℕ) (sym : ∀ x y, c x y = c y x)
    (rows : ∀ x, ∑ y, c x y = h) (f : Fin (2*n) → Fin (2*n) → ℝ) :
    (∑ p : Fin (2*n) × Fin (h+1), f p.1 ((finGraph c sym rows).target p).1) =
      ∑ x, ∑ y, (finMatrix c x y : ℝ) * f x y :=
  ofMatrix_sum (Equiv.refl _) _ _ _ _ f

end ThreeFlat.Diagonal.DoublePorts

end OAI
