import OAI.Computability.BorderVNP.ShortenNetworkHistory
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Splitting charged cables into consecutive intervals

A prefix cut introduces two cables with the same endpoints. The local tables
recover the old bit word in its original order. Such cuts can be iterated
before choosing the groups to match, without changing the tensor or the
charged length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open scoped BigOperators Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (firstWidth : N.Edge → ℕ)

/-- Keep the prefix and suffix of each cable on separate parallel cables. -/
def intervals : Network D P bits where
  Site := N.Site
  Edge := N.Edge ⊕ N.Edge
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := Sum.elim N.src N.src
  dst := Sum.elim N.dst N.dst
  width := Sum.elim firstWidth fun e => N.width e - firstWidth e
  attach := N.attach
  position := N.position
  in_ball := N.in_ball

private def splitBit {a n : ℕ} (h : a ≤ n) : Fin n ≃ Fin a ⊕ Fin (n-a) :=
  (finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm

variable {R : Type*}

/-- The new local tables concatenate the two intervals in their original order. -/
def intervalTables (h : ∀ e, firstWidth e ≤ N.width e) (table : N.Tables R) :
    (N.intervals firstWidth).Tables R := fun v a x =>
  table v (fun e k => Sum.elim (a ⟨.inl e.val, e.property⟩) (a ⟨.inr e.val, e.property⟩)
    (splitBit (h e.val) k)) x

private def intervalEquiv (h : ∀ e, firstWidth e ≤ N.width e) :
    (N.intervals firstWidth).Assignment ≃ N.Assignment where
  toFun a e k := Sum.elim (a (.inl e)) (a (.inr e)) (splitBit (h e) k)
  invFun a := fun
    | .inl e, k => a e ((splitBit (h e)).symm (.inl k))
    | .inr e, k => a e ((splitBit (h e)).symm (.inr k))
  left_inv a := by funext e k; cases e <;> simp only [Equiv.apply_symm_apply] <;> rfl
  right_inv a := by
    funext e k
    let split := splitBit (h e)
    have atPart (i : Fin (firstWidth e) ⊕ Fin (N.width e - firstWidth e)) :
        Sum.elim (fun z => a e (split.symm (.inl z))) (fun z => a e (split.symm (.inr z))) i =
          a e (split.symm i) := by cases i <;> rfl
    exact (atPart (split k)).trans (congrArg (a e) (split.symm_apply_apply k))

/-- The two intervals describe exactly one original cable assignment. -/
theorem value_intervals [CommSemiring R] (h : ∀ e, firstWidth e ≤ N.width e)
    (table : N.Tables R) (x : Ports bits) :
    (N.intervals firstWidth).value (N.intervalTables firstWidth h table) x = N.value table x := by
  unfold value
  exact Fintype.sum_equiv (N.intervalEquiv firstWidth h) _ _ fun _ => rfl

/-- Splitting widths preserves their total width-weighted length. -/
theorem cost_intervals (h : ∀ e, firstWidth e ≤ N.width e) :
    (N.intervals firstWidth).cost = N.cost := by
  unfold cost
  dsimp (config := { instances := true }) only [intervals]
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Sum.elim_inl, Sum.elim_inr, Nat.cast_sub (h e)]
  ring

end Crossing.Network

end BorderVNP
end Computability
end OAI
