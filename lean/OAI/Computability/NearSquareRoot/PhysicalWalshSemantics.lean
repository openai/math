import OAI.Computability.NearSquareRoot.PhysicalWalshPlan
import OAI.Computability.NearSquareRoot.KernelPassBank

/-! # Exact semantics of normalized Walsh plans

The ideal leaf operations on rational rows have the same interfaces as the
physical compiler's four leaves. Their serial and parallel evaluation realizes
the plan's matrix on the concatenated bank of address-indexed rows.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh

open KernelPass Matrix

variable {U H R : Type} {A i o : ℕ}

/-- The width, common header and row serialization are independent of the
exact arithmetic used to describe the ideal row operations. -/
def exactLayout (A : ℕ) (width : U → ℕ) (header : U → H)
    (store : (u : U) → (Addr A (width u) → ℚ) → R) : Layout U H R where
  Row u := Addr A (width u) → ℚ
  header := header
  store := store

variable (width : U → ℕ) (header : U → H) (store : (u : U) → (Addr A (width u) → ℚ) → R)

/-- A unary primitive consumes and returns its only row. -/
private def singleRow (p : Plan A 1 1) (h : ℕ) (x : Addr A h → ℚ) : Addr A h → ℚ :=
  p.applyAt h (fun _ => x) 0

/-- The four exact rational leaf actions, before fixed-point rounding. -/
def exactOps : Ops A (exactLayout A width header store) where
  mix c u x := (Plan.mix c).applyAt (width u) x
  xor g u := singleRow (.xor g) (width u)
  scale q t c u := singleRow (.scale q t c) (width u)
  child a u := singleRow (.child a) (width u)

private theorem unary_bank (p : Plan A 1 1) (h : ℕ) (x : Bank A h 1) :
    (fun _ : Fin 1 => singleRow p h (x 0)) = p.applyAt h x := by
  have hx : (fun _ : Fin 1 => x 0) = x := funext fun a => congrArg x (Subsingleton.elim 0 a)
  funext a
  rw [singleRow, hx, Subsingleton.elim a 0]

/-- On a whole row bank the evaluator used by the physical compiler agrees with
the matrix action, including its division of the rows for parallel execution. -/
theorem applyPlan_eq_applyAt (p : Plan A i o) (u : U) (x : Bank A (width u) i) :
    (exactOps width header store).applyPlan p u x = p.applyAt (width u) x := by
  induction p with
  | mix c => rfl
  | xor g => exact unary_bank _ _ _
  | scale q t c => exact unary_bank _ _ _
  | child a => exact unary_bank _ _ _
  | seq p q hp hq =>
    change (exactOps width header store).applyPlan p u ((exactOps width header store).applyPlan q u x) = _
    rw [hq, hp, Plan.applyAt_seq]
  | @parallel i j o b p q hp hq =>
    change Fin.append
      ((exactOps width header store).applyPlan p u (fun a => x (a.castAdd j)))
      ((exactOps width header store).applyPlan q u (fun a => x (a.natAdd i))) = _
    rw [hp, hq]
    have h := Plan.applyAt_parallel p q (h := width u)
      (fun a => x (a.castAdd j)) (fun a => x (a.natAdd i))
    rw [Fin.append_castAdd_natAdd] at h
    exact h.symm

theorem applyPlan_eq_mulVec (p : Plan A i o) (u : U) (x : Bank A (width u) i) :
    (exactOps width header store).applyPlan p u x =
      Function.curry ((p.eval (width u)).mulVec (Function.uncurry x)) :=
  applyPlan_eq_applyAt width header store p u x

/-- A certified template applied by the exact compiler semantics performs the
normalized Walsh transform independently on each row at every even child width. -/
theorem applyPlan_correct {W : ℕ} {p : Plan A W W} (hp : Correct p)
    (u : U) (x : Bank A (width u) W) :
    (exactOps width header store).applyPlan p u x =
      Function.curry ((target A W (width u)).mulVec (Function.uncurry x)) := by
  rw [applyPlan_eq_mulVec, hp]

end PhysicalWalsh

end NearSquareRoot
end Computability
end OAI
