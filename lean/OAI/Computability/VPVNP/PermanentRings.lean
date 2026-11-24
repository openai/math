import OAI.Computability.VPVNP.PermanentCoefficient
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Variable rings in the permanent reduction

Each row of a variable ring chooses its own column or the next column cyclically.
Covering all columns exactly once forces a common choice throughout each ring.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open scoped BigOperators

/-- One ring of length `m + 2` for each of the `k` variables. -/
abbrev RingRow (k m : ℕ) := Fin k × Fin (m + 2)

variable {k m : ℕ}

/-- The false edge stays in the column of its row. The true edge advances cyclically. -/
def ringTarget (u : RingRow k m) (b : Bool) : RingRow k m :=
  (u.1, if b then u.2 + 1 else u.2)

/-- Two consecutive rows of a permutation must make the same choice. -/
private theorem ringChoice_step (b : RingRow k m → Bool)
    (hb : Function.Bijective fun u => ringTarget u (b u))
    (v : Fin k) (j : Fin (m + 1)) :
    b (v, j.succ) = b (v, j.castSucc) := by
  cases hj : b (v, j.castSucc) <;> cases hs : b (v, j.succ)
  · rfl
  · obtain ⟨⟨v', i⟩, hi⟩ := hb.2 (v, j.succ)
    have hv : v' = v := congrArg Prod.fst hi
    subst v'
    have hc := congrArg Prod.snd hi
    cases h : b (v, i) with
    | false =>
      have e : i = j.succ := by simpa [ringTarget, h] using hc
      rw [e, hs] at h
      contradiction
    | true =>
      have e : i + 1 = j.castSucc + 1 := by simpa [ringTarget, h, Fin.coeSucc_eq_succ] using hc
      rw [add_right_cancel e, hj] at h
      contradiction
  · have e := hb.1 (a₁ := (v, j.castSucc)) (a₂ := (v, j.succ))
        (by simp [ringTarget, hj, hs, Fin.coeSucc_eq_succ])
    exact (Fin.castSucc_lt_succ.ne (congrArg Prod.snd e)).elim
  · rfl

/-- The destinations permute all ring positions exactly when each variable chooses
one of its two orientations consistently. -/
theorem ringTarget_bijective_iff (b : RingRow k m → Bool) :
    (Function.Bijective fun u => ringTarget u (b u)) ↔
      ∀ v j, b (v, j) = b (v, 0) := by
  constructor
  · intro hb v j
    induction j using Fin.induction with
    | zero => rfl
    | succ j ih => exact (ringChoice_step b hb v j).trans ih
  · intro h
    constructor
    · rintro ⟨v, i⟩ ⟨w, j⟩ he
      have hw : v = w := congrArg Prod.fst he
      subst w
      have hc := congrArg Prod.snd he
      cases hv : b (v, 0) <;> simpa [ringTarget, h v i, h v j, hv] using hc
    · rintro ⟨v, i⟩
      cases hv : b (v, 0) with
      | false => exact ⟨(v, i), by simp [ringTarget, h v i, hv]⟩
      | true => exact ⟨(v, i - 1), by simp [ringTarget, h v (i - 1), hv]⟩

/-- The full column monomial selects precisely the consistent ring choices. -/
theorem ringDegrees_eq_full_iff (b : RingRow k m → Bool) :
    (∑ u, Finsupp.single (ringTarget u (b u)) 1) = fullDegree (RingRow k m) ↔
      ∀ v j, b (v, j) = b (v, 0) := by
  rw [degrees_eq_full_iff, ringTarget_bijective_iff]

/-- Reading the orientation at position zero identifies consistent choices with
Boolean assignments to the variables. -/
def ringChoicesEquiv (k m : ℕ) :
    {b : RingRow k m → Bool // ∀ v j, b (v, j) = b (v, 0)} ≃ (Fin k → Bool) where
  toFun b v := b.1 (v, 0)
  invFun x := ⟨fun u => x u.1, fun _ _ => rfl⟩
  left_inv b := Subtype.ext (funext fun u => (b.2 u.1 u.2).symm)
  right_inv _ := rfl

open scoped Classical in
/-- After imposing the full ring-column degree, the sum over row choices counts
each Boolean assignment once, with its original weight. -/
theorem sum_ring_choices {A : Type*} [AddCommMonoid A] (weight : (RingRow k m → Bool) → A) :
    (∑ b, if (∑ u, Finsupp.single (ringTarget u (b u)) 1) = fullDegree (RingRow k m)
      then weight b else 0) = ∑ x : Fin k → Bool, weight (fun u => x u.1) := by
  simp_rw [ringDegrees_eq_full_iff]
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun b : RingRow k m → Bool =>
    ∀ v j, b (v, j) = b (v, 0)) _ (by simp)]
  exact (ringChoicesEquiv k m).symm.sum_comp (fun b => weight b.val) |>.symm

end PermanentReduction

end VPVNP
end Computability
end OAI
