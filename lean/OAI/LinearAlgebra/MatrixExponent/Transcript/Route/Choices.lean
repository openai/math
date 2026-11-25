import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Pi

/-!
# Unique codes for expansion choices

Dependent sums concatenate stage codes. Products assign a separate
field to each independent local choice. Out-of-range indices are
rejected and padding gives no extra multiplicity.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript

structure Selector (I C : Type) where
  write : I → C
  read : C → Option I
  valid : ∀ c i, read c = some i ↔ c = write i

namespace Selector

variable {I C D : Type}

theorem injective (S : Selector I C) : Function.Injective S.write := by
  intro i j he
  exact Option.some.inj (((S.valid _ i).mpr rfl).symm.trans ((S.valid _ j).mpr he))

def ordinal (n k : ℕ) (h : n ≤ k) : Selector (Fin n) (Fin k) where
  write := Fin.castLE h
  read c := if hc : c.val < n then some ⟨c.val, hc⟩ else none
  valid c i := by
    split
    · simp only [Option.some.injEq, Fin.ext_iff, Fin.val_castLE]
    · rename_i hc
      simp only [reduceCtorEq, false_iff]
      rintro rfl
      exact hc i.isLt

def relabel (S : Selector I C) (e : C ≃ D) : Selector I D where
  write i := e (S.write i)
  read d := S.read (e.symm d)
  valid d i := by rw [S.valid, e.symm_apply_eq]

/-- A branch can determine the next menu. -/
def bind {J : I → Type} (S : Selector I C) (T : ∀ i, Selector (J i) D) :
    Selector (Σ i, J i) (C × D) where
  write i := (S.write i.1, (T i.1).write i.2)
  read c := (S.read c.1).bind fun i => ((T i).read c.2).map (Sigma.mk i)
  valid c i := by
    rcases c with ⟨a, b⟩
    rcases i with ⟨i, j⟩
    constructor
    · intro h
      obtain ⟨x, hx, hy⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, he, hij⟩ := Option.map_eq_some_iff.mp hy
      cases hij
      exact Prod.ext ((S.valid _ _).mp hx) (((T i).valid _ _).mp he)
    · intro h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [(S.valid _ i).mpr rfl, Option.bind_some, ((T i).valid _ j).mpr rfl]
      rfl

/-- Independent local codes may have different lengths. -/
def family {A : Type} [Fintype A] {I C : A → Type} (S : ∀ a, Selector (I a) (C a)) :
    Selector (∀ a, I a) (∀ a, C a) where
  write i a := (S a).write (i a)
  read c := if h : ∀ a, ((S a).read (c a)).isSome
    then some (fun a => ((S a).read (c a)).get (h a)) else none
  valid c i := by
    constructor
    · split
      · rename_i h
        intro eq
        cases Option.some.inj eq
        funext a
        exact ((S a).valid _ _).mp (Option.some_get _).symm
      · simp
    · rintro rfl
      have h (a : A) : (S a).read ((S a).write (i a)) = some (i a) := ((S a).valid _ _).mpr rfl
      simp [h]

noncomputable section
open scoped Classical

theorem sum [Fintype C] [Fintype I] {F : Type} [AddCommMonoid F] (S : Selector I C)
    (f : I → F) : ∑ c, (S.read c).elim 0 f = ∑ i, f i := by
  have he (c : C) : (S.read c).elim 0 f = ∑ i, if c = S.write i then f i else 0 := by
    simp_rw [← S.valid]
    cases S.read c <;> simp
  simp_rw [he]
  rw [Finset.sum_comm]
  simp

end
end Selector
end OAI.LinearAlgebra.MatrixExponent.Transcript
