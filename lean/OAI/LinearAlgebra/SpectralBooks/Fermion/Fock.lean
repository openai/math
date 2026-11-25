import OAI.LinearAlgebra.SpectralBooks.Fermion.CARSign
import Mathlib.Data.Matrix.Basic

/-! # Finite fermion creation and annihilation matrices

The basis vectors are ordered subsets of the modes below a finite cutoff.
Inserting or erasing a mode has the sign of sorting it past the smaller occupied modes.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Finset
open scoped BigOperators

abbrev FockState (N : ℕ) := ↥((range N).powerset)

def FockState.erase {N : ℕ} (S : FockState N) (r : ℕ) : FockState N :=
  ⟨S.val.erase r, mem_powerset.mpr ((erase_subset _ _).trans (mem_powerset.mp S.property))⟩

def FockState.insert {N : ℕ} (S : FockState N) (r : Fin N) : FockState N :=
  ⟨Insert.insert r.val S.val, mem_powerset.mpr <|
    insert_subset (mem_range.mpr r.isLt) (mem_powerset.mp S.property)⟩

variable (K : Type*) [CommRing K] {N : ℕ}

/-- Exterior multiplication by the basis vector at mode `r`. -/
def creation (r : Fin N) : Matrix (FockState N) (FockState N) K := Matrix.of fun α β ↦
  if r.val ∈ α.val then if α.erase r = β then (wedgeSign r α.val : K) else 0 else 0

/-- Contraction against the basis vector at mode `r`. -/
def annihilation (r : Fin N) : Matrix (FockState N) (FockState N) K := (creation K r).transpose

theorem creation_apply (r : Fin N) (α β : FockState N) :
    creation K r α β =
      if r.val ∈ α.val then if α.erase r = β then (wedgeSign r α.val : K) else 0 else 0 := rfl

theorem annihilation_apply (r : Fin N) (α β : FockState N) :
    annihilation K r α β =
      if r.val ∈ α.val then 0 else if α.insert r = β then (wedgeSign r α.val : K) else 0 := by
  change creation K r β α = _
  rw [creation_apply]
  by_cases hβ : r.val ∈ β.val
  · by_cases h : β.erase r = α
    · subst α
      have he : (β.erase r).insert r = β := Subtype.ext (insert_erase hβ)
      simp [hβ, he, show (β.erase r).val = β.val.erase r.val from rfl, wedgeSign_erase _ hβ]
    · by_cases ha : r.val ∈ α.val
      · simp [hβ, h, ha]
      · have hi : α.insert r ≠ β := by
          intro he
          apply h
          apply Subtype.ext
          have he' := congrArg Subtype.val he
          change insert r.val α.val = β.val at he'
          change β.val.erase r.val = α.val
          rw [← he', erase_insert ha]
        simp [hβ, h, ha, hi]
  · have hi : α.insert r ≠ β := by
      intro he
      apply hβ
      rw [← he]
      exact mem_insert_self _ _
    simp [hβ, hi]

theorem creation_mul_apply (r : Fin N) (B : Matrix (FockState N) (FockState N) K)
    (α β : FockState N) :
    (creation K r * B) α β =
      if r.val ∈ α.val then (wedgeSign r α.val : K) * B (α.erase r) β else 0 := by
  classical
  by_cases h : r.val ∈ α.val <;> simp [Matrix.mul_apply, creation_apply, h, ite_mul]

theorem mul_annihilation_apply (r : Fin N) (B : Matrix (FockState N) (FockState N) K)
    (α β : FockState N) :
    (B * annihilation K r) α β =
      if r.val ∈ β.val then B α (β.erase r) * (wedgeSign r β.val : K) else 0 := by
  classical
  by_cases h : r.val ∈ β.val <;>
    simp [Matrix.mul_apply, annihilation, creation_apply, h, mul_ite]

theorem annihilation_mul_apply (r : Fin N) (B : Matrix (FockState N) (FockState N) K)
    (α β : FockState N) :
    (annihilation K r * B) α β =
      if r.val ∈ α.val then 0 else (wedgeSign r α.val : K) * B (α.insert r) β := by
  classical
  by_cases h : r.val ∈ α.val <;> simp [Matrix.mul_apply, annihilation_apply, h, ite_mul]

/-- Two creations anticommute, including the repeated-mode case. -/
theorem creation_mul_creation (i j : Fin N) :
    creation K i * creation K j + creation K j * creation K i = 0 := by
  ext α β
  change (creation K i * creation K j) α β + (creation K j * creation K i) α β = 0
  simp only [creation_mul_apply, creation_apply]
  have herase (r s : ℕ) : (α.erase r).erase s = (α.erase s).erase r :=
    Subtype.ext erase_right_comm
  have hval (r : ℕ) : (α.erase r).val = α.val.erase r := rfl
  by_cases hij : i.val = j.val
  · have h : i = j := Fin.ext hij
    subst j
    simp [hval]
  · have hji := Ne.symm hij
    by_cases hi : i.val ∈ α.val <;> by_cases hj : j.val ∈ α.val <;>
      simp [hi, hj, hval, hij, hji, herase i j]
    split
    · rw [wedgeSign_erase _ hi, wedgeSign_erase _ hj]
      rcases lt_or_gt_of_ne hij with h | h <;> simp [h, not_lt.mpr h.le] <;> ring
    · simp

/-- Two annihilations anticommute. -/
theorem annihilation_mul_annihilation (i j : Fin N) :
    annihilation K i * annihilation K j + annihilation K j * annihilation K i = 0 := by
  simpa only [annihilation, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_zero]
    using congrArg Matrix.transpose (creation_mul_creation K j i)


/-- Creating a mode and contracting a mode have anticommutator equal to the
identity for coincident modes and zero for distinct modes. -/
theorem annihilation_mul_creation (r s : Fin N) :
    annihilation K r * creation K s + creation K s * annihilation K r =
      if r = s then 1 else 0 := by
  classical
  ext α β
  rw [Matrix.add_apply, annihilation_mul_apply, creation_mul_apply]
  by_cases hrs : r = s
  · subst s
    rw [ite_eq_left (rfl : r = r), Matrix.one_apply]
    have hsq : (wedgeSign r α.val : K) * (wedgeSign r α.val : K) = 1 := by
      rw [← Int.cast_mul, wedgeSign_mul_self, Int.cast_one]
    by_cases h : r.val ∈ α.val
    · have he : (α.erase r).insert r = α := Subtype.ext (insert_erase h)
      simp [h, annihilation_apply, show (α.erase r).val = α.val.erase r.val from rfl,
        he, wedgeSign_erase _ h, mul_ite, hsq]
    · have he : (α.insert r).erase r = α := Subtype.ext (erase_insert h)
      simp [h, creation_apply, show (α.insert r).val = insert r.val α.val from rfl,
        he, wedgeSign_insert _ h, mul_ite, hsq]
  · have hn : r.val ≠ s.val := fun h ↦ hrs (Fin.ext h)
    have hins : (α.insert r).val = insert r.val α.val := rfl
    have hera : (α.erase s).val = α.val.erase s.val := rfl
    have hcomm : (α.insert r).erase s = (α.erase s).insert r := Subtype.ext (erase_insert_of_ne hn)
    rw [ite_eq_right hrs, Matrix.zero_apply]
    by_cases hr : r.val ∈ α.val <;> by_cases hs : s.val ∈ α.val <;>
      simp [hr, hs, creation_apply, annihilation_apply, hins, hera, hn, hn.symm, hcomm]
    by_cases hb : (α.erase s).insert r = β
    · rw [ite_eq_left hb, ite_eq_left hb, wedgeSign_insert _ hr, wedgeSign_erase _ hs]
      rcases lt_or_gt_of_ne hn with h | h
      · simp [h, not_lt_of_gt h, mul_comm]
      · simp [h, not_lt_of_gt h, mul_comm]
    · simp [hb]

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
